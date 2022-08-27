open Prog
open Regalloc
open Location



let b_print_graph         = ref false 
let b_debug               = ref false 
let b_graph_vis           = ref false
let b_stats               = ref false 
let b_count               = ref false 
let b_check_correctness   = ref false 
let b_optimize            = ref false 
let b_random_search       = ref false 
let b_fast_random_search  = ref true
let b_modify_result       = ref true 

let num_searches = 1000000
let output_format = "pdf"
let out_file = "test."^output_format
let dot_file = "test.dot"
let pipe_size = 5
let pos_list = []

(* --------------------------------------------------------------------------------*)
(* Numbered instruction *)

type ('len,'info,'asm) ninstr_r =
  | Nassgn of 'len glval * E.assgn_tag * 'len gty * 'len gexpr
  | Nopn   of 'len glvals * E.assgn_tag * 'asm Sopn.sopn * 'len gexprs
  | Nif    of 'len gexpr * ('len,'info,'asm) nstmt * ('len,'info,'asm) nstmt
  | Nfor   of 'len gvar_i * 'len grange * ('len,'info,'asm) nstmt
  | Nwhile of E.align * ('len,'info,'asm) nstmt * 'len gexpr * ('len,'info,'asm) nstmt
  | Ncall  of E.inline_info * 'len glvals * funname * 'len gexprs

and ('len,'info,'asm) ninstr = {
    n_desc : ('len,'info,'asm) ninstr_r;
    n_loc  : L.i_loc;
    n_info : 'info;
    n_annot : Syntax.annotations;
    n_pos : int;
    n_depth : int;
  }

and ('len,'info,'asm) nstmt = ('len,'info,'asm) ninstr array

(* --------------------------------------------------------------------------------*)
(* Conversion function *)

let rec ginstr_r_to_ninstr_r ?(depth=0) ginstr_r = match ginstr_r with
    | Cassgn (glval, assgn_tag, gty, gexpr) -> 
            Nassgn (glval, assgn_tag, gty, gexpr) 
    | Copn (glvals, assgn_tag, sopn, gexprs) -> 
            Nopn (glvals, assgn_tag, sopn, gexprs)
    | Cif (gexpr, gstmt1, gstmt2) -> 
            Nif (gexpr, gstmt_to_nstmt gstmt1 ~depth:(depth+1), gstmt_to_nstmt gstmt2 ~depth:(depth+1)) 
    | Cfor (gvar_i, grange, gstmt) -> 
            Nfor (gvar_i, grange, gstmt_to_nstmt gstmt ~depth:(depth+1))
    | Cwhile (align, gstmt1, gexpr, gstmt2) -> 
            let nstmt1 = gstmt_to_nstmt gstmt1 ~depth:(depth+1) in
            let nstmt2 = gstmt_to_nstmt gstmt2 ~depth:(depth+1) in
            Nwhile (align, nstmt1, gexpr, nstmt2)
    | Ccall (inline_info, glvals, funname, gexprs) -> 
            Ncall (inline_info, glvals, funname, gexprs)


and ginstr_to_ninstr ?(pos=ref 0) ?(depth=0) ginstr= 
    let curr_pos = !pos in 
    incr pos;
    {n_desc = ginstr_r_to_ninstr_r ~depth:(depth) ginstr.i_desc; 
     n_loc = ginstr.i_loc;  
     n_info = ginstr.i_info;
     n_annot = ginstr.i_annot;
     n_pos = curr_pos;
     n_depth = depth}

and gstmt_to_nstmt ?(pos=ref 0) ?(depth=0) gstmt = Array.of_list (List.map (fun x -> ginstr_to_ninstr ~pos:(pos) ~depth:(depth) x) gstmt)

(* --------------------------------------------------------------------------------*)
(* Utils function *)

let print_perm p = 
    (for i = 0 to Array.length p - 1 do
        Printf.printf "%d " p.(i);
    done;
    print_newline ();)


let is_perm_valid perm g =
    let n = Array.length g in 
    let seen = Array.make n 0 in
        let aux () = 
            if Array.length perm <> n then (Printf.printf "Expected length %d got %d\n" n (Array.length perm) ; failwith "incorrect length"); 
            for i = 0 to n-1 do
                if perm.(i) < 0 || perm.(i) > n-1 then failwith "not a permutation";
                if seen.(perm.(i)) = 1 then (print_int i; print_newline(); failwith "permutation with repetition");
                seen.(perm.(i)) <- 1;
                if List.exists (fun x -> seen.(x) = 0) g.(perm.(i)) then (print_int i; print_newline(); failwith "order not respected");
            done;
            true;
        in try aux () with e -> (print_perm perm; raise e)

let identity_perm n = 
    let arr = Array.init n (fun x -> x) in arr


(* --------------------------------------------------------------------------------*)
(* Utils functions *)

let var_mem = {pl_loc = L._dummy;
              pl_desc = Prog.V.mk "-mem" Inline tint L._dummy [];}

let var_mem = {pl_loc = L._dummy;
              pl_desc = Prog.V.mk "-mem" Inline tint L._dummy [];}

(* renvoie read, write*)
let rec get_rw_glval glval = match glval with
    | Lnone (_, _) -> 
            [], []
    | Lvar gvar_i -> 
            [], [gvar_i]
    | Lmem (_, gvar_i, gexpr) -> 
            let rl, wl = get_rw_gexpr gexpr in
                gvar_i::rl, var_mem::wl
    | Laset (_, _, gvar_i, gexpr) -> 
            let rl, wl = get_rw_gexpr gexpr in
                gvar_i::rl, var_mem::wl
    | Lasub (_, _, _, gvar_i, gexpr) ->  
            let rl, wl = get_rw_gexpr gexpr in
                gvar_i::rl, var_mem::wl

and get_rw_gexpr gexpr = match gexpr with
    | Pconst _ -> 
            [], []
    | Pbool _ -> 
            [], []
    | Parr_init _ ->
            [], []
    | Pvar ggvar ->
            [ggvar.gv], []
    | Pget (_, _, ggvar, gexpr) ->
            let rl, wl = get_rw_gexpr gexpr in
                ggvar.gv::rl, var_mem::wl 
    | Psub (_, _, _, ggvar, gexpr) -> 
            let rl, wl = get_rw_gexpr gexpr in
                ggvar.gv::rl, var_mem::wl 
    | Pload (_, gvar_i, gexpr) -> 
            let rl, wl = get_rw_gexpr gexpr in
                gvar_i::rl, var_mem::wl 
                (*FIXME : is it read or write?*)
    | Papp1 (_, gexpr) ->
            get_rw_gexpr gexpr
    | Papp2 (_, gexpr1, gexpr2) ->
            let rl1, wl1 = get_rw_gexpr gexpr1 in
            let rl2, wl2 = get_rw_gexpr gexpr2 in
                rl1@rl2, wl1@wl2
    | PappN (_, gexprs) ->
            get_rw_gexprs gexprs
    | Pif (_, gexpr1, gexpr2, gexpr3) ->
            let rl1, wl1 = get_rw_gexpr gexpr1 in
            let rl2, wl2 = get_rw_gexpr gexpr2 in
            let rl3, wl3 = get_rw_gexpr gexpr3 in
                rl1@rl2@rl3, wl1@wl2@wl3

and get_rw_glvals glvals = match glvals with
    | [] -> [], []
    | t::q -> let rl1, wl1 = get_rw_glval t in
              let rl2, wl2 = get_rw_glvals q in
                  rl1@rl2, wl1@wl2 

and get_rw_gexprs gexprs = match gexprs with
    | [] -> [], []
    | t::q -> let rl1, wl1 = get_rw_gexpr t in
              let rl2, wl2 = get_rw_gexprs q in
                  rl1@rl2, wl1@wl2 


and get_rw_ninstr ninstr = match ninstr.n_desc with
    | Nassgn (glval, _, _, gexpr) -> 
            let rl1, wl1 = get_rw_glval glval in
            let rl2, wl2 = get_rw_gexpr gexpr in
                rl1@rl2, wl1@wl2 
    | Nopn (glvals, _, _,  gexprs) ->
            let rl1, wl1 = get_rw_glvals glvals in
            let rl2, wl2 = get_rw_gexprs gexprs in
                rl1@rl2, wl1@wl2 
    | Nif (gexpr, nstmt1, nstmt2) ->
            let rl1, wl1 = get_rw_gexpr gexpr in
            let rl2, wl2 = get_rw_nstmt nstmt1 in
            let rl3, wl3 = get_rw_nstmt nstmt2 in
                rl1@rl2@rl3, wl1@wl2@wl3 
    | Nfor (_, _, _) ->
            failwith "ne devrait pas arriver :')"
    | Nwhile (_, nstmt1, gexpr, nstmt2) -> 
            let rl1, wl1 = get_rw_nstmt nstmt1 in
            let rl2, wl2 = get_rw_gexpr gexpr in
            let rl3, wl3 = get_rw_nstmt nstmt2 in
                rl1@rl2@rl3, wl1@wl2@wl3 
    | Ncall (_, glvals, _, gexprs) ->
            let rl1, wl1 = get_rw_glvals glvals in
            let rl2, wl2 = get_rw_gexprs gexprs in
                rl1@rl2, wl1@wl2 
 
and get_rw_nstmt nstmt = Array.fold_left (fun (rl1, wl1) ninstr -> let rl2, wl2 = get_rw_ninstr ninstr in (rl1@rl2, wl1@wl2)) ([], []) nstmt


let traiter_ninstr ninstr mem_write mem_read g = 
    let rl, wl = get_rw_ninstr ninstr in
        let aux1 wi = let w = wi.pl_desc in  
            if Hv.mem mem_write w && (Hv.find mem_write w <> ninstr.n_pos) then g.(ninstr.n_pos) <- (Hv.find mem_write w)::g.(ninstr.n_pos); 
            List.iter (fun x -> g.(ninstr.n_pos) <- x::g.(ninstr.n_pos)) (Hv.find_all mem_read w);
            Hv.replace mem_write w ninstr.n_pos; 
            Hv.remove mem_read w
        and aux2 ri = let r = ri.pl_desc in
            Hv.add mem_read r ninstr.n_pos;
            if Hv.mem mem_write r && (Hv.find mem_write r <> ninstr.n_pos) then g.(ninstr.n_pos) <- (Hv.find mem_write r)::g.(ninstr.n_pos) 
        in List.iter aux1 wl; List.iter aux2 rl

let traiter_nstmt nstmt = 
    let mem_write = Hv.create 100 in
    let mem_read = Hv.create 100 in
    let g = Array.make (Array.length nstmt) [] in
        Array.iter (fun x -> traiter_ninstr x mem_write mem_read g) nstmt; g

let enumerate_vertex_separators g f =
    let n = Array.length g in
    let rfree_nodes = ref [] in
    let rev_g = Array.make n [] in
    let rec add_rev i = function 
        | [] -> () 
        | t::q -> (rev_g.(t) <- i::rev_g.(t); add_rev i q) in
    for i = 0 to n-1 do
        add_rev i g.(i);
    done;
    for i = 0 to n-1 do
        if g.(i) = [] then rfree_nodes := i::!rfree_nodes;
    done;

    let buffer = ref [] in
        begin
        for i = 0 to n-1 do
            rfree_nodes := List.filter (fun x -> x <> i) !rfree_nodes;
            if !rfree_nodes = [] then buffer := i::!buffer;
            rfree_nodes := rev_g.(i) @ !rfree_nodes;
        done;
        f !buffer;
        end

let enumerate_all g f =
    let n = Array.length g in
    let rfree_nodes = ref [] in
    let num_dep = Array.make n 0 in
    let rev_g = Array.make n [] in
    let rec add_rev i = function 
        | [] -> () 
        | t::q -> (rev_g.(t) <- i::rev_g.(t); add_rev i q) in
    for i = 0 to n-1 do
        add_rev i g.(i);
        num_dep.(i) <- List.length g.(i);
        if num_dep.(i) = 0 then rfree_nodes := i::!rfree_nodes
    done;

    let rec update_childs childs rfree_nodes num_dep = match childs with
        | [] -> ()
        | child::q -> 
            (if num_dep.(child) = 1 then rfree_nodes := child::!rfree_nodes;
            num_dep.(child) <- num_dep.(child) - 1;
            update_childs q rfree_nodes num_dep) in

    let rec restore_childs childs num_dep = match childs with
        | [] -> ()
        | child::q -> 
            (num_dep.(child) <- num_dep.(child) + 1;
            restore_childs q num_dep) in

    let rec apply buffer num_dep rfree_nodes free_nodes f = match free_nodes with
        | [] -> if !rfree_nodes = [] then f buffer else ()
        | node::q -> let new_nodes = ref (List.filter (fun x -> x <> node) !rfree_nodes) in 
                     (update_childs rev_g.(node) new_nodes num_dep;
                     apply (node::buffer) num_dep new_nodes !new_nodes f;
                     restore_childs rev_g.(node) num_dep;
                     apply buffer num_dep rfree_nodes q f) in

    apply [] num_dep rfree_nodes !rfree_nodes f

let generate_random g f =
    let n = Array.length g in
    let rfree_nodes = ref [] in
    let num_dep = Array.make n 0 in
    let rev_g = Array.make n [] in
    let rec add_rev i = function 
        | [] -> () 
        | t::q -> (rev_g.(t) <- i::rev_g.(t); add_rev i q) in
    for i = 0 to n-1 do
        add_rev i g.(i);
        num_dep.(i) <- List.length g.(i);
        if num_dep.(i) = 0 then rfree_nodes := i::!rfree_nodes
    done;

    let rec update_childs childs rfree_nodes num_dep = match childs with
        | [] -> ()
        | child::q -> 
            (if num_dep.(child) = 1 then rfree_nodes := child::!rfree_nodes;
            num_dep.(child) <- num_dep.(child) - 1;
            update_childs q rfree_nodes num_dep) in

    let random_choice l = 
        let n = List.length l in
        let r = Random.int n in
        let rec get_r r l = match l with
            | [] -> failwith "nooo"
            | t::q -> if r = 0 then t else get_r (r-1) q
        in get_r r l in

    let rec apply buffer num_dep rfree_nodes f = match !rfree_nodes with
        | [] -> f buffer
        | _ ->  let node = random_choice !rfree_nodes in
                let new_nodes = ref (List.filter (fun x -> x <> node) !rfree_nodes) in 
                     (update_childs rev_g.(node) new_nodes num_dep;
                     apply (node::buffer) num_dep new_nodes f) in

    apply [] num_dep rfree_nodes f

let rec fast_random g perm = 
    let r = Random.int (Array.length g - 1) in
        begin
        if List.exists (fun x -> x = perm.(r)) g.(perm.(r+1)) then
            fast_random g perm
        else
            (let buffer = perm.(r) in
                (perm.(r) <- perm.(r+1);
                perm.(r+1) <- buffer);
                r)
        end

let score g perm = 
    let conf = Array.make pipe_size 0 in
    let found_col = ref false in
        begin    
        for i = 0 to Array.length g - 1 do
            found_col := false;
            for j = 0 to pipe_size - 1 do
                if not !found_col && i > j && List.exists (fun x -> x = perm.(i-1-j)) g.(perm.(i)) then (found_col := true; conf.(j) <- conf.(j) + 1);
            done
        done; 
        conf; 
        end

let local_fast_score g perm r = 
    let n = Array.length g in
    let res = ref 0 in
        begin
            for i = pipe_size downto 1 do
                if r < n && r - i >= 0 && List.exists (fun x -> x = perm.(r-i)) g.(perm.(r)) then res := (pipe_size - i + 1);  
            done;
            !res;
        end

(* r: indice de la transposition *)
let fast_score g perm r old_score =
    let s = ref 0 in
    let buffer = ref 0 in
        begin
            for i = r to r + 1 + pipe_size do
                s := !s + local_fast_score g perm i;
            done;
            buffer := perm.(r);
            perm.(r) <- perm.(r+1);
            perm.(r+1) <- !buffer;
            for i = r to r + 1 + pipe_size do
                s := !s - local_fast_score g perm i;
            done;
            buffer := perm.(r);
            perm.(r) <- perm.(r+1);
            perm.(r+1) <- !buffer;
            !s + old_score;
        end


let rec get_nstmt pos nstmt = match pos with
    | [] -> nstmt
    | (i, j)::q -> 
            if i < 0 || i >= Array.length nstmt then failwith "wrong positionnal arg"
            else begin
                match (j, nstmt.(i).n_desc) with
                    | (0, Nif (_, nstmt, _))       -> get_nstmt q nstmt 
                    | (1, Nif (_, _, nstmt))       -> get_nstmt q nstmt 
                    | (0, Nwhile (_, nstmt, _, _)) -> get_nstmt q nstmt
                    | (1, Nwhile (_, _, _, nstmt)) -> get_nstmt q nstmt
                    | _ -> failwith "no subgraph in instruction"
            end

(* --------------------------------------------------------------------------------*)
(* Kinda pretty printing *)


let rec padding_to_string depth = if depth<1 then "" else "\t"^(padding_to_string (depth-1))

let rec string_of_ninstr ninstr =
Printf.sprintf "%s%d: %s\n" 
        (padding_to_string ninstr.n_depth)
        ninstr.n_pos 
        (string_of_ninstr_r ninstr.n_desc) 

and string_of_nstmt nstmt = Array.fold_left (fun s ninstr -> s^(string_of_ninstr ninstr)) "" nstmt 

and string_of_row g i = Printf.sprintf "%d -> {%s} [color=%s]" i (List.fold_left (fun s x -> s^" "^(string_of_int x)) "" g.(i)) (if List.exists (fun x -> x = i-1) g.(i) then "red" else "green")

and string_of_graphe g = 
let acc = ref "digraph{" in
    for i = 0 to Array.length g - 1 do
        acc := !acc^"\n"^(string_of_row g i)
    done;
    !acc^"}"

and print_stats g perm = 
let s = ref 0 in
let conf = score g perm in 
    begin    
        Printf.printf "Total: %d\n\n" (Array.length g);
        for i = 0 to Array.length conf - 1 do
            Printf.printf "Conf[%d] = %d\n" i conf.(i);
            s := !s + (pipe_size - i) * conf.(i);
        done;
        Printf.printf "Score: %d\n" !s;
    end

and string_of_ninstr_r = function
    | Nassgn (glval, _, _, gexpr) -> 
            Printf.sprintf "%s = %s" (string_of_glval glval) (string_of_gexpr gexpr)
    | Nopn (glvals, _, _, gexprs) -> 
            Printf.sprintf "%s = OPN(%s)" 
                (List.fold_left (fun s glval -> s^" "^(string_of_glval glval)) "" glvals) 
                (List.fold_left (fun s gexpr -> s^" "^(string_of_gexpr gexpr)) "" gexprs)
    | Nwhile (_, nstmt1, gexpr, nstmt2) -> 
            Printf.sprintf "while {\n%s} (%s) {\n%s}" (string_of_nstmt nstmt1) (string_of_gexpr gexpr) (string_of_nstmt nstmt2)
    | Nif (gexpr, nstmt1, nstmt2) ->
            Printf.sprintf "if (%s) then {\n%s\n} else {\n%s}" (string_of_gexpr gexpr) (string_of_nstmt nstmt1) (string_of_nstmt nstmt2)
    | Nfor (_, _, _) -> 
            failwith "CFOR"
    | Ncall (_, glvals, funname, gexprs) -> 
            Printf.sprintf "%s = %s(%s)" 
                (List.fold_left (fun s glval -> s^" "^(string_of_glval glval)) "" glvals) 
                funname.fn_name
                (List.fold_left (fun s gexpr -> s^" "^(string_of_gexpr gexpr)) "" gexprs)

and string_of_gvars = function
    | [] -> ""
    | gvar::q -> gvar.v_name^" "^(string_of_gvars q)

and string_of_func f =
    (Printf.sprintf "\nfn %s:\n" f.f_name.fn_name)^
    (Printf.sprintf "Args: %s\n" (string_of_gvars f.f_args))^
    (Printf.sprintf "Body: \n%s" (string_of_nstmt (gstmt_to_nstmt f.f_body)))

and string_of_funcs = function
    | [] -> ""
    | f::q -> (string_of_func f)^(string_of_funcs q)

and string_of_gvar_i gvar_i = Printf.sprintf "%s.%d" gvar_i.pl_desc.v_name (int_of_uid gvar_i.pl_desc.v_id) 

and string_of_glval = function 
    | Lnone (_, _) -> 
            "_"
    | Lvar (gvar_i) -> 
            Printf.sprintf "%s" (string_of_gvar_i gvar_i)
    | Lmem (_, gvar_i, gexpr) -> 
            Printf.sprintf "[%s + %s]" (string_of_gvar_i gvar_i) (string_of_gexpr gexpr)
    | Laset (_, _, gvar_i, gexpr) -> 
            Printf.sprintf "%s[%s]" (string_of_gvar_i gvar_i) (string_of_gexpr gexpr)
    | Lasub (_, _, len, gvar_i, gexpr) -> 
            Printf.sprintf "%s[%s:%d]" (string_of_gvar_i gvar_i) (string_of_gexpr gexpr) len

and string_of_gexpr = function
    | Pconst t -> 
            Printf.sprintf "%s" (Z.to_string t)
    | Pbool  b -> 
            if b then "true" else "false"
    | Parr_init _ -> 
            "ARRAY INIT"
    | Pvar ggvar -> 
            (string_of_gvar_i ggvar.gv)
    | Pget (_, _, ggvar, gexpr) -> 
            Printf.sprintf "%s[%s]" (string_of_gvar_i ggvar.gv) (string_of_gexpr gexpr) 
    | Psub (_, _, len, ggvar, gexpr) -> 
            Printf.sprintf "%s[%s:%d]" (string_of_gvar_i ggvar.gv) (string_of_gexpr gexpr) len
    | Pload (_, gvar_i, gexpr) -> 
            Printf.sprintf "[%s + %s]" (string_of_gvar_i gvar_i) (string_of_gexpr gexpr)
    | Papp1 (_, gexpr) -> 
            Printf.sprintf "OP1(%s)" (string_of_gexpr gexpr)
    | Papp2 (_, gexpr1, gexpr2) -> 
            Printf.sprintf "OP2(%s, %s)" (string_of_gexpr gexpr1) (string_of_gexpr gexpr2)
    | PappN (_, gexpr_list) -> 
            Printf.sprintf "OP%d(%s)" (List.length gexpr_list) (List.fold_left (fun s gexpr -> s^" "^(string_of_gexpr gexpr)) "" gexpr_list)
    | Pif (_, gexpr1, gexpr2, gexpr3) -> 
            Printf.sprintf "if %s then %s else %s" (string_of_gexpr gexpr1) (string_of_gexpr gexpr2) (string_of_gexpr gexpr3)



let traite (cp: 'asm_op Expr._uprog) p = match p with _, f -> 
    let curr_nstmt = get_nstmt pos_list (gstmt_to_nstmt (List.hd f).f_body) in
    let g = traiter_nstmt curr_nstmt in
    let n = Array.length g in
    let final_perm = ref (identity_perm n) in

    if !b_debug then begin
        print_string (string_of_funcs f)
    end;

    if !b_print_graph then begin
        let str = string_of_graphe g in   
            Printf.printf "%s\n" str;    
    end;

    if !b_graph_vis then begin
        let oc = open_out dot_file in 
        let str = string_of_graphe g in   
            Printf.fprintf oc "%s" str;
            close_out oc;
            Printf.printf "Saved graph to file %s\n" dot_file;
            let _ = Sys.command ("dot test.dot -T"^output_format^" > "^out_file) in ();
            Printf.printf "Converted graph to %s\n" out_file;
    end;

    if !b_stats then begin
        print_stats g (identity_perm (Array.length g));
    end;

    if !b_count then begin
        let total = ref 0 in
        let count _ =
            begin 
            incr total;
            if !total mod 1000000 = 0 then Printf.printf "%d million permutations found!\n%!" (!total/1000000);
            end in
        enumerate_all g count;
        Printf.printf "Found %d permutations in total\n" !total;
    end;

    if !b_check_correctness then begin
            let correct = ref 0 and total = ref 0 in
            let test perm_l =
                let perm = Array.of_list (List.rev perm_l) in
                begin 
                Array.iter (fun e -> print_int e; print_string " ") perm;
                print_newline();
                if is_perm_valid perm g then (incr correct);
                incr total;
                end in 
            enumerate_all g (fun x -> test x);
            Printf.printf "Found %d permutations: %d are correct\n" !total !correct;
    end;

    if !b_optimize then begin
        let best_score = ref 1000000 in

        let test perm_l = 
            let perm = Array.of_list (List.rev perm_l) in
            let conf = score g perm in
            let score = ref 0 in
                for i = 0 to pipe_size - 1 do
                    score := !score + (pipe_size - i) * conf.(i);
                done;
                if !score < !best_score then begin
                    Printf.printf "Best score : %d  " !score;
                    print_perm perm;
                    final_perm := perm;
                    best_score := !score;
                end in
        enumerate_all g (fun x -> test x);
    end;

    if !Glob_options.optim && !b_random_search then begin
        Random.self_init ();
        Printf.printf "\n\n#####Starting random search#####\n";
        let best_score = ref 1000000 in
        let test perm_l = 
            let perm = Array.of_list (List.rev perm_l) in
            let conf = score g perm in
            let score = ref 0 in
                for i = 0 to pipe_size - 1 do
                    score := !score + (pipe_size - i) * conf.(i);
                done;
                if !score < !best_score then begin
                    Printf.printf "Best score : %d  " !score;
                    final_perm := perm;
                    (*print_perm perm; TODO*)
                    best_score := !score;
                end in

        for _ = 0 to num_searches do
            generate_random g test;
        done;
        Printf.printf "%d" !best_score;
    end;

    if !Glob_options.optim && !b_fast_random_search then begin
        Random.self_init ();
        Printf.printf "\n\n#####Starting fast random search#####\n";
        let best_score = ref 1000000 in
        let old_score = ref 0 in
        let p = ref 0 in
        let test perm = 
            begin
            old_score := fast_score g perm !p !old_score;
            if !old_score < !best_score then begin
                Printf.printf "Best score : %d\n" !old_score;
                final_perm := perm;
                (*print_perm perm;*)
                best_score := !old_score;
            end;
            end;
            in

        let start_perm = ref (Array.make n 0) in
            generate_random g (fun x -> start_perm := Array.of_list (List.rev x));
            let conf = score g !start_perm in
                begin
                for i = 0 to pipe_size - 1 do
                    old_score := !old_score + (pipe_size - i) * conf.(i);
                done;
                if Array.length g > 0 then 
                    (for _ = 0 to num_searches do
                        p := fast_random g !start_perm;
                        test !start_perm;
                    done;)
                else
                    Printf.printf "Selected empty statement to optimize\n";
                end;
        Printf.printf "%d" !best_score;
    end;


    let rec modify_body body pos = 
        let instr_arr = Array.of_list body in
        let new_arr = Array.copy instr_arr in
            match pos with
                | [] ->
                    begin
                    for i = 0 to n-1 do
                        new_arr.(i) <- instr_arr.(!final_perm.(i));
                    done;
                    Array.to_list new_arr;
                    end
                | (i,j)::q ->
                    begin
                    if i < 0 || i >= Array.length new_arr then failwith "wrong positionnal arg"
                    else begin
                        match (j, new_arr.(i)) with
                            | (0, Expr.MkI(info, Cif (e, gstmt, g)))  -> new_arr.(i) <- MkI(info, (Cif (e, modify_body gstmt q, g)))
                            | (1, MkI(info, Cif (e, g, gstmt)))       -> new_arr.(i) <- MkI(info, (Cif (e, g, modify_body gstmt q)))
                            | (0, MkI(info, Cwhile (a, gstmt, e, g))) -> new_arr.(i) <- MkI(info, (Cwhile (a, modify_body gstmt q, e, g)))
                            | (1, MkI(info, Cwhile (a, g, e, gstmt))) -> new_arr.(i) <- MkI(info, (Cwhile (a, g, e, modify_body gstmt q)))
                            | _ -> failwith "no subgraph in instruction"
                    end;
                    Array.to_list new_arr;
                    end;
                    in


    let modify_func (fun_name, fun_def) =
        let new_fun_def = {Expr.f_info = fun_def.Expr.f_info;
                          f_tyin = fun_def.f_tyin;
                          f_params = fun_def.f_params;
                          f_body= modify_body fun_def.f_body pos_list;
                          f_tyout = fun_def.f_tyout;
                          f_res = fun_def.f_res;
                          f_extra = fun_def.f_extra} in     
        (fun_name, new_fun_def) in

    let p_funs = (modify_func (List.hd cp.p_funcs))::(List.tl cp.p_funcs) in
    
    if !b_modify_result then
        {Expr.p_funcs = p_funs; p_globs = cp.p_globs; p_extra = cp.p_extra}
    else
        cp;

