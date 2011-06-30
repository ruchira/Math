(*
Module minpoly.ml

Module for approximate polynomial minimization using semidefinite programming.

Author: Ruchira S. Datta
Copyright 2001 by Ruchira S. Datta
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation fies (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM< DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM<
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*)

let partitions_with_num_parts d m i =
  if d < 0 then [] else 
    if d = 0 then ( if m = 0 then [ ( i, [] ) ] else [] ) else
      if m <= 0 || m > d then [] else
        if m = 1 then [ ( i, [ ( d, 1 ) ] ) ] else
          if m = d then [ ( i, [ ( 1, m ) ] ) ] else
            let rec aux cum cur_part =
              match cur_part with
              | ( p, ( largest, l ) :: ( next, n ) :: rest ) ->
                if largest - next = 1 then begin
                  match rest with
                  | [] -> cur_part :: cum
                  | ( nextnext, j ) :: restrest ->
                    (* l * largest + n * next + j * nextnext =
                      newlargest + (l + n) * (nextnext + 1) + (j - 1) * nextnext 
                     *)
                    let newlargest = 
                      l * ( largest - nextnext - 1 ) 
                        + n * ( next - nextnext - 1 ) + nextnext
                    in
                    let newrest = 
                      if j = 1 then restrest else begin
                        ( nextnext, j - 1 ) :: restrest
                      end
                    in
                    let newseq = 
                      if newlargest = nextnext + 1 then begin
                        ( newlargest, l + n + 1 ) :: newrest
                      end else begin
                        ( newlargest, 1 ) :: ( nextnext + 1, l + n ) :: newrest
                      end
                    in
                      aux ( cur_part :: cum ) ( p + 1, newseq )
                end else begin
                  (* l * largest + n * next 
                    = newlargest + l * ( next + 1 ) + ( n - 1 ) * next *)
                  let newlargest = l * ( largest - next - 1 ) + next in
                  let newrest = if n = 1 then rest else ( next, n - 1 ) :: rest in
                  let newseq = 
                    if newlargest = next + 1 then
                      ( newlargest, l + 1 ) :: newrest
                    else
                      ( newlargest, 1 ) :: ( next + 1, l ) :: newrest 
                  in 
                    aux ( cur_part :: cum ) ( p + 1, newseq )
                end
              | _ -> cur_part :: cum
            in aux [] ( i, [ ( d - m + 1, 1 ); ( 1, m - 1 ) ] )

let partitions_with_at_most_num_parts d maxparts =
  if d < 0 then [] else
    if d = 0 then begin
      if maxparts < 0 then [] else
        [ ( 0, partitions_with_num_parts 0 0 1 ) ] 
    end else
      let rec aux cum m =
        if m > maxparts then cum else
          let i =
            match cum with
            | ( _, ( j, _ ) :: _ ) :: _ -> j + 1
            | _ -> 1
          in
          let parts = partitions_with_num_parts d m i in
          aux ( ( m, parts ) :: cum ) ( m + 1 )
      in aux [] 1

let partitions d = partitions_with_at_most_num_parts d d

let combinations n k =
  if k < 0 || k > n then [] else
    let combo = Array.init k ( fun i -> i + 1 ) in
    let incr () =
      if combo.( k - 1 ) < n then begin
        combo.( k - 1 ) <- combo.( k - 1 ) + 1 ; true
      end else if k = 1 then false else
        let rec find_hole i =
          if combo.( i + 1 ) - combo.( i ) = 1 then begin
            if i = 0 then None else find_hole ( i - 1 )
          end else Some i
        in
        match find_hole ( k - 2 ) with
        | None -> false
        | Some i ->
            let rec move_hole j x =
              combo.( j ) <- x;
              if j < k - 1 then move_hole ( j + 1 ) ( x + 1 ) else ()
            in ( move_hole i ( combo.( i ) + 1 ); true )
    in
    let rec enum cum =
      let newcum = Array.copy combo :: cum in
      if incr () then enum newcum else newcum
    in List.rev ( enum [] )

let subsets_with_sizes n szs =
  if szs = [] then [ [|[||]|] ] else
    let ks = Array.of_list szs in
    let numks = Array.length ks in
    let combos = Array.create numks ( Array.of_list ( combinations 1 1 ) ) 
    in
    let eltsleft = Array.create numks n in
    let _ =
      for i = 0 to numks - 1 do
        combos.( i ) <-
          ( let lst = combinations eltsleft.( i ) ks.( i ) in
            Array.of_list lst );
          if i < numks - 1 then 
            eltsleft.( i + 1 ) <- eltsleft.( i ) - ks.( i )
      done
    in
    let js = Array.create numks 0 in
    let incrjs () =
      let rec aux i =
        if js.( i ) < Array.length combos.( i ) - 1 then begin
          js.( i ) <- js.( i ) + 1;
          true
        end else begin
          js.( i ) <- 0;
          if i = 0 then false else aux ( i - 1 )
        end
      in aux ( numks - 1 );
    in
    let numsleft = Array.init n (fun l -> l + 1) in
    let rec enum cum =
      let subsets = Array.init numks ( fun i -> Array.create ks.( i ) 0 ) in
      let _ = for l = 0 to n - 1 do numsleft.( l ) <- l + 1 done in
      let _ =
        for i = 0 to numks - 1 do
          let combo = combos.( i ).( js.( i ) ) in
          let rec loop j k l =
            if j = eltsleft.( i ) then () else
              if k < ks.( i ) && j + 1 = combo.( k ) then begin
                subsets.( i ).( k ) <- numsleft.( j );
                loop ( j + 1 ) ( k + 1 ) l
              end else begin
                numsleft.( l ) <- numsleft.( j );
                loop ( j + 1 ) k ( l + 1 )
              end
          in loop 0 0 0
        done
      in 
      match incrjs () with
      | false -> subsets :: cum
      | true -> enum ( subsets :: cum )
    in enum []

let unziplt lst =
  let f xs (a, b) = a :: xs in
  List.fold_left f [] lst

let unziprt lst =
  let f xs (a, b) = b :: xs in
  List.fold_left f [] lst

let unzip lst =
  let f ( xs, ys ) ( a, b ) = ( a :: xs, b :: ys ) in
  List.fold_left f ( [], [] ) lst

let just_partitions_with_at_most_num_parts d m =
  let partitions_with_info = partitions_with_at_most_num_parts d m in
  List.concat ( List.map unziprt ( unziprt partitions_with_info ) )

let monomial_of_degrees_subsets n degrees subsets =
  let mon = Array.make n 0 in
  let rec loop i j = function
  | [] -> ()
  | ( deg :: rest ) as degs ->
    if j = Array.length subsets.( i ) then
      loop ( i + 1 ) 0 rest
    else
      let _ = mon.( subsets.( i ).( j ) - 1 ) <- deg in
      loop i ( j + 1 ) degs
  in 
  let _ = loop 0 0 degrees in
  mon

let monomials n d =
  if d < 0 then [] else
    if d = 0 then [ Array.make n 0 ] else
      let parts = just_partitions_with_at_most_num_parts d n in
      let rec loop cum degs ps cursubs =
        match cursubs with
        | sub :: subs ->
          let mon = monomial_of_degrees_subsets n degs sub in
          loop ( mon :: cum ) degs ps subs
        | [] ->
          match ps with
          | [] -> cum
          | p :: rest ->
            let newdegs, szs = unzip p in
            loop cum newdegs rest ( subsets_with_sizes n szs )
      in loop [] [] parts []

let monomials_up_to_deg n d =
  let rec loop cum degs ps cursubs nextd =
    match cursubs with
    | sub :: subs ->
      let mon = monomial_of_degrees_subsets n degs sub in
      loop ( mon :: cum ) degs ps subs nextd
    | [] ->
      match ps with
      | [] -> 
        if nextd < 0 then cum else 
          let newps = just_partitions_with_at_most_num_parts nextd n in
          loop cum degs newps [] ( nextd - 1 )
      | p :: rest ->
        let newdegs, szs = unzip p in
        loop cum newdegs rest ( subsets_with_sizes n szs ) nextd
  in loop [] [] [] [] d

let monomial_prod monom1 monom2 =
  let n = Array.length monom1 in
  if n != Array.length monom2 then
    failwith "monomial_prod: different numbers of variables"
  else
    Array.init n ( fun i -> monom1.( i ) + monom2.( i ) )

let rec string_of_monom varnames monom =
  let n = Array.length monom in
  if n != Array.length varnames then
    failwith "string_of_monom: different numbers of variables"
  else
    let string_of_power i =
      let s = monom.( i ) in
      if s = 0 then "" else
        if s = 1 then varnames.( i ) else 
          Format.sprintf "%s^%d" varnames.( i ) s
    in
    let rec loop str i =
      if i = n then str else
        let next_str = string_of_power i in
        if str = "" || next_str = "" then
          loop ( str ^ next_str ) ( i + 1 )
        else
          loop ( str ^ "*" ^ next_str ) ( i + 1 )
    in 
    let res = loop "" 0 in
    if res = "" then "1" else res

let monomial_products n d =
  let monoms = monomials_up_to_deg n ( 2 * d ) in
  let divisors = monomials_up_to_deg n d in
  let numds = List.length divisors in
  let tbl = Hashtbl.create ( List.length monoms ) in
  let rec init = function
  | [] -> ()
  | monom :: rest -> Hashtbl.add tbl monom []; init rest
  in 
  let _ = init monoms in
  let rec loop fstdivs snddivs i j =
    match fstdivs with
    | [] -> () 
    | m1 :: m1s ->
      match snddivs with
      | [] -> loop m1s m1s ( i + 1 ) ( i + 1 )
      | m2 :: m2s ->
        let m = monomial_prod m1 m2 in
        let prs = Hashtbl.find tbl m in
        Hashtbl.replace tbl m ( ( ( i, m1 ), ( j, m2 ) ) :: prs ); 
        loop fstdivs m2s i ( j + 1 )
  in
  let _ = loop divisors divisors 1 1 in
  let rec sort cum i = function
  | [] -> cum
  | m :: ms -> sort ( ( i, m, Hashtbl.find tbl m ) :: cum ) ( i + 1 ) ms
  in ( List.length monoms, List.length divisors, List.rev ( sort [] 1 monoms ) )

let string_of_monom_prod_exps varnames d =
  let n = Array.length varnames in 
  let str_m m =
    let str = string_of_monom varnames m in
    if str = "" then "1" else str
  in
  let f2 str ( ( i1, m1 ), ( i2, m2 ) ) = 
    let str1 = Format.sprintf "= (%d) %s " i1 ( str_m m1 ) in
    let str2 = Format.sprintf "* (%d) %s " i2 ( str_m m2 ) in
    str ^ str1 ^ str2
  in
  let f1 ( i, m, prs ) =
    let startstr = Printf.sprintf "(%d) %s " i ( str_m m ) 
    in List.fold_left f2 startstr prs
  in 
  let _, _, prod_exps = monomial_products n d in 
  List.map f1 prod_exps

let pr_monom_prod_exps env d ch = 
  List.iter ( Printf.fprintf ch "%s\n" ) ( string_of_monom_prod_exps env d )

let rep_in_monomial_basis n d poly =
  let monoms = monomials_up_to_deg n d in
  let tbl = Hashtbl.create ( List.length monoms ) in
  let rec init = function
  | [] -> ()
  | monom :: rest -> Hashtbl.add tbl monom 0.0; init rest
  in 
  let _ = init monoms in
  let rec loop = function
  | [] -> ()
  | ( coeff, monom ) :: terms ->
      let oldcoeff = Hashtbl.find tbl monom in
      Hashtbl.replace tbl monom ( coeff +. oldcoeff ); loop terms
  in
  let _ = loop poly in
  let rec sort cum = function
  | [] -> cum
  | m :: ms -> sort ( Hashtbl.find tbl m :: cum ) ms
  in List.rev ( sort [] monoms )

let gram = Grammar.create (Plexer.make ())
let varpower = Grammar.Entry.create gram "varpower"
EXTEND
  varpower:
    [ [ x = LIDENT; "^"; n = INT -> ( x, int_of_string n ) 
      | x = LIDENT -> ( x, 1 ) ] ]
  ;
END;;
let monomial = Grammar.Entry.create gram "monomial"
EXTEND
  monomial:
    [ [ m1 = monomial; "*"; m2 = monomial -> m1 @ m2  
      | m = varpower -> [ m ] ] ]
  ;
END;;
let coeff = Grammar.Entry.create gram "coeff"
EXTEND
  coeff:
    [ [ c = FLOAT -> float_of_string c
      | c = INT -> float_of_string c ] ]
  ;
END
let term = Grammar.Entry.create gram "term"
EXTEND
  term:
    [ [ t = term; "/"; d = coeff -> let ( c, m ) = t in ( c /. d, m )
      | c = coeff; "*"; m = monomial -> ( c, m )
      | c = coeff -> ( c, [] )
      | m = monomial -> ( 1.0, m ) 
      | "("; t = term; ")" -> t ] ]
  ;
END
let polynomial = Grammar.Entry.create gram "polynomial"
EXTEND
  polynomial:
    [ [ p1 = polynomial; "+"; p2 = polynomial -> p1 @ p2
      | p1 = polynomial; "-"; ( c, m ) = term -> p1 @ [ ( ~-. c, m ) ]
      | t = term -> [ t ] ] ]
  ;
END

let unname varnames ( coeff, varpowers ) =
  let n = Array.length varnames in
  let monom = Array.make n 0 in
  let rec subst i ( varname, pow ) =
    if i = n then
      failwith ( "unname: unknown variable name " ^ varname )
    else
      if varnames.( i ) = varname then
        monom.( i ) <- monom.( i ) + pow
      else subst ( i + 1 ) ( varname, pow )
  in
  let _ = List.map ( subst 0 ) varpowers in
  ( coeff, monom )

let polynomial_of_stream vars strm =
  List.map ( unname vars ) ( Grammar.Entry.parse polynomial strm )

let total_degree poly =
  let total_degree_of_term ( c, m ) =
    Array.fold_left ( + ) 0 m
  in
  List.fold_left max 0 ( List.map total_degree_of_term poly )

let isone monom =
  let n = Array.length monom in
  let rec aux i =
    if i = n then
      true
    else if monom.( i ) = 0 then
      aux ( i + 1 )
    else 
      false
  in aux 0

let poly_prods n poly divs =
  let deg = total_degree poly in
  let d = if deg mod 2 = 0 then deg / 2 else deg / 2 + 1 in
  let prods = Hashtbl.create ( List.length poly ) in
  let rec init = function
  | [] -> ()
  | ( c, monom ) :: rest -> Hashtbl.add prods monom ( c, [] ); init rest
  in 
  let _ = init poly in
  let rec sort tbl f cum i = function
  | [] -> cum
  | m :: ms ->
    if Hashtbl.mem tbl m then begin
      let v = f tbl m i in
      sort tbl f ( v :: cum ) ( i + 1 ) ms
    end else
      sort tbl f cum i ms
  in
  let fd tbl m i = ( i, m ) in
  let one = Array.make n 0 in
  let rec loop cum i = function
  | [] -> cum
  | m :: ms -> 
    if isone m then
      loop cum i ms
    else
      loop ( ( i, m ) :: cum ) ( i + 1 ) ms
  in
  let div_list = loop [ ( 1, one ) ] 2 divs in
  let rec loop2 fstdivs snddivs =
    match fstdivs with
    | [] -> ()
    | ( i1, m1 ) :: m1s ->
      match snddivs with
      | [] -> loop2 m1s m1s
      | ( i2, m2 ) :: m2s ->
        let m = monomial_prod m1 m2 in
        if Hashtbl.mem prods m then begin
          let c, exps = Hashtbl.find prods m in
          Hashtbl.replace prods m ( c, ( ( i1, m1 ), ( i2, m2 ) ) :: exps );
        end else begin
          Hashtbl.add prods m ( 0.0, [ ( ( i1, m1 ), ( i2, m2 ) ) ] );
        end;
        loop2 fstdivs m2s
  in
  let _ = loop2 div_list div_list in
  let fp tbl m i = ( i, m, Hashtbl.find tbl m ) in
  let prod_list = sort prods fp [] 1 ( monomials_up_to_deg n deg ) in
  ( List.rev div_list, List.rev prod_list )

let pr_interp ch vars ( ds, ps ) =
  let _ = Printf.fprintf ch "There are %d possible monomial divisors:\n" 
    ( List.length ds ) in
  let string_of_div ( i, m ) 
    = Printf.sprintf "(%d) %s" i ( string_of_monom vars m ) in
  let _ = List.iter ( Printf.fprintf ch "%s\n" ) ( List.map string_of_div ds ) 
  in
  let _ = Printf.fprintf ch "There are %d possible monomial products:\n"
    ( List.length ps ) in
  let f2 ( ( i1, m1 ), ( i2, m2 ) ) = 
    Printf.fprintf ch "= (%d) %s * (%d) %s" 
      i1 ( string_of_monom vars m1 )
      i2 ( string_of_monom vars m2 )
  in
  let f1 ( i, m, ( c, exps ) ) =
    Printf.fprintf ch "%g of (%d) " c i;
    Printf.fprintf ch "%s" ( string_of_monom vars m );
    List.iter f2 exps;
    Printf.fprintf ch "\n"
  in List.iter f1 ps

let pr_sdpa ch ( ds, ps ) =
  Printf.fprintf ch "%d\n1\n%d\n" ( List.length ps ) ( List.length ds );
  let pr_coeff ( i, m, ( c, exps ) ) = Printf.fprintf ch "%.15g " c in
  List.iter pr_coeff ps;
  Printf.fprintf ch "\n0 1 1 1 0.0\n";
  let rec outer = function
  | [] -> ()
  | ( i, m, ( c, exps ) ) :: moreprods ->
    let rec inner = function
    | [] -> ()
    | ( ( i1, _ ), ( i2, _ ) ) :: moreexps ->
      Printf.fprintf ch "%d 1 %d %d 1.0\n" i i1 i2;
      inner moreexps
    in inner exps; outer moreprods
  in outer ps

let blocks ( ds, ps ) =
  let n = List.length ds in
  let graph = Array.make ( n + 1 ) [] in
  let component_of = Array.make ( n + 1 ) 0 in
  let f ( ( i, _ ), ( j, _ ) ) =
    let inbrs = graph.( i ) in
    let jnbrs = graph.( j ) in
    graph.( i ) <- j :: inbrs; graph.( j ) <- i :: inbrs
  in
  let iterf ( _, _, ( _, prs ) ) = List.iter f prs in
  let _ = List.iter iterf ps in
  let rec do_vertices component i =
    if i > n then component else
      if component_of.( i ) = 0 then begin
        let new_component = component + 1 in
        component_of.( i ) <- new_component;
        let rec dfs j =
          component_of.( j ) <- new_component;
          let jnbrs = graph.( j ) in
          List.iter ( fun k -> if component_of.( k ) = 0 then dfs k ) jnbrs
        in dfs i;
        do_vertices new_component ( i + 1 )
      end else do_vertices component ( i + 1 )
  in
  let num_components = do_vertices 0 1 in
  let components = Array.make ( num_components + 1 ) [] in
  for i = 1 to n do
    let s = component_of.( i ) in
    let js = components.( s ) in
    components.( s ) <- i :: js
  done;
  for s = 1 to num_components do
    components.( s ) <- List.sort compare ( components.( s ) )
  done;
  ( num_components, components )

let homogenize poly n =
  let total_degree_with_term ( c, m ) =
    let f sum ( var, pow ) = sum + pow in
    ( List.fold_left f 0 m, ( c, m ) )
  in
  let poly_with_degs = List.map total_degree_with_term poly in
  let d = List.fold_left max 0 ( unziplt poly_with_degs ) in
  let f ( deg, ( c, m ) ) = 
    if deg = d then ( c, m ) else ( c, m @ [ ( n + 1, d - deg ) ] )
  in
  List.map f poly_with_degs

let pr_f0_for_min ch ( ds, ps ) =
  let pr_entry ( _, _, ( c, prs ) ) =
    match prs with
    | [] -> ()
    | ( ( i1, _ ), ( i2, _ ) ) :: _ ->
      let c0 = if i1 = i2 then ~-. c else ~-. c /. 2. in
      Printf.fprintf ch "0 1 %d %d %.15f\n" i1 i2 c0
  in List.iter pr_entry ps

let pr_fis_for_min ch ( ds, ps ) =
  let rec pr_next i ( i1, i2 ) prs moreps =
    match prs with
    | ( ( j1, _ ), ( j2, _ ) ) :: rest ->
      if i1 = i2 then 
        Printf.fprintf ch "%d 1 %d %d -2.0\n" i i1 i2
      else
        Printf.fprintf ch "%d 1 %d %d -1.0\n" i i1 i2;
      Printf.fprintf ch "%d 1 %d %d 1.0\n" i j1 j2;
      pr_next ( i + 1 ) ( i1, i2 ) rest moreps
    | [] ->
      match moreps with
      | ( _, _, ( c, ( ( ni1, _ ), ( ni2, _ ) ) :: nprs ) ) :: nmoreps 
        -> pr_next i ( ni1, ni2 ) nprs nmoreps
      | _ -> ()
  in 
  let newps =
    match ps with
    | ( 1, m, ( c, [ ( ( 1, m1 ), ( 1, m2 ) ) ] ) ) :: moreps
      ->  let n = Array.length m in
          if isone m && isone m1 && isone m2 then moreps else ps
    | _ -> ps
  in
  Printf.fprintf ch "1 1 1 1 1.0\n";
  pr_next 2 ( 1, 1 ) [] newps

let pr_header_for_min ch ( ds, ps ) =
  let m = List.length ds in
  let s = List.length ps in
  let r = m * ( m + 1 ) / 2 - s + 1 in
  Printf.fprintf ch "%d\n1\n%d\n" r m;
  Printf.fprintf ch "1.0 ";
  for i = 1 to r - 1 do Printf.fprintf ch "0.0 " done;
  Printf.fprintf ch "\n"
    
let pr_sdpa_for_min ch ( ds, ps ) =
  let _ = pr_header_for_min ch ( ds, ps ) in
  let _ = pr_f0_for_min ch ( ds, ps ) in
  pr_fis_for_min ch ( ds, ps )
