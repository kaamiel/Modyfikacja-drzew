(*  Zadanie 3: Modyfikacja drzew  *)
(*  autor: Kamil Dubil, 370826    *)
(*  reviewer:     -               *)

(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl,
 * Jacek Chrzaszcz, Kamil Dubil
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(** Interval Set.

    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint. 

*)

(* Wszystkie operacje (poza fold, iter, elements oraz is_empty) wykonują się *)
(* w czasie O(log n), gdzie n jest liczbą wierzchołków w drzewie.            *)

(* Typ zbioru przedziałów, piątka:                                              *)
(* lewe_poddrzewo * [pocz, kon] * prawe_poddrzewo * liczba_elementów * wysokosc *)
type t =
    | Empty
    | Node of t * (int * int) * t * int * int

(* Zbiór pusty *)
let empty = Empty

(* Bezpieczne dodawanie (odporne na wartości w pobliżu min_int i max_int) *)
let rec plus x y =
    if x <= 0 && y <= 0 && x + y > 0 then min_int
    else if x >= 0 && y >= 0 && x + y < 0 then max_int
    else x + y

(* Zwraca true wtedy i tylko wtedy, gdy zbiór jest pusty *)
let is_empty s =
    s = Empty

(* Liczba elementów zbioru *)
let number_of_elements = function
    | Empty -> 0
    | Node (_, _, _, n, _) -> n

(* Wysokość drzewa *)
let height = function
    | Empty -> 0
    | Node (_, _, _, _, h) -> h

(* Najmniejszy element zbioru (przedział) *)
let rec min_elt = function
    | Empty -> raise Not_found
    | Node (Empty, k, _, _, _) -> k
    | Node (l, _, _, _, _) -> min_elt l

(* Największy element zbioru (przedzial) *)
let rec max_elt = function
    | Empty -> raise Not_found
    | Node (_, k, Empty, _, _) -> k
    | Node (_, _, r, _, _) -> max_elt r

(* Liczba całkowitych liczb w przedziale [x, y] *)
let length_of_interval (x, y) =
    if x = min_int then plus (plus y max_int) 2
    else plus (plus y (-x)) 1

(* Suma liczby elementów drzew l, r i przedziału x *)
let size_sum l k r =
    plus
        (plus (number_of_elements l) (number_of_elements r))
        (length_of_interval k)

(* Utworzenie zbioru z danych dwóch drzew i przedziału              *)
(* Założenie: elementy l < elementy k < elementy r,                 *)
(* l i r są zbalansowane i ich wysokości różnią się co najwyżej o 2 *)
(* wynik jest zbalansowany                                          *)
let make l k r =
    Node (l, k, r, size_sum l k r, max (height l) (height r) + 1)

(* Wyważanie drzewa (wariant AVL z maksymalną różnicą wysokości równą 2) *)
(* Założenie: elementy l < elementy k < elementy r,                      *)
(* l i r są zbalansowane i ich wysokości różnią się co najwyżej o 3      *)
(* wynik (oczywiście) jest zbalansowany                                  *)
let bal l k r =
    let hl = height l in
    let hr = height r in
    if hl > hr + 2
        then match l with
        | Node (ll, lk, lr, _, _) ->
            if height ll >= height lr then make ll lk (make lr k r)
            else
                (match lr with
                | Node (lrl, lrk, lrr, _, _) ->
                    make (make ll lk lrl) lrk (make lrr k r)
                | Empty -> assert false)
        | Empty -> assert false
    else if hr > hl + 2 then
        match r with
        | Node (rl, rk, rr, _, _) ->
            if height rr >= height rl then make (make l k rl) rk rr
            else
                (match rl with
                | Node (rll, rlk, rlr, _, _) ->
                    make (make l k rll) rlk (make rlr rk rr)
                | Empty -> assert false)
        | Empty -> assert false
    else make l k r

(* Usunięcie najmniejszego elementu, wynik jest zbalansowany *)
let rec remove_min_elt = function
    | Node (Empty, _, r, _, _) -> r
    | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
    | Empty -> invalid_arg "ISet.remove_min_elt"

(* Usunięcie największego elementu, wynik jest zbalansowany *)
let rec remove_max_elt = function
    | Node (l, _, Empty, _, _) -> l
    | Node (l, k, r, _, _) -> bal l k (remove_max_elt r)
    | Empty -> invalid_arg "ISet.remove_max_elt"

(* Połączenie dwóch zbiorów                                                   *)
(* Założenie: t1 i t2 zbalansowane, ich wysokości różnią się co najwyżej o 3, *)
(* elementy t1 < elementy t2,   wynik jest zbalansowany                       *)
let merge t1 t2 =
    match t1, t2 with
    | Empty, _ -> t2
    | _, Empty -> t1
    | _ -> let k = min_elt t2
        in bal t1 k (remove_min_elt t2)

(* Prosta wersja dodania elementu do zbioru                          *)
(* Założenie: przedział [a,b] jest rozłączny (w sensie tego zadania) *)
(* z każdym elementem zbioru s,   wynik jest zbalansowany            *)
let rec add_simply (a, b) s =
    match s with
    | Empty -> Node (Empty, (a, b), Empty, length_of_interval (a, b), 1)
    | Node (l, (x, y), r, _, h) ->
        if plus b 1 < x
            then bal (add_simply (a, b) l) (x, y) r
        else if y < plus a (-1)
            then bal l (x, y) (add_simply (a, b) r)
        else invalid_arg "ISet.add_simply"

(* Założenie: l, r - zbalansowane, niełączliwe z k *)
(* wynik jest zbalansowany                         *)
let rec join l k r =
    match l, r with
    | Empty, _ -> add_simply k r
    | _, Empty -> add_simply k l
    | Node(ll, lk, lr, _, lh), Node(rl, rk, rr, _, rh) ->
        if lh > rh + 2 then bal ll lk (join lr k r)
        else if rh > lh + 2 then bal (join l k rl) rk rr
        else make l k r

(* [split x s] returns a triple [(l, present, r)], where
    [l] is the set of elements of [s] that are strictly lesser than [x];
    [r] is the set of elements of [s] that are strictly greater than [x];
    [present] is [false] if [s] contains no element equal to [x],
    or [true] if [s] contains an element equal to [x]. *)
let split a s =
    let rec loop = function
        | Empty -> (Empty, false, Empty)
        | Node (l, (x, y), r, _, _) ->
            if x <= a && a <= y
                then let l1 = if x < a then add_simply (x, plus a (-1)) l else l
                and r1 = if a < y then add_simply (plus a 1, y) r else r
                in (l1, true, r1)
            else if a < x
                then let (ll, pres, rl) = loop l
                in (ll, pres, join rl (x, y) r)
            else
                let (lr, pres, rr) = loop r
                in (join l (x, y) lr, pres, rr)
    in loop s

(* [add (x, y) s] returns a set containing the same elements as [s],
    plus all elements of the interval [[x,y]] including [x] and [y].
    Assumes [x <= y]. *)
(* wynik jest zbalansowany *)
let add (a, b) s =
    let (sl, _, _) = split a s
    and (_, _, sr) = split b s
    in match (sl, sr) with
    | (Empty, Empty) -> add_simply (a, b) empty
    | _ ->
        let (sl_red, sl_max) =
            if is_empty sl then (sl, a)
            else
                let (x, y) = max_elt sl
                in if y + 1 >= a then (remove_max_elt sl, x)
                else (sl, a)
        and (sr_red, sr_min) =
            if is_empty sr then (sr, b)
            else
                let (x, y) = min_elt sr
                in if x - 1 <= b then (remove_min_elt sr, y)
                else (sr, b)
        in
        join sl_red (sl_max, sr_min) sr_red

(* usuwa z drzewa przedział (a, b) przy założeniu,      *)
(* że istnieje wierzchołek, który zawiera ten przedział *)
(* wynik jest zbalansowany                              *)
let rec remove_simply (a, b) = function
    | Node (l, (x, y), r, _, _) ->
        if (x <= a && b <= y)
            then let l1 = if x < a then add (x, plus a (-1)) l else l
            and r1 = if b < y then add (plus b 1, y) r else r
            in merge l1 r1
        else if (y < a) then bal l (x, y) (remove_simply (a, b) r)
        else bal (remove_simply (a, b) l) (x, y) r
    | Empty -> invalid_arg "ISet.remove_reduced"

(* [remove (x, y) s] returns a set containing the same elements as [s],
    except for all those which are included between [x] and [y].
    Assumes [x <= y]. *)
(* wynik jest zbalansowany *)
let remove x s =
    let s2 = add x s
    in remove_simply x s2

(* [mem x s] returns [true] if [s] contains [x], and [false] otherwise. *)
let mem a s =
    let rec loop = function
        | Empty -> false
        | Node (l, (x, y), r, _, _) ->
            if x <= a && a <= y then true
            else loop (if a < x then l else r)
    in loop s

(* [iter f s] applies [f] to all continuous intervals in the set [s].
    The intervals are passed to [f] in increasing order. *)
let iter f s =
    let rec loop = function
        | Empty -> ()
        | Node (l, k, r, _, _) -> loop l; f k; loop r
    in loop s

(* [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)], where x1
    ... xN are all continuous intervals of s, in increasing order. *)
let fold f s acc =
    let rec loop acc = function
        | Empty -> acc
        | Node (l, k, r, _, _) -> loop (f k (loop acc l)) r
    in loop acc s

(* Return the list of all continuous intervals of the given set.
    The returned list is sorted in increasing order. *)
let elements s =
    let rec loop acc = function
        | Empty -> acc
        | Node (l, k, r, _, _) -> loop (k :: (loop acc r)) l
    in loop [] s

(* [below n s] returns the number of elements of [s] that are lesser
    or equal to [n]. If there are more than max_int such elements, 
    the result should be max_int. *)
let below a s =
    let rec loop acc = function
        | Empty -> acc
        | Node (l, (x, y), r, _, _) ->
            if (x <= a && a <= y)
                then plus
                    acc
                    (plus (number_of_elements l) (length_of_interval (x, a)))
            else if a < x then loop acc l
            else loop
                (plus
                    acc
                    (plus (number_of_elements l) (length_of_interval (x, y))))
                r
    in loop 0 s

(*****************************************************************************)

(* testy *)

(*

open ISet;;
let print_pair (x,y) =
print_string "[";
print_int x;
print_string " ";
print_int y;
print_string "] ";;
let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (170, 183) a ;;
let a = add (-227, -218) a ;;
let a = add (2045, 2055) a ;;
let a = add (658, 672) a ;;
let a = add (-1114, -1102) a ;;
let a = add (-2639, -2628) a ;;
let a = add (-4415, -4404) a ;;
let a = add (-4536, -4527) a ;;
let a = add (2100, 2106) a ;;
let a = add (-1273, -1265) a ;;
let a = add (-3923, -3921) a ;;
let a = add (459, 461) a ;;
let a = add (-1133, -1130) a ;;
let a = add (-1329, -1325) a ;;
let a = add (470, 481) a ;;
let a = add (-357, -350) a ;;
let a = add (-1825, -1821) a ;;
let a = add (-1186, -1172) a ;;
let a = add (282, 283) a ;;
let a = add (-3760, -3759) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("-1408 - ") ;;
 print_string (string_of_bool (mem (-1408) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3591 - ") ;;
 print_string (string_of_bool (mem (-3591) a) ) ;;
 print_string "\n" ;; 
 print_string ("3668 - ") ;;
 print_string (string_of_bool (mem (3668) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3022 - ") ;;
 print_string (string_of_bool (mem (-3022) a) ) ;;
 print_string "\n" ;; 
 print_string ("4473 - ") ;;
 print_string (string_of_bool (mem (4473) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2482 - ") ;;
 print_string (string_of_bool (mem (-2482) a) ) ;;
 print_string "\n" ;; 
 print_string ("2097 - ") ;;
 print_string (string_of_bool (mem (2097) a) ) ;;
 print_string "\n" ;; 
 print_string ("2535 - ") ;;
 print_string (string_of_bool (mem (2535) a) ) ;;
 print_string "\n" ;; 
 print_string ("3310 - ") ;;
 print_string (string_of_bool (mem (3310) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2167 - ") ;;
 print_string (string_of_bool (mem (-2167) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4109 - ") ;;
 print_string (string_of_bool (mem (-4109) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2674 - ") ;;
 print_string (string_of_bool (mem (-2674) a) ) ;;
 print_string "\n" ;; 
 print_string ("471 - ") ;;
 print_string (string_of_bool (mem (471) a) ) ;;
 print_string "\n" ;; 
 print_string ("3977 - ") ;;
 print_string (string_of_bool (mem (3977) a) ) ;;
 print_string "\n" ;; 
 print_string ("3069 - ") ;;
 print_string (string_of_bool (mem (3069) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3631 - ") ;;
 print_string (string_of_bool (mem (-3631) a) ) ;;
 print_string "\n" ;; 
 print_string ("119 - ") ;;
 print_string (string_of_bool (mem (119) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4722 - ") ;;
 print_string (string_of_bool (mem (-4722) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2260 - ") ;;
 print_string (string_of_bool (mem (-2260) a) ) ;;
 print_string "\n" ;; 
 print_string ("4941 - ") ;;
 print_string (string_of_bool (mem (4941) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2765 - ") ;;
 print_string (string_of_bool (mem (-2765) a) ) ;;
 print_string "\n" ;; 
 print_string ("357 - ") ;;
 print_string (string_of_bool (mem (357) a) ) ;;
 print_string "\n" ;; 
 print_string ("376 - ") ;;
 print_string (string_of_bool (mem (376) a) ) ;;
 print_string "\n" ;; 
 print_string ("3483 - ") ;;
 print_string (string_of_bool (mem (3483) a) ) ;;
 print_string "\n" ;; 
 print_string ("1034 - ") ;;
 print_string (string_of_bool (mem (1034) a) ) ;;
 print_string "\n" ;; 
 print_string ("173 - ") ;;
 print_string (string_of_bool (mem (173) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2674 - ") ;;
 print_string (string_of_bool (mem (-2674) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3813 - ") ;;
 print_string (string_of_bool (mem (-3813) a) ) ;;
 print_string "\n" ;; 
 print_string ("3508 - ") ;;
 print_string (string_of_bool (mem (3508) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3051 - ") ;;
 print_string (string_of_bool (mem (-3051) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (4700) a) ;
print_string "\n" ;;
print_int (below (2406) a) ;
print_string "\n" ;;
print_int (below (-1609) a) ;
print_string "\n" ;;
print_int (below (-4959) a) ;
print_string "\n" ;;
print_int (below (4874) a) ;
print_string "\n" ;;
print_int (below (-1955) a) ;
print_string "\n" ;;
print_int (below (2324) a) ;
print_string "\n" ;;
print_int (below (206) a) ;
print_string "\n" ;;
print_int (below (-2908) a) ;
print_string "\n" ;;
print_int (below (-4090) a) ;
print_string "\n" ;;
print_int (below (-2043) a) ;
print_string "\n" ;;
print_int (below (-1791) a) ;
print_string "\n" ;;
print_int (below (4815) a) ;
print_string "\n" ;;
print_int (below (-4214) a) ;
print_string "\n" ;;
print_int (below (4746) a) ;
print_string "\n" ;;
print_int (below (4900) a) ;
print_string "\n" ;;
print_int (below (300) a) ;
print_string "\n" ;;
print_int (below (-1970) a) ;
print_string "\n" ;;
print_int (below (787) a) ;
print_string "\n" ;;
print_int (below (-3483) a) ;
print_string "\n" ;;
print_int (below (3182) a) ;
print_string "\n" ;;
print_int (below (1005) a) ;
print_string "\n" ;;
print_int (below (-4103) a) ;
print_string "\n" ;;
print_int (below (-910) a) ;
print_string "\n" ;;
print_int (below (3956) a) ;
print_string "\n" ;;
print_int (below (-3658) a) ;
print_string "\n" ;;
print_int (below (-1968) a) ;
print_string "\n" ;;
print_int (below (-717) a) ;
print_string "\n" ;;
print_int (below (-2405) a) ;
print_string "\n" ;;
print_int (below (-106) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (4901) a) ;
print_string "\n" ;;
print_int (below (2950) a) ;
print_string "\n" ;;
print_int (below (16) a) ;
print_string "\n" ;;
print_int (below (4815) a) ;
print_string "\n" ;;
print_int (below (4554) a) ;
print_string "\n" ;;
print_int (below (-4169) a) ;
print_string "\n" ;;
print_int (below (89) a) ;
print_string "\n" ;;
print_int (below (947) a) ;
print_string "\n" ;;
print_int (below (4089) a) ;
print_string "\n" ;;
print_int (below (-3907) a) ;
print_string "\n" ;;
print_int (below (4562) a) ;
print_string "\n" ;;
print_int (below (397) a) ;
print_string "\n" ;;
print_int (below (719) a) ;
print_string "\n" ;;
print_int (below (-4665) a) ;
print_string "\n" ;;
print_int (below (-3749) a) ;
print_string "\n" ;;
print_int (below (-2980) a) ;
print_string "\n" ;;
print_int (below (2481) a) ;
print_string "\n" ;;
print_int (below (205) a) ;
print_string "\n" ;;
print_int (below (3555) a) ;
print_string "\n" ;;
print_int (below (-4654) a) ;
print_string "\n" ;;
print_int (below (-1023) a) ;
print_string "\n" ;;
print_int (below (2198) a) ;
print_string "\n" ;;
print_int (below (350) a) ;
print_string "\n" ;;
print_int (below (-1656) a) ;
print_string "\n" ;;
print_int (below (-2708) a) ;
print_string "\n" ;;
print_int (below (189) a) ;
print_string "\n" ;;
print_int (below (833) a) ;
print_string "\n" ;;
print_int (below (-1505) a) ;
print_string "\n" ;;
print_int (below (3052) a) ;
print_string "\n" ;;
print_int (below (-2382) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (3646, 3650) a ;;
let a = remove (-2479, -2318) a ;;
let a = remove (1329, 1415) a ;;
let a = remove (-2335, -2226) a ;;
let a = remove (2511, 2532) a ;;
let a = remove (4213, 4242) a ;;
let a = remove (1356, 1500) a ;;
let a = remove (1545, 1675) a ;;
let a = remove (-3483, -3448) a ;;
let a = remove (2887, 3056) a ;;
let a = remove (1041, 1124) a ;;
let a = remove (-4197, -4117) a ;;
let a = remove (-2559, -2527) a ;;
let a = remove (4997, 5091) a ;;
let a = remove (-2106, -2000) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (1679, 1690) a ;;
let a = add (-2908, -2894) a ;;
let a = add (2404, 2405) a ;;
let a = add (2734, 2740) a ;;
let a = add (-2321, -2318) a ;;
let a = add (642, 650) a ;;
let a = add (4326, 4330) a ;;
let a = add (-3358, -3346) a ;;
let a = add (3591, 3602) a ;;
let a = add (837, 849) a ;;
let a = add (-943, -929) a ;;
let a = add (-1111, -1104) a ;;
let a = add (-1345, -1338) a ;;
let a = add (4323, 4329) a ;;
let a = add (-1551, -1538) a ;;
let a = add (4199, 4209) a ;;
let a = add (4969, 4971) a ;;
let a = add (1341, 1351) a ;;
let a = add (-4643, -4635) a ;;
let a = add (3564, 3573) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("-3319 - ") ;;
 print_string (string_of_bool (mem (-3319) a) ) ;;
 print_string "\n" ;; 
 print_string ("2156 - ") ;;
 print_string (string_of_bool (mem (2156) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1892 - ") ;;
 print_string (string_of_bool (mem (-1892) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1620 - ") ;;
 print_string (string_of_bool (mem (-1620) a) ) ;;
 print_string "\n" ;; 
 print_string ("1639 - ") ;;
 print_string (string_of_bool (mem (1639) a) ) ;;
 print_string "\n" ;; 
 print_string ("-265 - ") ;;
 print_string (string_of_bool (mem (-265) a) ) ;;
 print_string "\n" ;; 
 print_string ("2709 - ") ;;
 print_string (string_of_bool (mem (2709) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1724 - ") ;;
 print_string (string_of_bool (mem (-1724) a) ) ;;
 print_string "\n" ;; 
 print_string ("2368 - ") ;;
 print_string (string_of_bool (mem (2368) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2341 - ") ;;
 print_string (string_of_bool (mem (-2341) a) ) ;;
 print_string "\n" ;; 
 print_string ("1094 - ") ;;
 print_string (string_of_bool (mem (1094) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3678 - ") ;;
 print_string (string_of_bool (mem (-3678) a) ) ;;
 print_string "\n" ;; 
 print_string ("1679 - ") ;;
 print_string (string_of_bool (mem (1679) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4154 - ") ;;
 print_string (string_of_bool (mem (-4154) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3238 - ") ;;
 print_string (string_of_bool (mem (-3238) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2806 - ") ;;
 print_string (string_of_bool (mem (-2806) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4774 - ") ;;
 print_string (string_of_bool (mem (-4774) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3325 - ") ;;
 print_string (string_of_bool (mem (-3325) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1334 - ") ;;
 print_string (string_of_bool (mem (-1334) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3960 - ") ;;
 print_string (string_of_bool (mem (-3960) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3422 - ") ;;
 print_string (string_of_bool (mem (-3422) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1670 - ") ;;
 print_string (string_of_bool (mem (-1670) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2394 - ") ;;
 print_string (string_of_bool (mem (-2394) a) ) ;;
 print_string "\n" ;; 
 print_string ("4152 - ") ;;
 print_string (string_of_bool (mem (4152) a) ) ;;
 print_string "\n" ;; 
 print_string ("-141 - ") ;;
 print_string (string_of_bool (mem (-141) a) ) ;;
 print_string "\n" ;; 
 print_string ("2099 - ") ;;
 print_string (string_of_bool (mem (2099) a) ) ;;
 print_string "\n" ;; 
 print_string ("1769 - ") ;;
 print_string (string_of_bool (mem (1769) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4093 - ") ;;
 print_string (string_of_bool (mem (-4093) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1804 - ") ;;
 print_string (string_of_bool (mem (-1804) a) ) ;;
 print_string "\n" ;; 
 print_string ("406 - ") ;;
 print_string (string_of_bool (mem (406) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (2240) a) ;
print_string "\n" ;;
print_int (below (-2952) a) ;
print_string "\n" ;;
print_int (below (-4527) a) ;
print_string "\n" ;;
print_int (below (1386) a) ;
print_string "\n" ;;
print_int (below (3927) a) ;
print_string "\n" ;;
print_int (below (-1539) a) ;
print_string "\n" ;;
print_int (below (4572) a) ;
print_string "\n" ;;
print_int (below (4832) a) ;
print_string "\n" ;;
print_int (below (4309) a) ;
print_string "\n" ;;
print_int (below (3080) a) ;
print_string "\n" ;;
print_int (below (-1829) a) ;
print_string "\n" ;;
print_int (below (-3390) a) ;
print_string "\n" ;;
print_int (below (-3661) a) ;
print_string "\n" ;;
print_int (below (-3400) a) ;
print_string "\n" ;;
print_int (below (2083) a) ;
print_string "\n" ;;
print_int (below (-1860) a) ;
print_string "\n" ;;
print_int (below (4722) a) ;
print_string "\n" ;;
print_int (below (2690) a) ;
print_string "\n" ;;
print_int (below (1089) a) ;
print_string "\n" ;;
print_int (below (2816) a) ;
print_string "\n" ;;
print_int (below (-775) a) ;
print_string "\n" ;;
print_int (below (-69) a) ;
print_string "\n" ;;
print_int (below (-3917) a) ;
print_string "\n" ;;
print_int (below (17) a) ;
print_string "\n" ;;
print_int (below (-1589) a) ;
print_string "\n" ;;
print_int (below (-4029) a) ;
print_string "\n" ;;
print_int (below (-4628) a) ;
print_string "\n" ;;
print_int (below (4722) a) ;
print_string "\n" ;;
print_int (below (2607) a) ;
print_string "\n" ;;
print_int (below (107) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (-4632) a) ;
print_string "\n" ;;
print_int (below (365) a) ;
print_string "\n" ;;
print_int (below (1779) a) ;
print_string "\n" ;;
print_int (below (-4956) a) ;
print_string "\n" ;;
print_int (below (4836) a) ;
print_string "\n" ;;
print_int (below (-589) a) ;
print_string "\n" ;;
print_int (below (-2128) a) ;
print_string "\n" ;;
print_int (below (-3662) a) ;
print_string "\n" ;;
print_int (below (-1912) a) ;
print_string "\n" ;;
print_int (below (1976) a) ;
print_string "\n" ;;
print_int (below (-3128) a) ;
print_string "\n" ;;
print_int (below (-3273) a) ;
print_string "\n" ;;
print_int (below (-4776) a) ;
print_string "\n" ;;
print_int (below (-2399) a) ;
print_string "\n" ;;
print_int (below (2469) a) ;
print_string "\n" ;;
print_int (below (-3425) a) ;
print_string "\n" ;;
print_int (below (-4474) a) ;
print_string "\n" ;;
print_int (below (-2807) a) ;
print_string "\n" ;;
print_int (below (903) a) ;
print_string "\n" ;;
print_int (below (-474) a) ;
print_string "\n" ;;
print_int (below (1888) a) ;
print_string "\n" ;;
print_int (below (2703) a) ;
print_string "\n" ;;
print_int (below (-3075) a) ;
print_string "\n" ;;
print_int (below (-2766) a) ;
print_string "\n" ;;
print_int (below (1397) a) ;
print_string "\n" ;;
print_int (below (-4841) a) ;
print_string "\n" ;;
print_int (below (2099) a) ;
print_string "\n" ;;
print_int (below (-3634) a) ;
print_string "\n" ;;
print_int (below (-2461) a) ;
print_string "\n" ;;
print_int (below (1963) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (3540, 3723) a ;;
let a = remove (-4366, -4175) a ;;
let a = remove (619, 726) a ;;
let a = remove (2446, 2593) a ;;
let a = remove (-4862, -4746) a ;;
let a = remove (2937, 2971) a ;;
let a = remove (-4276, -4148) a ;;
let a = remove (-4118, -3939) a ;;
let a = remove (-3584, -3578) a ;;
let a = remove (-2398, -2277) a ;;
let a = remove (-3680, -3618) a ;;
let a = remove (-2064, -1967) a ;;
let a = remove (4607, 4643) a ;;
let a = remove (1266, 1332) a ;;
let a = remove (4813, 4964) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (-81, -80) a ;;
let a = add (3115, 3118) a ;;
let a = add (3595, 3605) a ;;
let a = add (1174, 1179) a ;;
let a = add (3333, 3347) a ;;
let a = add (-2454, -2446) a ;;
let a = add (-4668, -4668) a ;;
let a = add (118, 127) a ;;
let a = add (3354, 3360) a ;;
let a = add (-4172, -4164) a ;;
let a = add (-3923, -3922) a ;;
let a = add (324, 337) a ;;
let a = add (3829, 3842) a ;;
let a = add (2611, 2621) a ;;
let a = add (-1657, -1646) a ;;
let a = add (3351, 3359) a ;;
let a = add (2587, 2591) a ;;
let a = add (3729, 3738) a ;;
let a = add (2398, 2410) a ;;
let a = add (2392, 2403) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("-2220 - ") ;;
 print_string (string_of_bool (mem (-2220) a) ) ;;
 print_string "\n" ;; 
 print_string ("-781 - ") ;;
 print_string (string_of_bool (mem (-781) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1470 - ") ;;
 print_string (string_of_bool (mem (-1470) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4875 - ") ;;
 print_string (string_of_bool (mem (-4875) a) ) ;;
 print_string "\n" ;; 
 print_string ("4561 - ") ;;
 print_string (string_of_bool (mem (4561) a) ) ;;
 print_string "\n" ;; 
 print_string ("4263 - ") ;;
 print_string (string_of_bool (mem (4263) a) ) ;;
 print_string "\n" ;; 
 print_string ("1532 - ") ;;
 print_string (string_of_bool (mem (1532) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3027 - ") ;;
 print_string (string_of_bool (mem (-3027) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4271 - ") ;;
 print_string (string_of_bool (mem (-4271) a) ) ;;
 print_string "\n" ;; 
 print_string ("642 - ") ;;
 print_string (string_of_bool (mem (642) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2108 - ") ;;
 print_string (string_of_bool (mem (-2108) a) ) ;;
 print_string "\n" ;; 
 print_string ("588 - ") ;;
 print_string (string_of_bool (mem (588) a) ) ;;
 print_string "\n" ;; 
 print_string ("3203 - ") ;;
 print_string (string_of_bool (mem (3203) a) ) ;;
 print_string "\n" ;; 
 print_string ("2151 - ") ;;
 print_string (string_of_bool (mem (2151) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1730 - ") ;;
 print_string (string_of_bool (mem (-1730) a) ) ;;
 print_string "\n" ;; 
 print_string ("1824 - ") ;;
 print_string (string_of_bool (mem (1824) a) ) ;;
 print_string "\n" ;; 
 print_string ("-519 - ") ;;
 print_string (string_of_bool (mem (-519) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1474 - ") ;;
 print_string (string_of_bool (mem (-1474) a) ) ;;
 print_string "\n" ;; 
 print_string ("-978 - ") ;;
 print_string (string_of_bool (mem (-978) a) ) ;;
 print_string "\n" ;; 
 print_string ("3640 - ") ;;
 print_string (string_of_bool (mem (3640) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1501 - ") ;;
 print_string (string_of_bool (mem (-1501) a) ) ;;
 print_string "\n" ;; 
 print_string ("1520 - ") ;;
 print_string (string_of_bool (mem (1520) a) ) ;;
 print_string "\n" ;; 
 print_string ("-175 - ") ;;
 print_string (string_of_bool (mem (-175) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4855 - ") ;;
 print_string (string_of_bool (mem (-4855) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4781 - ") ;;
 print_string (string_of_bool (mem (-4781) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2657 - ") ;;
 print_string (string_of_bool (mem (-2657) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2318 - ") ;;
 print_string (string_of_bool (mem (-2318) a) ) ;;
 print_string "\n" ;; 
 print_string ("3693 - ") ;;
 print_string (string_of_bool (mem (3693) a) ) ;;
 print_string "\n" ;; 
 print_string ("2584 - ") ;;
 print_string (string_of_bool (mem (2584) a) ) ;;
 print_string "\n" ;; 
 print_string ("1042 - ") ;;
 print_string (string_of_bool (mem (1042) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (1570) a) ;
print_string "\n" ;;
print_int (below (-4617) a) ;
print_string "\n" ;;
print_int (below (-1823) a) ;
print_string "\n" ;;
print_int (below (-430) a) ;
print_string "\n" ;;
print_int (below (3792) a) ;
print_string "\n" ;;
print_int (below (-2397) a) ;
print_string "\n" ;;
print_int (below (-4678) a) ;
print_string "\n" ;;
print_int (below (-4679) a) ;
print_string "\n" ;;
print_int (below (4817) a) ;
print_string "\n" ;;
print_int (below (652) a) ;
print_string "\n" ;;
print_int (below (1384) a) ;
print_string "\n" ;;
print_int (below (543) a) ;
print_string "\n" ;;
print_int (below (2907) a) ;
print_string "\n" ;;
print_int (below (-576) a) ;
print_string "\n" ;;
print_int (below (2785) a) ;
print_string "\n" ;;
print_int (below (-2510) a) ;
print_string "\n" ;;
print_int (below (-2188) a) ;
print_string "\n" ;;
print_int (below (-4148) a) ;
print_string "\n" ;;
print_int (below (4570) a) ;
print_string "\n" ;;
print_int (below (4517) a) ;
print_string "\n" ;;
print_int (below (1352) a) ;
print_string "\n" ;;
print_int (below (1359) a) ;
print_string "\n" ;;
print_int (below (-2184) a) ;
print_string "\n" ;;
print_int (below (-3588) a) ;
print_string "\n" ;;
print_int (below (1925) a) ;
print_string "\n" ;;
print_int (below (-655) a) ;
print_string "\n" ;;
print_int (below (3902) a) ;
print_string "\n" ;;
print_int (below (3364) a) ;
print_string "\n" ;;
print_int (below (1786) a) ;
print_string "\n" ;;
print_int (below (-5) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (-3263) a) ;
print_string "\n" ;;
print_int (below (-1630) a) ;
print_string "\n" ;;
print_int (below (994) a) ;
print_string "\n" ;;
print_int (below (2167) a) ;
print_string "\n" ;;
print_int (below (3060) a) ;
print_string "\n" ;;
print_int (below (-278) a) ;
print_string "\n" ;;
print_int (below (1302) a) ;
print_string "\n" ;;
print_int (below (3147) a) ;
print_string "\n" ;;
print_int (below (-4029) a) ;
print_string "\n" ;;
print_int (below (3191) a) ;
print_string "\n" ;;
print_int (below (2328) a) ;
print_string "\n" ;;
print_int (below (616) a) ;
print_string "\n" ;;
print_int (below (44) a) ;
print_string "\n" ;;
print_int (below (-4392) a) ;
print_string "\n" ;;
print_int (below (1976) a) ;
print_string "\n" ;;
print_int (below (-4106) a) ;
print_string "\n" ;;
print_int (below (-3265) a) ;
print_string "\n" ;;
print_int (below (3395) a) ;
print_string "\n" ;;
print_int (below (2867) a) ;
print_string "\n" ;;
print_int (below (1176) a) ;
print_string "\n" ;;
print_int (below (-4950) a) ;
print_string "\n" ;;
print_int (below (1693) a) ;
print_string "\n" ;;
print_int (below (797) a) ;
print_string "\n" ;;
print_int (below (1091) a) ;
print_string "\n" ;;
print_int (below (4280) a) ;
print_string "\n" ;;
print_int (below (2132) a) ;
print_string "\n" ;;
print_int (below (4481) a) ;
print_string "\n" ;;
print_int (below (-542) a) ;
print_string "\n" ;;
print_int (below (-784) a) ;
print_string "\n" ;;
print_int (below (-412) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (-2037, -1885) a ;;
let a = remove (302, 449) a ;;
let a = remove (-914, -853) a ;;
let a = remove (-3443, -3432) a ;;
let a = remove (1250, 1266) a ;;
let a = remove (-2047, -1940) a ;;
let a = remove (-3225, -3132) a ;;
let a = remove (-357, -183) a ;;
let a = remove (-810, -806) a ;;
let a = remove (1594, 1610) a ;;
let a = remove (-4355, -4268) a ;;
let a = remove (60, 155) a ;;
let a = remove (4159, 4282) a ;;
let a = remove (-173, -143) a ;;
let a = remove (-4784, -4601) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (2000, 2005) a ;;
let a = add (-1659, -1652) a ;;
let a = add (-1953, -1939) a ;;
let a = add (-3079, -3066) a ;;
let a = add (-1435, -1423) a ;;
let a = add (-204, -202) a ;;
let a = add (-3491, -3481) a ;;
let a = add (4739, 4744) a ;;
let a = add (-462, -460) a ;;
let a = add (644, 656) a ;;
let a = add (1979, 1984) a ;;
let a = add (659, 668) a ;;
let a = add (-2316, -2309) a ;;
let a = add (4910, 4917) a ;;
let a = add (336, 347) a ;;
let a = add (3528, 3536) a ;;
let a = add (-2875, -2870) a ;;
let a = add (33, 40) a ;;
let a = add (4563, 4576) a ;;
let a = add (-2612, -2603) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("431 - ") ;;
 print_string (string_of_bool (mem (431) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2445 - ") ;;
 print_string (string_of_bool (mem (-2445) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3516 - ") ;;
 print_string (string_of_bool (mem (-3516) a) ) ;;
 print_string "\n" ;; 
 print_string ("2448 - ") ;;
 print_string (string_of_bool (mem (2448) a) ) ;;
 print_string "\n" ;; 
 print_string ("4670 - ") ;;
 print_string (string_of_bool (mem (4670) a) ) ;;
 print_string "\n" ;; 
 print_string ("2095 - ") ;;
 print_string (string_of_bool (mem (2095) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2329 - ") ;;
 print_string (string_of_bool (mem (-2329) a) ) ;;
 print_string "\n" ;; 
 print_string ("-498 - ") ;;
 print_string (string_of_bool (mem (-498) a) ) ;;
 print_string "\n" ;; 
 print_string ("2311 - ") ;;
 print_string (string_of_bool (mem (2311) a) ) ;;
 print_string "\n" ;; 
 print_string ("3761 - ") ;;
 print_string (string_of_bool (mem (3761) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3014 - ") ;;
 print_string (string_of_bool (mem (-3014) a) ) ;;
 print_string "\n" ;; 
 print_string ("219 - ") ;;
 print_string (string_of_bool (mem (219) a) ) ;;
 print_string "\n" ;; 
 print_string ("4800 - ") ;;
 print_string (string_of_bool (mem (4800) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3017 - ") ;;
 print_string (string_of_bool (mem (-3017) a) ) ;;
 print_string "\n" ;; 
 print_string ("3747 - ") ;;
 print_string (string_of_bool (mem (3747) a) ) ;;
 print_string "\n" ;; 
 print_string ("2345 - ") ;;
 print_string (string_of_bool (mem (2345) a) ) ;;
 print_string "\n" ;; 
 print_string ("3102 - ") ;;
 print_string (string_of_bool (mem (3102) a) ) ;;
 print_string "\n" ;; 
 print_string ("597 - ") ;;
 print_string (string_of_bool (mem (597) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3047 - ") ;;
 print_string (string_of_bool (mem (-3047) a) ) ;;
 print_string "\n" ;; 
 print_string ("-155 - ") ;;
 print_string (string_of_bool (mem (-155) a) ) ;;
 print_string "\n" ;; 
 print_string ("3681 - ") ;;
 print_string (string_of_bool (mem (3681) a) ) ;;
 print_string "\n" ;; 
 print_string ("4584 - ") ;;
 print_string (string_of_bool (mem (4584) a) ) ;;
 print_string "\n" ;; 
 print_string ("1033 - ") ;;
 print_string (string_of_bool (mem (1033) a) ) ;;
 print_string "\n" ;; 
 print_string ("2300 - ") ;;
 print_string (string_of_bool (mem (2300) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4417 - ") ;;
 print_string (string_of_bool (mem (-4417) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3530 - ") ;;
 print_string (string_of_bool (mem (-3530) a) ) ;;
 print_string "\n" ;; 
 print_string ("2624 - ") ;;
 print_string (string_of_bool (mem (2624) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1567 - ") ;;
 print_string (string_of_bool (mem (-1567) a) ) ;;
 print_string "\n" ;; 
 print_string ("2588 - ") ;;
 print_string (string_of_bool (mem (2588) a) ) ;;
 print_string "\n" ;; 
 print_string ("-126 - ") ;;
 print_string (string_of_bool (mem (-126) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (-4830) a) ;
print_string "\n" ;;
print_int (below (-3218) a) ;
print_string "\n" ;;
print_int (below (-3614) a) ;
print_string "\n" ;;
print_int (below (-903) a) ;
print_string "\n" ;;
print_int (below (4565) a) ;
print_string "\n" ;;
print_int (below (731) a) ;
print_string "\n" ;;
print_int (below (-4660) a) ;
print_string "\n" ;;
print_int (below (-609) a) ;
print_string "\n" ;;
print_int (below (-1749) a) ;
print_string "\n" ;;
print_int (below (389) a) ;
print_string "\n" ;;
print_int (below (322) a) ;
print_string "\n" ;;
print_int (below (2653) a) ;
print_string "\n" ;;
print_int (below (-374) a) ;
print_string "\n" ;;
print_int (below (371) a) ;
print_string "\n" ;;
print_int (below (-157) a) ;
print_string "\n" ;;
print_int (below (2002) a) ;
print_string "\n" ;;
print_int (below (673) a) ;
print_string "\n" ;;
print_int (below (-2921) a) ;
print_string "\n" ;;
print_int (below (387) a) ;
print_string "\n" ;;
print_int (below (3652) a) ;
print_string "\n" ;;
print_int (below (-3939) a) ;
print_string "\n" ;;
print_int (below (-903) a) ;
print_string "\n" ;;
print_int (below (1050) a) ;
print_string "\n" ;;
print_int (below (645) a) ;
print_string "\n" ;;
print_int (below (2125) a) ;
print_string "\n" ;;
print_int (below (-1670) a) ;
print_string "\n" ;;
print_int (below (2658) a) ;
print_string "\n" ;;
print_int (below (1745) a) ;
print_string "\n" ;;
print_int (below (-4897) a) ;
print_string "\n" ;;
print_int (below (3699) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (-318) a) ;
print_string "\n" ;;
print_int (below (-42) a) ;
print_string "\n" ;;
print_int (below (-2273) a) ;
print_string "\n" ;;
print_int (below (1630) a) ;
print_string "\n" ;;
print_int (below (-844) a) ;
print_string "\n" ;;
print_int (below (-317) a) ;
print_string "\n" ;;
print_int (below (2370) a) ;
print_string "\n" ;;
print_int (below (-4734) a) ;
print_string "\n" ;;
print_int (below (-4084) a) ;
print_string "\n" ;;
print_int (below (-3925) a) ;
print_string "\n" ;;
print_int (below (-4118) a) ;
print_string "\n" ;;
print_int (below (8) a) ;
print_string "\n" ;;
print_int (below (-2623) a) ;
print_string "\n" ;;
print_int (below (2513) a) ;
print_string "\n" ;;
print_int (below (1574) a) ;
print_string "\n" ;;
print_int (below (-3927) a) ;
print_string "\n" ;;
print_int (below (-4617) a) ;
print_string "\n" ;;
print_int (below (4236) a) ;
print_string "\n" ;;
print_int (below (-989) a) ;
print_string "\n" ;;
print_int (below (-902) a) ;
print_string "\n" ;;
print_int (below (-3854) a) ;
print_string "\n" ;;
print_int (below (2968) a) ;
print_string "\n" ;;
print_int (below (3791) a) ;
print_string "\n" ;;
print_int (below (-997) a) ;
print_string "\n" ;;
print_int (below (4434) a) ;
print_string "\n" ;;
print_int (below (1788) a) ;
print_string "\n" ;;
print_int (below (3222) a) ;
print_string "\n" ;;
print_int (below (-3032) a) ;
print_string "\n" ;;
print_int (below (-1254) a) ;
print_string "\n" ;;
print_int (below (1070) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (-813, -740) a ;;
let a = remove (430, 492) a ;;
let a = remove (-3672, -3591) a ;;
let a = remove (927, 1014) a ;;
let a = remove (3498, 3609) a ;;
let a = remove (-3642, -3581) a ;;
let a = remove (-4221, -4134) a ;;
let a = remove (-1010, -901) a ;;
let a = remove (-510, -451) a ;;
let a = remove (-1764, -1635) a ;;
let a = remove (945, 975) a ;;
let a = remove (-3370, -3270) a ;;
let a = remove (-32, 80) a ;;
let a = remove (265, 373) a ;;
let a = remove (-4352, -4231) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (-1016, -1013) a ;;
let a = add (29, 40) a ;;
let a = add (316, 319) a ;;
let a = add (-178, -169) a ;;
let a = add (-2237, -2232) a ;;
let a = add (1718, 1731) a ;;
let a = add (-2548, -2543) a ;;
let a = add (-1400, -1398) a ;;
let a = add (-4264, -4263) a ;;
let a = add (-2973, -2960) a ;;
let a = add (-1846, -1839) a ;;
let a = add (2234, 2236) a ;;
let a = add (-2627, -2625) a ;;
let a = add (-1577, -1572) a ;;
let a = add (2116, 2117) a ;;
let a = add (3847, 3860) a ;;
let a = add (2582, 2589) a ;;
let a = add (3752, 3762) a ;;
let a = add (-2381, -2377) a ;;
let a = add (4397, 4400) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("4650 - ") ;;
 print_string (string_of_bool (mem (4650) a) ) ;;
 print_string "\n" ;; 
 print_string ("504 - ") ;;
 print_string (string_of_bool (mem (504) a) ) ;;
 print_string "\n" ;; 
 print_string ("-336 - ") ;;
 print_string (string_of_bool (mem (-336) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1367 - ") ;;
 print_string (string_of_bool (mem (-1367) a) ) ;;
 print_string "\n" ;; 
 print_string ("3542 - ") ;;
 print_string (string_of_bool (mem (3542) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4540 - ") ;;
 print_string (string_of_bool (mem (-4540) a) ) ;;
 print_string "\n" ;; 
 print_string ("2786 - ") ;;
 print_string (string_of_bool (mem (2786) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2193 - ") ;;
 print_string (string_of_bool (mem (-2193) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3207 - ") ;;
 print_string (string_of_bool (mem (-3207) a) ) ;;
 print_string "\n" ;; 
 print_string ("-799 - ") ;;
 print_string (string_of_bool (mem (-799) a) ) ;;
 print_string "\n" ;; 
 print_string ("4473 - ") ;;
 print_string (string_of_bool (mem (4473) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4541 - ") ;;
 print_string (string_of_bool (mem (-4541) a) ) ;;
 print_string "\n" ;; 
 print_string ("-559 - ") ;;
 print_string (string_of_bool (mem (-559) a) ) ;;
 print_string "\n" ;; 
 print_string ("2718 - ") ;;
 print_string (string_of_bool (mem (2718) a) ) ;;
 print_string "\n" ;; 
 print_string ("2672 - ") ;;
 print_string (string_of_bool (mem (2672) a) ) ;;
 print_string "\n" ;; 
 print_string ("-145 - ") ;;
 print_string (string_of_bool (mem (-145) a) ) ;;
 print_string "\n" ;; 
 print_string ("724 - ") ;;
 print_string (string_of_bool (mem (724) a) ) ;;
 print_string "\n" ;; 
 print_string ("457 - ") ;;
 print_string (string_of_bool (mem (457) a) ) ;;
 print_string "\n" ;; 
 print_string ("15 - ") ;;
 print_string (string_of_bool (mem (15) a) ) ;;
 print_string "\n" ;; 
 print_string ("-375 - ") ;;
 print_string (string_of_bool (mem (-375) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3942 - ") ;;
 print_string (string_of_bool (mem (-3942) a) ) ;;
 print_string "\n" ;; 
 print_string ("4158 - ") ;;
 print_string (string_of_bool (mem (4158) a) ) ;;
 print_string "\n" ;; 
 print_string ("-628 - ") ;;
 print_string (string_of_bool (mem (-628) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2680 - ") ;;
 print_string (string_of_bool (mem (-2680) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2262 - ") ;;
 print_string (string_of_bool (mem (-2262) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4625 - ") ;;
 print_string (string_of_bool (mem (-4625) a) ) ;;
 print_string "\n" ;; 
 print_string ("940 - ") ;;
 print_string (string_of_bool (mem (940) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3874 - ") ;;
 print_string (string_of_bool (mem (-3874) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3793 - ") ;;
 print_string (string_of_bool (mem (-3793) a) ) ;;
 print_string "\n" ;; 
 print_string ("4971 - ") ;;
 print_string (string_of_bool (mem (4971) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (-1919) a) ;
print_string "\n" ;;
print_int (below (141) a) ;
print_string "\n" ;;
print_int (below (767) a) ;
print_string "\n" ;;
print_int (below (56) a) ;
print_string "\n" ;;
print_int (below (1479) a) ;
print_string "\n" ;;
print_int (below (-691) a) ;
print_string "\n" ;;
print_int (below (-4403) a) ;
print_string "\n" ;;
print_int (below (-4854) a) ;
print_string "\n" ;;
print_int (below (3904) a) ;
print_string "\n" ;;
print_int (below (219) a) ;
print_string "\n" ;;
print_int (below (3717) a) ;
print_string "\n" ;;
print_int (below (-605) a) ;
print_string "\n" ;;
print_int (below (-1714) a) ;
print_string "\n" ;;
print_int (below (2508) a) ;
print_string "\n" ;;
print_int (below (2424) a) ;
print_string "\n" ;;
print_int (below (3326) a) ;
print_string "\n" ;;
print_int (below (-3949) a) ;
print_string "\n" ;;
print_int (below (3340) a) ;
print_string "\n" ;;
print_int (below (3121) a) ;
print_string "\n" ;;
print_int (below (1850) a) ;
print_string "\n" ;;
print_int (below (-1532) a) ;
print_string "\n" ;;
print_int (below (2726) a) ;
print_string "\n" ;;
print_int (below (94) a) ;
print_string "\n" ;;
print_int (below (2319) a) ;
print_string "\n" ;;
print_int (below (2818) a) ;
print_string "\n" ;;
print_int (below (-4220) a) ;
print_string "\n" ;;
print_int (below (-3734) a) ;
print_string "\n" ;;
print_int (below (-2545) a) ;
print_string "\n" ;;
print_int (below (-4304) a) ;
print_string "\n" ;;
print_int (below (-3661) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (-237) a) ;
print_string "\n" ;;
print_int (below (2425) a) ;
print_string "\n" ;;
print_int (below (-3158) a) ;
print_string "\n" ;;
print_int (below (-254) a) ;
print_string "\n" ;;
print_int (below (513) a) ;
print_string "\n" ;;
print_int (below (3584) a) ;
print_string "\n" ;;
print_int (below (2349) a) ;
print_string "\n" ;;
print_int (below (-4334) a) ;
print_string "\n" ;;
print_int (below (-242) a) ;
print_string "\n" ;;
print_int (below (4145) a) ;
print_string "\n" ;;
print_int (below (-1896) a) ;
print_string "\n" ;;
print_int (below (947) a) ;
print_string "\n" ;;
print_int (below (3190) a) ;
print_string "\n" ;;
print_int (below (-3783) a) ;
print_string "\n" ;;
print_int (below (1250) a) ;
print_string "\n" ;;
print_int (below (-1928) a) ;
print_string "\n" ;;
print_int (below (-783) a) ;
print_string "\n" ;;
print_int (below (-2026) a) ;
print_string "\n" ;;
print_int (below (1470) a) ;
print_string "\n" ;;
print_int (below (-4277) a) ;
print_string "\n" ;;
print_int (below (-737) a) ;
print_string "\n" ;;
print_int (below (1733) a) ;
print_string "\n" ;;
print_int (below (-523) a) ;
print_string "\n" ;;
print_int (below (-1882) a) ;
print_string "\n" ;;
print_int (below (-425) a) ;
print_string "\n" ;;
print_int (below (-177) a) ;
print_string "\n" ;;
print_int (below (745) a) ;
print_string "\n" ;;
print_int (below (-655) a) ;
print_string "\n" ;;
print_int (below (-2321) a) ;
print_string "\n" ;;
print_int (below (-4134) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (3235, 3397) a ;;
let a = remove (-371, -231) a ;;
let a = remove (-2016, -1843) a ;;
let a = remove (-1293, -1183) a ;;
let a = remove (4154, 4302) a ;;
let a = remove (4677, 4707) a ;;
let a = remove (-1794, -1784) a ;;
let a = remove (1971, 2078) a ;;
let a = remove (-4448, -4254) a ;;
let a = remove (3121, 3250) a ;;
let a = remove (3044, 3235) a ;;
let a = remove (-2158, -1999) a ;;
let a = remove (-3299, -3103) a ;;
let a = remove (-4424, -4303) a ;;
let a = remove (-1286, -1106) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (-1234, -1221) a ;;
let a = add (-4417, -4417) a ;;
let a = add (-4979, -4971) a ;;
let a = add (-1286, -1283) a ;;
let a = add (2880, 2883) a ;;
let a = add (4961, 4971) a ;;
let a = add (1753, 1756) a ;;
let a = add (-1664, -1652) a ;;
let a = add (-3460, -3450) a ;;
let a = add (-4534, -4532) a ;;
let a = add (266, 267) a ;;
let a = add (-1724, -1715) a ;;
let a = add (4741, 4752) a ;;
let a = add (3934, 3942) a ;;
let a = add (2662, 2668) a ;;
let a = add (1717, 1725) a ;;
let a = add (-2982, -2978) a ;;
let a = add (-4532, -4532) a ;;
let a = add (-2032, -2021) a ;;
let a = add (-422, -413) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("-4266 - ") ;;
 print_string (string_of_bool (mem (-4266) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2607 - ") ;;
 print_string (string_of_bool (mem (-2607) a) ) ;;
 print_string "\n" ;; 
 print_string ("4653 - ") ;;
 print_string (string_of_bool (mem (4653) a) ) ;;
 print_string "\n" ;; 
 print_string ("2382 - ") ;;
 print_string (string_of_bool (mem (2382) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4708 - ") ;;
 print_string (string_of_bool (mem (-4708) a) ) ;;
 print_string "\n" ;; 
 print_string ("4680 - ") ;;
 print_string (string_of_bool (mem (4680) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4914 - ") ;;
 print_string (string_of_bool (mem (-4914) a) ) ;;
 print_string "\n" ;; 
 print_string ("1297 - ") ;;
 print_string (string_of_bool (mem (1297) a) ) ;;
 print_string "\n" ;; 
 print_string ("-412 - ") ;;
 print_string (string_of_bool (mem (-412) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3641 - ") ;;
 print_string (string_of_bool (mem (-3641) a) ) ;;
 print_string "\n" ;; 
 print_string ("3794 - ") ;;
 print_string (string_of_bool (mem (3794) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4279 - ") ;;
 print_string (string_of_bool (mem (-4279) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1942 - ") ;;
 print_string (string_of_bool (mem (-1942) a) ) ;;
 print_string "\n" ;; 
 print_string ("2536 - ") ;;
 print_string (string_of_bool (mem (2536) a) ) ;;
 print_string "\n" ;; 
 print_string ("3086 - ") ;;
 print_string (string_of_bool (mem (3086) a) ) ;;
 print_string "\n" ;; 
 print_string ("3192 - ") ;;
 print_string (string_of_bool (mem (3192) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1777 - ") ;;
 print_string (string_of_bool (mem (-1777) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2890 - ") ;;
 print_string (string_of_bool (mem (-2890) a) ) ;;
 print_string "\n" ;; 
 print_string ("144 - ") ;;
 print_string (string_of_bool (mem (144) a) ) ;;
 print_string "\n" ;; 
 print_string ("2177 - ") ;;
 print_string (string_of_bool (mem (2177) a) ) ;;
 print_string "\n" ;; 
 print_string ("1099 - ") ;;
 print_string (string_of_bool (mem (1099) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3915 - ") ;;
 print_string (string_of_bool (mem (-3915) a) ) ;;
 print_string "\n" ;; 
 print_string ("553 - ") ;;
 print_string (string_of_bool (mem (553) a) ) ;;
 print_string "\n" ;; 
 print_string ("-536 - ") ;;
 print_string (string_of_bool (mem (-536) a) ) ;;
 print_string "\n" ;; 
 print_string ("-57 - ") ;;
 print_string (string_of_bool (mem (-57) a) ) ;;
 print_string "\n" ;; 
 print_string ("-712 - ") ;;
 print_string (string_of_bool (mem (-712) a) ) ;;
 print_string "\n" ;; 
 print_string ("1309 - ") ;;
 print_string (string_of_bool (mem (1309) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4610 - ") ;;
 print_string (string_of_bool (mem (-4610) a) ) ;;
 print_string "\n" ;; 
 print_string ("4007 - ") ;;
 print_string (string_of_bool (mem (4007) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1156 - ") ;;
 print_string (string_of_bool (mem (-1156) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (2346) a) ;
print_string "\n" ;;
print_int (below (798) a) ;
print_string "\n" ;;
print_int (below (147) a) ;
print_string "\n" ;;
print_int (below (-1907) a) ;
print_string "\n" ;;
print_int (below (312) a) ;
print_string "\n" ;;
print_int (below (-1496) a) ;
print_string "\n" ;;
print_int (below (-2294) a) ;
print_string "\n" ;;
print_int (below (-129) a) ;
print_string "\n" ;;
print_int (below (-3327) a) ;
print_string "\n" ;;
print_int (below (165) a) ;
print_string "\n" ;;
print_int (below (-1194) a) ;
print_string "\n" ;;
print_int (below (-2235) a) ;
print_string "\n" ;;
print_int (below (-3573) a) ;
print_string "\n" ;;
print_int (below (-3458) a) ;
print_string "\n" ;;
print_int (below (343) a) ;
print_string "\n" ;;
print_int (below (1026) a) ;
print_string "\n" ;;
print_int (below (3962) a) ;
print_string "\n" ;;
print_int (below (3166) a) ;
print_string "\n" ;;
print_int (below (-1864) a) ;
print_string "\n" ;;
print_int (below (2105) a) ;
print_string "\n" ;;
print_int (below (-1861) a) ;
print_string "\n" ;;
print_int (below (1292) a) ;
print_string "\n" ;;
print_int (below (-1716) a) ;
print_string "\n" ;;
print_int (below (-2003) a) ;
print_string "\n" ;;
print_int (below (3438) a) ;
print_string "\n" ;;
print_int (below (4779) a) ;
print_string "\n" ;;
print_int (below (750) a) ;
print_string "\n" ;;
print_int (below (-3487) a) ;
print_string "\n" ;;
print_int (below (-1563) a) ;
print_string "\n" ;;
print_int (below (-4608) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (-2912) a) ;
print_string "\n" ;;
print_int (below (2301) a) ;
print_string "\n" ;;
print_int (below (-3811) a) ;
print_string "\n" ;;
print_int (below (40) a) ;
print_string "\n" ;;
print_int (below (3244) a) ;
print_string "\n" ;;
print_int (below (-556) a) ;
print_string "\n" ;;
print_int (below (2099) a) ;
print_string "\n" ;;
print_int (below (4261) a) ;
print_string "\n" ;;
print_int (below (-4621) a) ;
print_string "\n" ;;
print_int (below (-1563) a) ;
print_string "\n" ;;
print_int (below (-1137) a) ;
print_string "\n" ;;
print_int (below (-4043) a) ;
print_string "\n" ;;
print_int (below (4709) a) ;
print_string "\n" ;;
print_int (below (-3915) a) ;
print_string "\n" ;;
print_int (below (-828) a) ;
print_string "\n" ;;
print_int (below (4532) a) ;
print_string "\n" ;;
print_int (below (-1862) a) ;
print_string "\n" ;;
print_int (below (4670) a) ;
print_string "\n" ;;
print_int (below (-3652) a) ;
print_string "\n" ;;
print_int (below (2702) a) ;
print_string "\n" ;;
print_int (below (3209) a) ;
print_string "\n" ;;
print_int (below (3353) a) ;
print_string "\n" ;;
print_int (below (-2811) a) ;
print_string "\n" ;;
print_int (below (476) a) ;
print_string "\n" ;;
print_int (below (1584) a) ;
print_string "\n" ;;
print_int (below (-1844) a) ;
print_string "\n" ;;
print_int (below (-4735) a) ;
print_string "\n" ;;
print_int (below (961) a) ;
print_string "\n" ;;
print_int (below (3418) a) ;
print_string "\n" ;;
print_int (below (717) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (-1103, -1061) a ;;
let a = remove (2966, 3078) a ;;
let a = remove (4992, 5167) a ;;
let a = remove (4046, 4230) a ;;
let a = remove (3656, 3749) a ;;
let a = remove (-1467, -1346) a ;;
let a = remove (-3900, -3787) a ;;
let a = remove (744, 792) a ;;
let a = remove (-2983, -2938) a ;;
let a = remove (-1401, -1239) a ;;
let a = remove (-3351, -3187) a ;;
let a = remove (-393, -195) a ;;
let a = remove (-3458, -3373) a ;;
let a = remove (-1233, -1214) a ;;
let a = remove (-2218, -2159) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (-4863, -4854) a ;;
let a = add (-4336, -4323) a ;;
let a = add (-850, -837) a ;;
let a = add (3450, 3463) a ;;
let a = add (495, 497) a ;;
let a = add (-4610, -4602) a ;;
let a = add (-3974, -3969) a ;;
let a = add (-1772, -1758) a ;;
let a = add (3009, 3010) a ;;
let a = add (4581, 4585) a ;;
let a = add (-4840, -4838) a ;;
let a = add (4107, 4107) a ;;
let a = add (2612, 2618) a ;;
let a = add (4430, 4444) a ;;
let a = add (1874, 1881) a ;;
let a = add (2523, 2534) a ;;
let a = add (2481, 2485) a ;;
let a = add (1066, 1068) a ;;
let a = add (4622, 4636) a ;;
let a = add (-843, -843) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("-1089 - ") ;;
 print_string (string_of_bool (mem (-1089) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3160 - ") ;;
 print_string (string_of_bool (mem (-3160) a) ) ;;
 print_string "\n" ;; 
 print_string ("4586 - ") ;;
 print_string (string_of_bool (mem (4586) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4257 - ") ;;
 print_string (string_of_bool (mem (-4257) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2634 - ") ;;
 print_string (string_of_bool (mem (-2634) a) ) ;;
 print_string "\n" ;; 
 print_string ("2981 - ") ;;
 print_string (string_of_bool (mem (2981) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4677 - ") ;;
 print_string (string_of_bool (mem (-4677) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4410 - ") ;;
 print_string (string_of_bool (mem (-4410) a) ) ;;
 print_string "\n" ;; 
 print_string ("3730 - ") ;;
 print_string (string_of_bool (mem (3730) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2302 - ") ;;
 print_string (string_of_bool (mem (-2302) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1228 - ") ;;
 print_string (string_of_bool (mem (-1228) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3629 - ") ;;
 print_string (string_of_bool (mem (-3629) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3636 - ") ;;
 print_string (string_of_bool (mem (-3636) a) ) ;;
 print_string "\n" ;; 
 print_string ("2631 - ") ;;
 print_string (string_of_bool (mem (2631) a) ) ;;
 print_string "\n" ;; 
 print_string ("446 - ") ;;
 print_string (string_of_bool (mem (446) a) ) ;;
 print_string "\n" ;; 
 print_string ("773 - ") ;;
 print_string (string_of_bool (mem (773) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3749 - ") ;;
 print_string (string_of_bool (mem (-3749) a) ) ;;
 print_string "\n" ;; 
 print_string ("2013 - ") ;;
 print_string (string_of_bool (mem (2013) a) ) ;;
 print_string "\n" ;; 
 print_string ("933 - ") ;;
 print_string (string_of_bool (mem (933) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3239 - ") ;;
 print_string (string_of_bool (mem (-3239) a) ) ;;
 print_string "\n" ;; 
 print_string ("4853 - ") ;;
 print_string (string_of_bool (mem (4853) a) ) ;;
 print_string "\n" ;; 
 print_string ("693 - ") ;;
 print_string (string_of_bool (mem (693) a) ) ;;
 print_string "\n" ;; 
 print_string ("2428 - ") ;;
 print_string (string_of_bool (mem (2428) a) ) ;;
 print_string "\n" ;; 
 print_string ("231 - ") ;;
 print_string (string_of_bool (mem (231) a) ) ;;
 print_string "\n" ;; 
 print_string ("464 - ") ;;
 print_string (string_of_bool (mem (464) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3722 - ") ;;
 print_string (string_of_bool (mem (-3722) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1465 - ") ;;
 print_string (string_of_bool (mem (-1465) a) ) ;;
 print_string "\n" ;; 
 print_string ("-970 - ") ;;
 print_string (string_of_bool (mem (-970) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1955 - ") ;;
 print_string (string_of_bool (mem (-1955) a) ) ;;
 print_string "\n" ;; 
 print_string ("-866 - ") ;;
 print_string (string_of_bool (mem (-866) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (-3223) a) ;
print_string "\n" ;;
print_int (below (289) a) ;
print_string "\n" ;;
print_int (below (3276) a) ;
print_string "\n" ;;
print_int (below (-1660) a) ;
print_string "\n" ;;
print_int (below (-1277) a) ;
print_string "\n" ;;
print_int (below (4128) a) ;
print_string "\n" ;;
print_int (below (-2472) a) ;
print_string "\n" ;;
print_int (below (3365) a) ;
print_string "\n" ;;
print_int (below (1277) a) ;
print_string "\n" ;;
print_int (below (2410) a) ;
print_string "\n" ;;
print_int (below (2482) a) ;
print_string "\n" ;;
print_int (below (-4787) a) ;
print_string "\n" ;;
print_int (below (-1188) a) ;
print_string "\n" ;;
print_int (below (-401) a) ;
print_string "\n" ;;
print_int (below (-2062) a) ;
print_string "\n" ;;
print_int (below (-1896) a) ;
print_string "\n" ;;
print_int (below (610) a) ;
print_string "\n" ;;
print_int (below (2257) a) ;
print_string "\n" ;;
print_int (below (840) a) ;
print_string "\n" ;;
print_int (below (-799) a) ;
print_string "\n" ;;
print_int (below (-1521) a) ;
print_string "\n" ;;
print_int (below (-4600) a) ;
print_string "\n" ;;
print_int (below (-1100) a) ;
print_string "\n" ;;
print_int (below (245) a) ;
print_string "\n" ;;
print_int (below (2913) a) ;
print_string "\n" ;;
print_int (below (472) a) ;
print_string "\n" ;;
print_int (below (-1492) a) ;
print_string "\n" ;;
print_int (below (695) a) ;
print_string "\n" ;;
print_int (below (3720) a) ;
print_string "\n" ;;
print_int (below (2175) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (67) a) ;
print_string "\n" ;;
print_int (below (-2419) a) ;
print_string "\n" ;;
print_int (below (3962) a) ;
print_string "\n" ;;
print_int (below (2267) a) ;
print_string "\n" ;;
print_int (below (1298) a) ;
print_string "\n" ;;
print_int (below (1920) a) ;
print_string "\n" ;;
print_int (below (4345) a) ;
print_string "\n" ;;
print_int (below (3165) a) ;
print_string "\n" ;;
print_int (below (-837) a) ;
print_string "\n" ;;
print_int (below (528) a) ;
print_string "\n" ;;
print_int (below (123) a) ;
print_string "\n" ;;
print_int (below (-498) a) ;
print_string "\n" ;;
print_int (below (3963) a) ;
print_string "\n" ;;
print_int (below (-2000) a) ;
print_string "\n" ;;
print_int (below (-4994) a) ;
print_string "\n" ;;
print_int (below (1169) a) ;
print_string "\n" ;;
print_int (below (951) a) ;
print_string "\n" ;;
print_int (below (-4795) a) ;
print_string "\n" ;;
print_int (below (-4616) a) ;
print_string "\n" ;;
print_int (below (-4716) a) ;
print_string "\n" ;;
print_int (below (2833) a) ;
print_string "\n" ;;
print_int (below (-1439) a) ;
print_string "\n" ;;
print_int (below (860) a) ;
print_string "\n" ;;
print_int (below (-329) a) ;
print_string "\n" ;;
print_int (below (-2071) a) ;
print_string "\n" ;;
print_int (below (447) a) ;
print_string "\n" ;;
print_int (below (4561) a) ;
print_string "\n" ;;
print_int (below (162) a) ;
print_string "\n" ;;
print_int (below (4844) a) ;
print_string "\n" ;;
print_int (below (263) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (4041, 4045) a ;;
let a = remove (4993, 4993) a ;;
let a = remove (1258, 1273) a ;;
let a = remove (-2326, -2278) a ;;
let a = remove (1666, 1845) a ;;
let a = remove (-2526, -2466) a ;;
let a = remove (575, 644) a ;;
let a = remove (-1023, -841) a ;;
let a = remove (-4673, -4615) a ;;
let a = remove (-4517, -4444) a ;;
let a = remove (707, 812) a ;;
let a = remove (-4664, -4635) a ;;
let a = remove (3416, 3586) a ;;
let a = remove (583, 712) a ;;
let a = remove (-583, -503) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (-2763, -2759) a ;;
let a = add (-2975, -2964) a ;;
let a = add (4045, 4048) a ;;
let a = add (-1027, -1023) a ;;
let a = add (4238, 4240) a ;;
let a = add (-2711, -2697) a ;;
let a = add (-3969, -3969) a ;;
let a = add (-2950, -2943) a ;;
let a = add (2920, 2926) a ;;
let a = add (202, 215) a ;;
let a = add (-1234, -1228) a ;;
let a = add (3325, 3325) a ;;
let a = add (-3546, -3532) a ;;
let a = add (-445, -434) a ;;
let a = add (-1886, -1879) a ;;
let a = add (2329, 2337) a ;;
let a = add (-4870, -4866) a ;;
let a = add (4502, 4514) a ;;
let a = add (2485, 2489) a ;;
let a = add (3848, 3856) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("3906 - ") ;;
 print_string (string_of_bool (mem (3906) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3447 - ") ;;
 print_string (string_of_bool (mem (-3447) a) ) ;;
 print_string "\n" ;; 
 print_string ("549 - ") ;;
 print_string (string_of_bool (mem (549) a) ) ;;
 print_string "\n" ;; 
 print_string ("2318 - ") ;;
 print_string (string_of_bool (mem (2318) a) ) ;;
 print_string "\n" ;; 
 print_string ("1825 - ") ;;
 print_string (string_of_bool (mem (1825) a) ) ;;
 print_string "\n" ;; 
 print_string ("893 - ") ;;
 print_string (string_of_bool (mem (893) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1476 - ") ;;
 print_string (string_of_bool (mem (-1476) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3245 - ") ;;
 print_string (string_of_bool (mem (-3245) a) ) ;;
 print_string "\n" ;; 
 print_string ("1460 - ") ;;
 print_string (string_of_bool (mem (1460) a) ) ;;
 print_string "\n" ;; 
 print_string ("1088 - ") ;;
 print_string (string_of_bool (mem (1088) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3703 - ") ;;
 print_string (string_of_bool (mem (-3703) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3537 - ") ;;
 print_string (string_of_bool (mem (-3537) a) ) ;;
 print_string "\n" ;; 
 print_string ("4667 - ") ;;
 print_string (string_of_bool (mem (4667) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4656 - ") ;;
 print_string (string_of_bool (mem (-4656) a) ) ;;
 print_string "\n" ;; 
 print_string ("1222 - ") ;;
 print_string (string_of_bool (mem (1222) a) ) ;;
 print_string "\n" ;; 
 print_string ("3512 - ") ;;
 print_string (string_of_bool (mem (3512) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2871 - ") ;;
 print_string (string_of_bool (mem (-2871) a) ) ;;
 print_string "\n" ;; 
 print_string ("1665 - ") ;;
 print_string (string_of_bool (mem (1665) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3925 - ") ;;
 print_string (string_of_bool (mem (-3925) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3868 - ") ;;
 print_string (string_of_bool (mem (-3868) a) ) ;;
 print_string "\n" ;; 
 print_string ("-310 - ") ;;
 print_string (string_of_bool (mem (-310) a) ) ;;
 print_string "\n" ;; 
 print_string ("1167 - ") ;;
 print_string (string_of_bool (mem (1167) a) ) ;;
 print_string "\n" ;; 
 print_string ("-245 - ") ;;
 print_string (string_of_bool (mem (-245) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2181 - ") ;;
 print_string (string_of_bool (mem (-2181) a) ) ;;
 print_string "\n" ;; 
 print_string ("903 - ") ;;
 print_string (string_of_bool (mem (903) a) ) ;;
 print_string "\n" ;; 
 print_string ("740 - ") ;;
 print_string (string_of_bool (mem (740) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3249 - ") ;;
 print_string (string_of_bool (mem (-3249) a) ) ;;
 print_string "\n" ;; 
 print_string ("1178 - ") ;;
 print_string (string_of_bool (mem (1178) a) ) ;;
 print_string "\n" ;; 
 print_string ("1651 - ") ;;
 print_string (string_of_bool (mem (1651) a) ) ;;
 print_string "\n" ;; 
 print_string ("-819 - ") ;;
 print_string (string_of_bool (mem (-819) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (-2832) a) ;
print_string "\n" ;;
print_int (below (-3001) a) ;
print_string "\n" ;;
print_int (below (3995) a) ;
print_string "\n" ;;
print_int (below (476) a) ;
print_string "\n" ;;
print_int (below (1354) a) ;
print_string "\n" ;;
print_int (below (23) a) ;
print_string "\n" ;;
print_int (below (-458) a) ;
print_string "\n" ;;
print_int (below (-4802) a) ;
print_string "\n" ;;
print_int (below (-1956) a) ;
print_string "\n" ;;
print_int (below (-112) a) ;
print_string "\n" ;;
print_int (below (4309) a) ;
print_string "\n" ;;
print_int (below (169) a) ;
print_string "\n" ;;
print_int (below (-1481) a) ;
print_string "\n" ;;
print_int (below (1826) a) ;
print_string "\n" ;;
print_int (below (3533) a) ;
print_string "\n" ;;
print_int (below (3709) a) ;
print_string "\n" ;;
print_int (below (4681) a) ;
print_string "\n" ;;
print_int (below (3421) a) ;
print_string "\n" ;;
print_int (below (-4081) a) ;
print_string "\n" ;;
print_int (below (-2949) a) ;
print_string "\n" ;;
print_int (below (4594) a) ;
print_string "\n" ;;
print_int (below (4803) a) ;
print_string "\n" ;;
print_int (below (-515) a) ;
print_string "\n" ;;
print_int (below (-3459) a) ;
print_string "\n" ;;
print_int (below (-4292) a) ;
print_string "\n" ;;
print_int (below (1682) a) ;
print_string "\n" ;;
print_int (below (776) a) ;
print_string "\n" ;;
print_int (below (-2512) a) ;
print_string "\n" ;;
print_int (below (-903) a) ;
print_string "\n" ;;
print_int (below (-3094) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (-4689) a) ;
print_string "\n" ;;
print_int (below (3507) a) ;
print_string "\n" ;;
print_int (below (4866) a) ;
print_string "\n" ;;
print_int (below (-4399) a) ;
print_string "\n" ;;
print_int (below (2178) a) ;
print_string "\n" ;;
print_int (below (2086) a) ;
print_string "\n" ;;
print_int (below (-3024) a) ;
print_string "\n" ;;
print_int (below (3176) a) ;
print_string "\n" ;;
print_int (below (-4198) a) ;
print_string "\n" ;;
print_int (below (2363) a) ;
print_string "\n" ;;
print_int (below (206) a) ;
print_string "\n" ;;
print_int (below (3444) a) ;
print_string "\n" ;;
print_int (below (-3602) a) ;
print_string "\n" ;;
print_int (below (-944) a) ;
print_string "\n" ;;
print_int (below (1648) a) ;
print_string "\n" ;;
print_int (below (-1646) a) ;
print_string "\n" ;;
print_int (below (-2193) a) ;
print_string "\n" ;;
print_int (below (-2059) a) ;
print_string "\n" ;;
print_int (below (3434) a) ;
print_string "\n" ;;
print_int (below (2358) a) ;
print_string "\n" ;;
print_int (below (1510) a) ;
print_string "\n" ;;
print_int (below (-2384) a) ;
print_string "\n" ;;
print_int (below (4037) a) ;
print_string "\n" ;;
print_int (below (-4427) a) ;
print_string "\n" ;;
print_int (below (4899) a) ;
print_string "\n" ;;
print_int (below (-1726) a) ;
print_string "\n" ;;
print_int (below (3540) a) ;
print_string "\n" ;;
print_int (below (3792) a) ;
print_string "\n" ;;
print_int (below (3831) a) ;
print_string "\n" ;;
print_int (below (-4352) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (126, 294) a ;;
let a = remove (2319, 2347) a ;;
let a = remove (731, 769) a ;;
let a = remove (3089, 3238) a ;;
let a = remove (3886, 3922) a ;;
let a = remove (4275, 4290) a ;;
let a = remove (-2511, -2354) a ;;
let a = remove (589, 639) a ;;
let a = remove (2111, 2207) a ;;
let a = remove (943, 943) a ;;
let a = remove (2774, 2925) a ;;
let a = remove (2295, 2350) a ;;
let a = remove (-3875, -3730) a ;;
let a = remove (3265, 3464) a ;;
let a = remove (4166, 4203) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (4602, 4606) a ;;
let a = add (-817, -804) a ;;
let a = add (1527, 1538) a ;;
let a = add (-777, -763) a ;;
let a = add (1225, 1227) a ;;
let a = add (-1026, -1019) a ;;
let a = add (3177, 3185) a ;;
let a = add (-4184, -4184) a ;;
let a = add (2481, 2484) a ;;
let a = add (-3680, -3667) a ;;
let a = add (-1517, -1512) a ;;
let a = add (-4256, -4253) a ;;
let a = add (1796, 1801) a ;;
let a = add (-594, -592) a ;;
let a = add (4443, 4446) a ;;
let a = add (783, 796) a ;;
let a = add (-3387, -3380) a ;;
let a = add (-4575, -4571) a ;;
let a = add (2782, 2795) a ;;
let a = add (4745, 4754) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("-703 - ") ;;
 print_string (string_of_bool (mem (-703) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2210 - ") ;;
 print_string (string_of_bool (mem (-2210) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1295 - ") ;;
 print_string (string_of_bool (mem (-1295) a) ) ;;
 print_string "\n" ;; 
 print_string ("-348 - ") ;;
 print_string (string_of_bool (mem (-348) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3755 - ") ;;
 print_string (string_of_bool (mem (-3755) a) ) ;;
 print_string "\n" ;; 
 print_string ("38 - ") ;;
 print_string (string_of_bool (mem (38) a) ) ;;
 print_string "\n" ;; 
 print_string ("-108 - ") ;;
 print_string (string_of_bool (mem (-108) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3662 - ") ;;
 print_string (string_of_bool (mem (-3662) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1616 - ") ;;
 print_string (string_of_bool (mem (-1616) a) ) ;;
 print_string "\n" ;; 
 print_string ("-621 - ") ;;
 print_string (string_of_bool (mem (-621) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2728 - ") ;;
 print_string (string_of_bool (mem (-2728) a) ) ;;
 print_string "\n" ;; 
 print_string ("930 - ") ;;
 print_string (string_of_bool (mem (930) a) ) ;;
 print_string "\n" ;; 
 print_string ("3674 - ") ;;
 print_string (string_of_bool (mem (3674) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3524 - ") ;;
 print_string (string_of_bool (mem (-3524) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3458 - ") ;;
 print_string (string_of_bool (mem (-3458) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1206 - ") ;;
 print_string (string_of_bool (mem (-1206) a) ) ;;
 print_string "\n" ;; 
 print_string ("4734 - ") ;;
 print_string (string_of_bool (mem (4734) a) ) ;;
 print_string "\n" ;; 
 print_string ("3149 - ") ;;
 print_string (string_of_bool (mem (3149) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1311 - ") ;;
 print_string (string_of_bool (mem (-1311) a) ) ;;
 print_string "\n" ;; 
 print_string ("473 - ") ;;
 print_string (string_of_bool (mem (473) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1985 - ") ;;
 print_string (string_of_bool (mem (-1985) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3162 - ") ;;
 print_string (string_of_bool (mem (-3162) a) ) ;;
 print_string "\n" ;; 
 print_string ("4049 - ") ;;
 print_string (string_of_bool (mem (4049) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1358 - ") ;;
 print_string (string_of_bool (mem (-1358) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3431 - ") ;;
 print_string (string_of_bool (mem (-3431) a) ) ;;
 print_string "\n" ;; 
 print_string ("3373 - ") ;;
 print_string (string_of_bool (mem (3373) a) ) ;;
 print_string "\n" ;; 
 print_string ("-2914 - ") ;;
 print_string (string_of_bool (mem (-2914) a) ) ;;
 print_string "\n" ;; 
 print_string ("1898 - ") ;;
 print_string (string_of_bool (mem (1898) a) ) ;;
 print_string "\n" ;; 
 print_string ("4368 - ") ;;
 print_string (string_of_bool (mem (4368) a) ) ;;
 print_string "\n" ;; 
 print_string ("4099 - ") ;;
 print_string (string_of_bool (mem (4099) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (-4469) a) ;
print_string "\n" ;;
print_int (below (4691) a) ;
print_string "\n" ;;
print_int (below (3721) a) ;
print_string "\n" ;;
print_int (below (234) a) ;
print_string "\n" ;;
print_int (below (-4042) a) ;
print_string "\n" ;;
print_int (below (-1450) a) ;
print_string "\n" ;;
print_int (below (3923) a) ;
print_string "\n" ;;
print_int (below (2176) a) ;
print_string "\n" ;;
print_int (below (493) a) ;
print_string "\n" ;;
print_int (below (4989) a) ;
print_string "\n" ;;
print_int (below (513) a) ;
print_string "\n" ;;
print_int (below (-2788) a) ;
print_string "\n" ;;
print_int (below (4018) a) ;
print_string "\n" ;;
print_int (below (1367) a) ;
print_string "\n" ;;
print_int (below (1461) a) ;
print_string "\n" ;;
print_int (below (3916) a) ;
print_string "\n" ;;
print_int (below (-772) a) ;
print_string "\n" ;;
print_int (below (-134) a) ;
print_string "\n" ;;
print_int (below (504) a) ;
print_string "\n" ;;
print_int (below (2230) a) ;
print_string "\n" ;;
print_int (below (132) a) ;
print_string "\n" ;;
print_int (below (-3277) a) ;
print_string "\n" ;;
print_int (below (-2349) a) ;
print_string "\n" ;;
print_int (below (4731) a) ;
print_string "\n" ;;
print_int (below (3987) a) ;
print_string "\n" ;;
print_int (below (3118) a) ;
print_string "\n" ;;
print_int (below (-787) a) ;
print_string "\n" ;;
print_int (below (-4279) a) ;
print_string "\n" ;;
print_int (below (593) a) ;
print_string "\n" ;;
print_int (below (895) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (-2464) a) ;
print_string "\n" ;;
print_int (below (4337) a) ;
print_string "\n" ;;
print_int (below (-1122) a) ;
print_string "\n" ;;
print_int (below (434) a) ;
print_string "\n" ;;
print_int (below (2544) a) ;
print_string "\n" ;;
print_int (below (2524) a) ;
print_string "\n" ;;
print_int (below (-4048) a) ;
print_string "\n" ;;
print_int (below (-4435) a) ;
print_string "\n" ;;
print_int (below (2606) a) ;
print_string "\n" ;;
print_int (below (-591) a) ;
print_string "\n" ;;
print_int (below (1590) a) ;
print_string "\n" ;;
print_int (below (-3797) a) ;
print_string "\n" ;;
print_int (below (969) a) ;
print_string "\n" ;;
print_int (below (3534) a) ;
print_string "\n" ;;
print_int (below (-1426) a) ;
print_string "\n" ;;
print_int (below (-4969) a) ;
print_string "\n" ;;
print_int (below (1944) a) ;
print_string "\n" ;;
print_int (below (-4831) a) ;
print_string "\n" ;;
print_int (below (-129) a) ;
print_string "\n" ;;
print_int (below (-1045) a) ;
print_string "\n" ;;
print_int (below (633) a) ;
print_string "\n" ;;
print_int (below (4405) a) ;
print_string "\n" ;;
print_int (below (723) a) ;
print_string "\n" ;;
print_int (below (3783) a) ;
print_string "\n" ;;
print_int (below (-710) a) ;
print_string "\n" ;;
print_int (below (-1275) a) ;
print_string "\n" ;;
print_int (below (-789) a) ;
print_string "\n" ;;
print_int (below (1030) a) ;
print_string "\n" ;;
print_int (below (-853) a) ;
print_string "\n" ;;
print_int (below (4672) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (-1698, -1623) a ;;
let a = remove (-3643, -3537) a ;;
let a = remove (-3062, -2986) a ;;
let a = remove (4107, 4168) a ;;
let a = remove (2677, 2772) a ;;
let a = remove (4753, 4784) a ;;
let a = remove (-4435, -4277) a ;;
let a = remove (2062, 2209) a ;;
let a = remove (3487, 3592) a ;;
let a = remove (-4341, -4212) a ;;
let a = remove (2973, 3144) a ;;
let a = remove (-1848, -1826) a ;;
let a = remove (-1906, -1751) a ;;
let a = remove (3582, 3696) a ;;
let a = remove (2244, 2322) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

let a = empty;;
 print_string("--ADD_TEST -- a ; 20 ; 5000 ; 15 --\n") ;;
let a = add (-3291, -3285) a ;;
let a = add (4474, 4474) a ;;
let a = add (32, 42) a ;;
let a = add (2731, 2734) a ;;
let a = add (-2188, -2184) a ;;
let a = add (1318, 1327) a ;;
let a = add (1441, 1450) a ;;
let a = add (3215, 3221) a ;;
let a = add (-1771, -1768) a ;;
let a = add (-2485, -2473) a ;;
let a = add (1115, 1116) a ;;
let a = add (-1501, -1498) a ;;
let a = add (-707, -693) a ;;
let a = add (-2384, -2381) a ;;
let a = add (-1212, -1204) a ;;
let a = add (-2164, -2161) a ;;
let a = add (585, 593) a ;;
let a = add (120, 130) a ;;
let a = add (-1533, -1532) a ;;
let a = add (2581, 2594) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("fold: ");;
print_int ( fold (fun x il -> print_pair x ; il+1 ) a 0) ;;
print_string("\n\n");;

print_string("iter: ");;
iter (fun x -> print_pair x) a;;
print_string("\n\n");;

print_string("--MEM_TEST -- a ; 30 ; 5000 -- \n") ;;
 print_string ("-3645 - ") ;;
 print_string (string_of_bool (mem (-3645) a) ) ;;
 print_string "\n" ;; 
 print_string ("3233 - ") ;;
 print_string (string_of_bool (mem (3233) a) ) ;;
 print_string "\n" ;; 
 print_string ("4382 - ") ;;
 print_string (string_of_bool (mem (4382) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1811 - ") ;;
 print_string (string_of_bool (mem (-1811) a) ) ;;
 print_string "\n" ;; 
 print_string ("-616 - ") ;;
 print_string (string_of_bool (mem (-616) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3826 - ") ;;
 print_string (string_of_bool (mem (-3826) a) ) ;;
 print_string "\n" ;; 
 print_string ("3764 - ") ;;
 print_string (string_of_bool (mem (3764) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4738 - ") ;;
 print_string (string_of_bool (mem (-4738) a) ) ;;
 print_string "\n" ;; 
 print_string ("3554 - ") ;;
 print_string (string_of_bool (mem (3554) a) ) ;;
 print_string "\n" ;; 
 print_string ("3433 - ") ;;
 print_string (string_of_bool (mem (3433) a) ) ;;
 print_string "\n" ;; 
 print_string ("2830 - ") ;;
 print_string (string_of_bool (mem (2830) a) ) ;;
 print_string "\n" ;; 
 print_string ("612 - ") ;;
 print_string (string_of_bool (mem (612) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3289 - ") ;;
 print_string (string_of_bool (mem (-3289) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1917 - ") ;;
 print_string (string_of_bool (mem (-1917) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1079 - ") ;;
 print_string (string_of_bool (mem (-1079) a) ) ;;
 print_string "\n" ;; 
 print_string ("2002 - ") ;;
 print_string (string_of_bool (mem (2002) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1564 - ") ;;
 print_string (string_of_bool (mem (-1564) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4203 - ") ;;
 print_string (string_of_bool (mem (-4203) a) ) ;;
 print_string "\n" ;; 
 print_string ("996 - ") ;;
 print_string (string_of_bool (mem (996) a) ) ;;
 print_string "\n" ;; 
 print_string ("3740 - ") ;;
 print_string (string_of_bool (mem (3740) a) ) ;;
 print_string "\n" ;; 
 print_string ("2777 - ") ;;
 print_string (string_of_bool (mem (2777) a) ) ;;
 print_string "\n" ;; 
 print_string ("3871 - ") ;;
 print_string (string_of_bool (mem (3871) a) ) ;;
 print_string "\n" ;; 
 print_string ("-309 - ") ;;
 print_string (string_of_bool (mem (-309) a) ) ;;
 print_string "\n" ;; 
 print_string ("-4107 - ") ;;
 print_string (string_of_bool (mem (-4107) a) ) ;;
 print_string "\n" ;; 
 print_string ("4849 - ") ;;
 print_string (string_of_bool (mem (4849) a) ) ;;
 print_string "\n" ;; 
 print_string ("707 - ") ;;
 print_string (string_of_bool (mem (707) a) ) ;;
 print_string "\n" ;; 
 print_string ("-1166 - ") ;;
 print_string (string_of_bool (mem (-1166) a) ) ;;
 print_string "\n" ;; 
 print_string ("-3020 - ") ;;
 print_string (string_of_bool (mem (-3020) a) ) ;;
 print_string "\n" ;; 
 print_string ("4817 - ") ;;
 print_string (string_of_bool (mem (4817) a) ) ;;
 print_string "\n" ;; 
 print_string ("1276 - ") ;;
 print_string (string_of_bool (mem (1276) a) ) ;;
 print_string "\n" ;; 
print_string("--DONE--\n\n\n");; 

print_string("--BELOW_TEST -- a ; 30 ; 5000 -- \n") ;;
print_int (below (4973) a) ;
print_string "\n" ;;
print_int (below (3324) a) ;
print_string "\n" ;;
print_int (below (-4866) a) ;
print_string "\n" ;;
print_int (below (189) a) ;
print_string "\n" ;;
print_int (below (-1246) a) ;
print_string "\n" ;;
print_int (below (-3826) a) ;
print_string "\n" ;;
print_int (below (-4200) a) ;
print_string "\n" ;;
print_int (below (-1917) a) ;
print_string "\n" ;;
print_int (below (2658) a) ;
print_string "\n" ;;
print_int (below (2428) a) ;
print_string "\n" ;;
print_int (below (4917) a) ;
print_string "\n" ;;
print_int (below (-2892) a) ;
print_string "\n" ;;
print_int (below (807) a) ;
print_string "\n" ;;
print_int (below (3243) a) ;
print_string "\n" ;;
print_int (below (-2202) a) ;
print_string "\n" ;;
print_int (below (4224) a) ;
print_string "\n" ;;
print_int (below (-4150) a) ;
print_string "\n" ;;
print_int (below (1418) a) ;
print_string "\n" ;;
print_int (below (-4132) a) ;
print_string "\n" ;;
print_int (below (1230) a) ;
print_string "\n" ;;
print_int (below (3240) a) ;
print_string "\n" ;;
print_int (below (754) a) ;
print_string "\n" ;;
print_int (below (-2753) a) ;
print_string "\n" ;;
print_int (below (-4653) a) ;
print_string "\n" ;;
print_int (below (48) a) ;
print_string "\n" ;;
print_int (below (-623) a) ;
print_string "\n" ;;
print_int (below (-1570) a) ;
print_string "\n" ;;
print_int (below (-3752) a) ;
print_string "\n" ;;
print_int (below (-780) a) ;
print_string "\n" ;;
print_int (below (4354) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 

print_string("--SPLIT_TEST -- a ; 30 ; 5000 -- \n") ;;print_int (below (4219) a) ;
print_string "\n" ;;
print_int (below (-1510) a) ;
print_string "\n" ;;
print_int (below (3831) a) ;
print_string "\n" ;;
print_int (below (2385) a) ;
print_string "\n" ;;
print_int (below (-887) a) ;
print_string "\n" ;;
print_int (below (4694) a) ;
print_string "\n" ;;
print_int (below (23) a) ;
print_string "\n" ;;
print_int (below (2920) a) ;
print_string "\n" ;;
print_int (below (4472) a) ;
print_string "\n" ;;
print_int (below (891) a) ;
print_string "\n" ;;
print_int (below (-2360) a) ;
print_string "\n" ;;
print_int (below (837) a) ;
print_string "\n" ;;
print_int (below (-2734) a) ;
print_string "\n" ;;
print_int (below (1307) a) ;
print_string "\n" ;;
print_int (below (-4289) a) ;
print_string "\n" ;;
print_int (below (2849) a) ;
print_string "\n" ;;
print_int (below (-592) a) ;
print_string "\n" ;;
print_int (below (-1877) a) ;
print_string "\n" ;;
print_int (below (3640) a) ;
print_string "\n" ;;
print_int (below (-91) a) ;
print_string "\n" ;;
print_int (below (581) a) ;
print_string "\n" ;;
print_int (below (1359) a) ;
print_string "\n" ;;
print_int (below (2938) a) ;
print_string "\n" ;;
print_int (below (4732) a) ;
print_string "\n" ;;
print_int (below (-4558) a) ;
print_string "\n" ;;
print_int (below (3282) a) ;
print_string "\n" ;;
print_int (below (-4842) a) ;
print_string "\n" ;;
print_int (below (-2200) a) ;
print_string "\n" ;;
print_int (below (-61) a) ;
print_string "\n" ;;
print_int (below (2443) a) ;
print_string "\n" ;;
print_string("--DONE--\n\n\n");;print_string("--REMOVE_TEST -- a ; 15 ; 5000 ; 200 -- \n") ;;
let a = remove (521, 531) a ;;
let a = remove (2465, 2504) a ;;
let a = remove (4592, 4645) a ;;
let a = remove (-4684, -4498) a ;;
let a = remove (-822, -680) a ;;
let a = remove (-3760, -3686) a ;;
let a = remove (-2523, -2522) a ;;
let a = remove (-805, -761) a ;;
let a = remove (-1277, -1104) a ;;
let a = remove (2690, 2858) a ;;
let a = remove (-3392, -3379) a ;;
let a = remove (3954, 4075) a ;;
let a = remove (-1393, -1324) a ;;
let a = remove (-798, -702) a ;;
let a = remove (-784, -749) a ;;
print_string ("-- elem\n") ;;
List.fold_left (fun x y -> print_pair y) () (elements a);;
print_string "\n" ;;
print_string("--DONE--\n\n\n");; 


*)
