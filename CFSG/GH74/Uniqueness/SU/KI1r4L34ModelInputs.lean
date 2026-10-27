
module

public import CFSG.GH74.KGroups.L34TablesBase
public meta import CFSG.GH74.KGroups.L34AutBase
public meta import CFSG.GH74.KGroups.L34Base
public meta import CFSG.GH74.KGroups.Checks

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L34M

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34
@[expose] def s0gens : List (Equiv.Perm (Fin 42)) := [
    tab (List.formPerm [1, 16] * List.formPerm [2, 15] * List.formPerm [3, 14]
      * List.formPerm [4, 13] * List.formPerm [5, 10] * List.formPerm [6, 11]
      * List.formPerm [7, 9] * List.formPerm [8, 12] * List.formPerm [21, 37]
      * List.formPerm [22, 30] * List.formPerm [24, 40] * List.formPerm [25, 27]
      * List.formPerm [26, 38] * List.formPerm [29, 31] * List.formPerm [32, 41]
      * List.formPerm [35, 36]),
    tab (List.formPerm [0, 6, 19, 13] * List.formPerm [1, 12] * List.formPerm [2, 3, 15, 7]
      * List.formPerm [4, 17, 11, 18] * List.formPerm [5, 9, 10, 14] * List.formPerm [8, 16]
      * List.formPerm [21, 30, 27, 24] * List.formPerm [22, 31, 40, 38] * List.formPerm [23, 33]
      * List.formPerm [25, 32, 37, 36] * List.formPerm [26, 35, 29, 41] * List.formPerm [34, 39]),
    tab (List.formPerm [0, 2, 18, 10] * List.formPerm [1, 12] * List.formPerm [3, 13, 14, 11]
      * List.formPerm [4, 7, 6, 9] * List.formPerm [5, 19, 15, 17] * List.formPerm [8, 16]
      * List.formPerm [21, 24, 29, 35] * List.formPerm [22, 31, 32, 37] * List.formPerm [23, 34]
      * List.formPerm [25, 40, 38, 36] * List.formPerm [26, 41, 27, 30] * List.formPerm [33, 39]),
    tab (List.formPerm [0, 17] * List.formPerm [1, 12] * List.formPerm [2, 15]
      * List.formPerm [4, 6] * List.formPerm [5, 10] * List.formPerm [8, 16]
      * List.formPerm [11, 13] * List.formPerm [18, 19] * List.formPerm [21, 30]
      * List.formPerm [22, 37] * List.formPerm [24, 27] * List.formPerm [25, 40]
      * List.formPerm [26, 35] * List.formPerm [29, 41] * List.formPerm [31, 32]
      * List.formPerm [36, 38])
]

@[expose] def bfsClosure (gens : List (Equiv.Perm (Fin 42))) :
    ℕ → List (Equiv.Perm (Fin 42)) → List (Equiv.Perm (Fin 42)) →
      List (Equiv.Perm (Fin 42))
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | n + 1, seen, g :: rest =>
    let new := gens.foldl (fun acc s =>
      let h := tab (g * s)
      if h ∈ seen ∨ h ∈ acc then acc else acc ++ [h]) []
    bfsClosure gens n (seen ++ new) (rest ++ new)

@[expose] def s0list : List (Equiv.Perm (Fin 42)) := bfsClosure s0gens 200 [1] [1]

@[expose] def modelCheck (LA LP : List (Equiv.Perm (Fin 42))) : Bool :=
  LA.all fun g =>
    (!(s0list.all fun s => decide (g * s = s * g)) || decide (g ∈ s0list)) &&
      (!decide (g ^ 2 = 1) || QP.sift g 0 ||
        !(s0list.all fun s => decide (g * s * g⁻¹ ∈ s0list)) ||
        !decide (9 ∣ (LP.filter fun h => decide (h * g = g * h)).length) ||
        [PA, PB, sg0, sg1, sg2].all fun a => QP.sift (a * g * a⁻¹ * g⁻¹) 0)

@[expose] def y0 : Equiv.Perm (Fin 42) :=
  tab (List.formPerm [2, 3, 4] * List.formPerm [5, 14, 11] * List.formPerm [6, 15, 9]
    * List.formPerm [7, 13, 10] * List.formPerm [8, 16, 12] * List.formPerm [17, 18, 19]
    * List.formPerm [21, 27, 29] * List.formPerm [22, 38, 30] * List.formPerm [23, 33, 39]
    * List.formPerm [24, 36, 25] * List.formPerm [31, 35, 32] * List.formPerm [37, 41, 40])

end CFSG.GH74.Uniqueness.SU.K.R4.L34M
