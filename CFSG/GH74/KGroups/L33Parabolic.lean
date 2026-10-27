module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.L33Inputs
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.L33Inputs

public section

namespace CFSG.GH74.KGroups.L33

open CFSG.Certificates CFSG.Sporadic.Schreier

@[expose] def parabolicS0List : List (Equiv.Perm (Fin 26)) :=
  [1,
   List.formPerm [1, 2] * List.formPerm [3, 5] * List.formPerm [6, 7] *
     List.formPerm [9, 11] * List.formPerm [14, 21] * List.formPerm [15, 17] *
     List.formPerm [18, 20] * List.formPerm [23, 25],
   List.formPerm [0, 1, 4, 3] * List.formPerm [2, 7, 5, 6] *
     List.formPerm [9, 12] * List.formPerm [10, 11] * List.formPerm [14, 16] *
     List.formPerm [15, 19, 25, 22] * List.formPerm [17, 20, 23, 18] *
     List.formPerm [21, 24],
   List.formPerm [0, 1, 7, 2, 4, 3, 6, 5] * List.formPerm [9, 10, 11, 12] *
     List.formPerm [14, 24, 21, 16] *
     List.formPerm [15, 20, 17, 19, 25, 18, 23, 22],
   List.formPerm [0, 2, 6, 1, 4, 5, 7, 3] * List.formPerm [9, 12, 11, 10] *
     List.formPerm [14, 16, 21, 24] *
     List.formPerm [15, 19, 23, 20, 25, 22, 17, 18],
   List.formPerm [0, 2, 4, 5] * List.formPerm [1, 6, 3, 7] *
     List.formPerm [9, 10] * List.formPerm [11, 12] * List.formPerm [14, 24] *
     List.formPerm [15, 18, 25, 20] * List.formPerm [16, 21] *
     List.formPerm [17, 19, 23, 22],
   List.formPerm [0, 3, 4, 1] * List.formPerm [2, 6, 5, 7] *
     List.formPerm [9, 12] * List.formPerm [10, 11] *
     List.formPerm [14, 16] * List.formPerm [15, 22, 25, 19] *
     List.formPerm [17, 18, 23, 20] * List.formPerm [21, 24],
   List.formPerm [0, 3, 7, 5, 4, 1, 6, 2] * List.formPerm [9, 10, 11, 12] *
     List.formPerm [14, 24, 21, 16] *
     List.formPerm [15, 18, 17, 22, 25, 20, 23, 19],
   List.formPerm [0, 4] * List.formPerm [1, 3] * List.formPerm [2, 5] *
     List.formPerm [6, 7] * List.formPerm [15, 25] * List.formPerm [17, 23] *
     List.formPerm [18, 20] * List.formPerm [19, 22],
   List.formPerm [0, 4] * List.formPerm [1, 5] * List.formPerm [2, 3] *
     List.formPerm [9, 11] * List.formPerm [14, 21] * List.formPerm [15, 23] *
     List.formPerm [17, 25] * List.formPerm [19, 22],
   List.formPerm [0, 5, 6, 3, 4, 2, 7, 1] * List.formPerm [9, 12, 11, 10] *
     List.formPerm [14, 16, 21, 24] *
     List.formPerm [15, 22, 23, 18, 25, 19, 17, 20],
   List.formPerm [0, 5, 4, 2] * List.formPerm [1, 7, 3, 6] *
     List.formPerm [9, 10] * List.formPerm [11, 12] * List.formPerm [14, 24] *
     List.formPerm [15, 20, 25, 18] * List.formPerm [16, 21] *
     List.formPerm [17, 22, 23, 19],
   List.formPerm [0, 6] * List.formPerm [2, 5] * List.formPerm [4, 7] *
     List.formPerm [10, 12] * List.formPerm [16, 24] * List.formPerm [17, 23] *
     List.formPerm [18, 22] * List.formPerm [19, 20],
   List.formPerm [0, 6, 4, 7] * List.formPerm [1, 5, 3, 2] *
     List.formPerm [9, 11] * List.formPerm [10, 12] * List.formPerm [14, 21] *
     List.formPerm [15, 23, 25, 17] * List.formPerm [16, 24] *
     List.formPerm [18, 19, 20, 22],
   List.formPerm [0, 7, 4, 6] * List.formPerm [1, 2, 3, 5] *
     List.formPerm [9, 11] * List.formPerm [10, 12] * List.formPerm [14, 21] *
     List.formPerm [15, 17, 25, 23] * List.formPerm [16, 24] *
     List.formPerm [18, 22, 20, 19],
   List.formPerm [0, 7] * List.formPerm [1, 3] * List.formPerm [4, 6] *
     List.formPerm [10, 12] * List.formPerm [15, 25] * List.formPerm [16, 24] *
     List.formPerm [18, 19] * List.formPerm [20, 22]]

@[expose] def parabolicU1a : Equiv.Perm (Fin 26) :=
  List.formPerm [1, 3, 11] * List.formPerm [2, 9, 5] * List.formPerm [6, 7, 12] *
    List.formPerm [13, 18, 20] * List.formPerm [15, 19, 17] * List.formPerm [22, 25, 23]

@[expose] def parabolicU1b : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 4, 10] * List.formPerm [2, 9, 5] * List.formPerm [6, 12, 7] *
    List.formPerm [13, 23, 17] * List.formPerm [15, 18, 22] * List.formPerm [19, 20, 25]

@[expose] def parabolicU2a : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5] * List.formPerm [6, 7, 8] *
    List.formPerm [14, 25, 15] * List.formPerm [17, 23, 21] * List.formPerm [18, 20, 24]

@[expose] def parabolicU2b : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 3, 6] * List.formPerm [1, 4, 7] * List.formPerm [2, 5, 8] *
    List.formPerm [16, 22, 19] * List.formPerm [17, 23, 21] * List.formPerm [18, 24, 20]

@[expose] def parabolicE1 : List (Equiv.Perm (Fin 26)) :=
  [List.formPerm [1, 11, 3] * List.formPerm [2, 5, 9] * List.formPerm [6, 12, 7] *
     List.formPerm [13, 20, 18] * List.formPerm [15, 17, 19] * List.formPerm [22, 23, 25],
   List.formPerm [0, 4, 10] * List.formPerm [2, 9, 5] * List.formPerm [6, 12, 7] *
     List.formPerm [13, 23, 17] * List.formPerm [15, 18, 22] * List.formPerm [19, 20, 25],
   List.formPerm [0, 4, 10] * List.formPerm [1, 3, 11] * List.formPerm [2, 5, 9] *
     List.formPerm [13, 22, 19] * List.formPerm [15, 20, 23] * List.formPerm [17, 18, 25],
   List.formPerm [0, 4, 10] * List.formPerm [1, 11, 3] * List.formPerm [6, 7, 12] *
     List.formPerm [13, 25, 15] * List.formPerm [17, 20, 22] * List.formPerm [18, 23, 19]]

@[expose] def parabolicW1 : List (Equiv.Perm (Fin 26)) :=
  [List.formPerm [0, 1, 4, 3] * List.formPerm [2, 7, 5, 6] * List.formPerm [9, 12] *
     List.formPerm [10, 11] * List.formPerm [14, 16] * List.formPerm [15, 19, 25, 22] *
     List.formPerm [17, 20, 23, 18] * List.formPerm [21, 24],
   List.formPerm [1, 2] * List.formPerm [3, 5] * List.formPerm [6, 7] *
     List.formPerm [9, 11] * List.formPerm [14, 21] * List.formPerm [15, 17] *
     List.formPerm [18, 20] * List.formPerm [23, 25],
   List.formPerm [0, 1, 4, 3] * List.formPerm [2, 7, 5, 6] * List.formPerm [9, 12] *
     List.formPerm [10, 11] * List.formPerm [14, 16] * List.formPerm [15, 19, 25, 22] *
     List.formPerm [17, 20, 23, 18] * List.formPerm [21, 24],
   List.formPerm [1, 2] * List.formPerm [3, 5] * List.formPerm [6, 7] *
     List.formPerm [9, 11] * List.formPerm [14, 21] * List.formPerm [15, 17] *
     List.formPerm [18, 20] * List.formPerm [23, 25]]

@[expose] def parabolicE2 : List (Equiv.Perm (Fin 26)) :=
  [List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5] * List.formPerm [6, 7, 8] *
     List.formPerm [14, 25, 15] * List.formPerm [17, 23, 21] * List.formPerm [18, 20, 24],
   List.formPerm [0, 3, 6] * List.formPerm [1, 4, 7] * List.formPerm [2, 5, 8] *
     List.formPerm [16, 22, 19] * List.formPerm [17, 23, 21] * List.formPerm [18, 24, 20],
   List.formPerm [0, 8, 4] * List.formPerm [1, 6, 5] * List.formPerm [2, 7, 3] *
     List.formPerm [14, 15, 25] * List.formPerm [16, 19, 22] * List.formPerm [17, 23, 21],
   List.formPerm [0, 5, 7] * List.formPerm [1, 3, 8] * List.formPerm [2, 4, 6] *
     List.formPerm [14, 15, 25] * List.formPerm [16, 22, 19] * List.formPerm [18, 20, 24]]

@[expose] def parabolicW2 : List (Equiv.Perm (Fin 26)) := parabolicW1

@[expose] def parabolicPairs1 : List (Equiv.Perm (Fin 26) × Equiv.Perm (Fin 26)) :=
  parabolicE1.zip parabolicW1

@[expose] def parabolicPairs2 : List (Equiv.Perm (Fin 26) × Equiv.Perm (Fin 26)) :=
  parabolicE2.zip parabolicW2

@[expose] def closedListCheck (L : List (Equiv.Perm (Fin 26))) : Bool :=
  decide (L.length = 16) && decide L.Nodup && decide (1 ∈ L) &&
    L.all (fun x => L.all (fun y => decide (x * y ∈ L))) &&
    L.all (fun x => decide (x⁻¹ ∈ L))

@[expose] def memGroupListCheck (Q : RawSchreierDatum 26) (L : List (Equiv.Perm (Fin 26))) : Bool :=
  L.all fun x => Q.sift x 0

@[expose] def e9ListCheck (Q : RawSchreierDatum 26) (a b : Equiv.Perm (Fin 26)) : Bool :=
  let L := pow3list a b
  decide L.Nodup && decide (L.length = 9) &&
    L.all (fun x => decide (x ^ 3 = 1)) &&
    L.all (fun x => L.all (fun y => decide (x * y = y * x))) &&
    L.all (fun x => L.all (fun y => decide (x * y ∈ L))) && memGroupListCheck Q L

@[expose] def normalizesListCheck (S L : List (Equiv.Perm (Fin 26))) : Bool :=
  S.all fun s => L.all fun x => decide (s * x * s⁻¹ ∈ L)

@[expose] def order3PairsCheck (S L : List (Equiv.Perm (Fin 26)))
    (W : List (Equiv.Perm (Fin 26) × Equiv.Perm (Fin 26))) : Bool :=
  let E := W.map Prod.fst
  decide (W.length = 4) &&
    W.all (fun p => decide (p.1 ≠ 1) && decide (p.1 ^ 3 = 1) && decide (p.1 ∈ L) &&
      decide (p.2 ∈ S) &&
      decide (p.1 * p.2 ∉ S.flatMap (fun t => [t, t * p.1, t * p.1 ^ 2]))) &&
    decide (E.flatMap (fun e => [e, e ^ 2])).Nodup &&
    decide ((E.flatMap (fun e => [e, e ^ 2])).length = 8) &&
    (L.filter (fun x => decide (x ≠ 1))).all
      (fun x => decide (x ∈ E.flatMap (fun e => [e, e ^ 2])))

@[expose] def parabolicQU (_ : Unit := ()) : RawSchreierDatum 26 :=
  certificate (by decide) [parabolicU1a, parabolicU1b, parabolicU2a, parabolicU2b]
    [[4, -2, 3, 1, 3, -4], [-1, -3, -1, 4], [1, 2, 4, -3, -1, -2],
      [2, 4, 1, -3, -4, -2], [-2, -3, -2], [-4, 1, 3]]
    #v[0, 1, 2, 3, 4] (by decide)

@[expose] def parabolicPairCheck (_ : Unit := ()) : Bool :=
  closedListCheck parabolicS0List && memGroupListCheck QP parabolicS0List &&
    e9ListCheck QP parabolicU1a parabolicU1b && e9ListCheck QP parabolicU2a parabolicU2b &&
    normalizesListCheck parabolicS0List (pow3list parabolicU1a parabolicU1b) &&
    normalizesListCheck parabolicS0List (pow3list parabolicU2a parabolicU2b) &&
    order3PairsCheck parabolicS0List (pow3list parabolicU1a parabolicU1b) parabolicPairs1 &&
    order3PairsCheck parabolicS0List (pow3list parabolicU2a parabolicU2b) parabolicPairs2 &&
    (parabolicQU ()).check && decide ((parabolicQU ()).orderCertificate = 5616)

@[expose] def l33ParabolicListSubgroup (L : List (Equiv.Perm (Fin 26))) (hnd : L.Nodup)
    (h1 : 1 ∈ L) (hmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) (hinv : ∀ x ∈ L, x⁻¹ ∈ L) :
    Subgroup (Equiv.Perm (Fin 26)) where
  carrier := {x | x ∈ L.toFinset}
  one_mem' := by simp [h1]
  mul_mem' := fun hx hy => by
    simp only [Set.mem_setOf_eq, List.mem_toFinset] at hx hy ⊢
    exact hmul _ hx _ hy
  inv_mem' := fun hx => by
    simp only [Set.mem_setOf_eq, List.mem_toFinset] at hx ⊢
    exact hinv _ hx

@[simp] theorem mem_l33ParabolicListSubgroup {L : List (Equiv.Perm (Fin 26))} {hnd h1 hmul hinv}
    {x : Equiv.Perm (Fin 26)} :
    x ∈ l33ParabolicListSubgroup L hnd h1 hmul hinv ↔ x ∈ L := by
  simp [l33ParabolicListSubgroup]

theorem card_l33ParabolicListSubgroup {L : List (Equiv.Perm (Fin 26))} {hnd h1 hmul hinv} :
    Nat.card (l33ParabolicListSubgroup L hnd h1 hmul hinv) = L.length := by
  let e : ↥(l33ParabolicListSubgroup L hnd h1 hmul hinv) ≃ L.toFinset :=
    { toFun := fun x => ⟨x.1, List.mem_toFinset.2 (mem_l33ParabolicListSubgroup.1 x.2)⟩
      invFun := fun x => ⟨x.1, mem_l33ParabolicListSubgroup.2 (List.mem_toFinset.1 x.2)⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

theorem mem_flatMap_mul_three {S : List (Equiv.Perm (Fin 26))} {e x : Equiv.Perm (Fin 26)} :
    x ∈ S.flatMap (fun t => [t, t * e, t * e ^ 2]) ↔
      ∃ t ∈ S, x = t ∨ x = t * e ∨ x = t * e ^ 2 := by
  simp [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_assoc]

theorem closedListCheck_sound {L : List (Equiv.Perm (Fin 26))} (h : closedListCheck L = true) :
    L.length = 16 ∧ L.Nodup ∧ 1 ∈ L ∧
      (∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) ∧ (∀ x ∈ L, x⁻¹ ∈ L) := by
  simp only [closedListCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    and_assoc] at h
  exact h

theorem memGroupListCheck_sound (Q : RawSchreierDatum 26) (hQ : ValidSchreier Q)
    {L : List (Equiv.Perm (Fin 26))} (h : memGroupListCheck Q L = true) :
    ∀ x ∈ L, x ∈ Q.originalSubgroup := by
  intro x hx
  exact (mem_iff_sift Q hQ x).2 (List.all_eq_true.1 h x hx)

theorem e9ListCheck_sound (Q : RawSchreierDatum 26) {a b : Equiv.Perm (Fin 26)}
    (h : e9ListCheck Q a b = true) :
    (pow3list a b).Nodup ∧ (pow3list a b).length = 9 ∧
      (∀ x ∈ pow3list a b, x ^ 3 = 1) ∧
      (∀ x ∈ pow3list a b, ∀ y ∈ pow3list a b, x * y = y * x) ∧
      (∀ x ∈ pow3list a b, ∀ y ∈ pow3list a b, x * y ∈ pow3list a b) ∧
      memGroupListCheck Q (pow3list a b) = true := by
  simp only [e9ListCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    and_assoc] at h
  exact h

theorem normalizesListCheck_sound {S L : List (Equiv.Perm (Fin 26))}
    (h : normalizesListCheck S L = true) :
    ∀ s ∈ S, ∀ x ∈ L, s * x * s⁻¹ ∈ L := by
  simpa [normalizesListCheck, List.all_eq_true, decide_eq_true_eq] using h

theorem order3PairsCheck_sound {S L : List (Equiv.Perm (Fin 26))}
    {W : List (Equiv.Perm (Fin 26) × Equiv.Perm (Fin 26))}
    (h : order3PairsCheck S L W = true) :
    W.length = 4 ∧
      (∀ p ∈ W, p.1 ≠ 1 ∧ p.1 ^ 3 = 1 ∧ p.1 ∈ L ∧ p.2 ∈ S ∧
        p.1 * p.2 ∉ S.flatMap (fun t => [t, t * p.1, t * p.1 ^ 2])) ∧
      ((W.map Prod.fst).flatMap (fun e => [e, e ^ 2])).Nodup ∧
      ((W.map Prod.fst).flatMap (fun e => [e, e ^ 2])).length = 8 ∧
      (∀ x, x ∈ L ∧ x ≠ 1 → x ∈ (W.map Prod.fst).flatMap (fun e => [e, e ^ 2])) := by
  simpa only [order3PairsCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_filter, and_assoc, List.length_map] using h

theorem parabolicQU_valid (h : (parabolicQU ()).check = true) : ValidSchreier (parabolicQU ()) := h

theorem parabolicQU_closure : (parabolicQU ()).originalSubgroup =
    Subgroup.closure ({parabolicU1a, parabolicU1b, parabolicU2a, parabolicU2b} :
      Set (Equiv.Perm (Fin 26))) := by
  simp only [parabolicQU]
  rw [certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem parabolicQU_card (hcheck : (parabolicQU ()).check = true)
    (hord : (parabolicQU ()).orderCertificate = 5616) :
    Nat.card (parabolicQU ()).originalSubgroup = 5616 := by
  rw [card_group (parabolicQU ()) (parabolicQU_valid hcheck), hord]

end CFSG.GH74.KGroups.L33
