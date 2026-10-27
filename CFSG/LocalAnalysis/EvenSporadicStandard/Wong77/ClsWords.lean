module

public import CFSG.Blueprint.NativeSporadic

public noncomputable section

namespace CFSG.EvenSporadicStandard.Wong77.Cls

open Equiv CFSG.Blueprint

@[expose] def tabFn (l : List (Fin 23)) (i : Fin 23) : Fin 23 := l.getD i.val 0

@[expose] def tabPerm (l : List (Fin 23)) (h : Function.Bijective (tabFn l)) : Perm (Fin 23) :=
  Equiv.ofBijective (tabFn l) h

@[expose] def pinA : Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

@[expose] def pinB : Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem pinA_mem : pinA ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem pinB_mem : pinB ∈ NativeSporadic.M23 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def gA : NativeSporadic.Carrier .M23 := ⟨pinA, pinA_mem⟩

@[expose] def gB : NativeSporadic.Carrier .M23 := ⟨pinB, pinB_mem⟩

@[expose] def toPerm : NativeSporadic.Carrier .M23 →* Perm (Fin 23) := NativeSporadic.M23.subtype

theorem toPerm_injective : Function.Injective toPerm := Subtype.val_injective

@[expose] def tabA : Perm (Fin 23) :=
  tabPerm [1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]
    (by decide)

@[expose] def tabB : Perm (Fin 23) :=
  tabPerm [15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]
    (by decide)

@[expose] def pc : Perm (Fin 23) :=
  tabPerm [14, 9, 1, 4, 6, 20, 7, 22, 21, 8, 3, 0, 18, 17, 16, 10, 15, 5, 19, 13, 11, 12, 2]
    (by decide)

@[expose] def ph : Perm (Fin 23) :=
  tabPerm [20, 8, 5, 22, 16, 17, 13, 1, 11, 4, 18, 3, 7, 2, 21, 0, 6, 15, 14, 19, 9, 12, 10]
    (by decide)

@[expose] def pt : Perm (Fin 23) :=
  tabPerm [22, 1, 4, 3, 19, 18, 16, 17, 8, 6, 21, 9, 2, 15, 20, 7, 11, 13, 10, 12, 14, 5, 0]
    (by decide)

theorem toPerm_gA : toPerm gA = tabA := by
  show pinA = tabA
  decide

theorem toPerm_gB : toPerm gB = tabB := by
  show pinB = tabB
  decide

@[expose] def gBi : NativeSporadic.Carrier .M23 := gB ^ 3

theorem toPerm_gBi : toPerm gBi = tabB ^ 3 := by
  simp only [gBi, map_pow, toPerm_gB]

@[expose] def cE : NativeSporadic.Carrier .M23 := gA * gB

@[expose] def hE : NativeSporadic.Carrier .M23 :=
  gA * gBi * gA * gB * gB * gA * gB * gA * gB * gA * gB * gB * gA * gB * gA * gB * gB * gA * gBi *
    gA * gB * gA * gBi * gA * gBi

@[expose] def tE : NativeSporadic.Carrier .M23 :=
  gBi * gA * gB * gA * gBi * gA * gBi * gA * gB * gA * gB * gA * gB * gA * gB * gB * gA * gBi *
    gA * gB * gB

theorem toPerm_cE : toPerm cE = pc := by
  simp only [cE, map_mul, toPerm_gA, toPerm_gB]
  decide

set_option maxRecDepth 100000 in
theorem toPerm_hE : toPerm hE = ph := by
  simp only [hE, map_mul, toPerm_gA, toPerm_gB, toPerm_gBi]
  decide

set_option maxRecDepth 100000 in
theorem toPerm_tE : toPerm tE = pt := by
  simp only [tE, map_mul, toPerm_gA, toPerm_gB, toPerm_gBi]
  decide

theorem cE_pow : cE ^ 23 = 1 := by
  apply toPerm_injective
  simp only [map_pow, toPerm_cE, map_one]
  decide

theorem cE_ne_one : cE ≠ 1 := by
  intro h
  have := congrArg toPerm h
  simp only [toPerm_cE, map_one] at this
  revert this
  decide

theorem hE_pow : hE ^ 11 = 1 := by
  apply toPerm_injective
  simp only [map_pow, toPerm_hE, map_one]
  decide

theorem hE_cE : hE * cE = cE ^ 16 * hE := by
  apply toPerm_injective
  simp only [map_mul, map_pow, toPerm_hE, toPerm_cE]
  decide

theorem tE_pow : tE ^ 4 = 1 := by
  apply toPerm_injective
  simp only [map_pow, toPerm_tE, map_one]
  decide

theorem hE_tE : hE * tE = tE * (cE ^ 9 * hE ^ 5) := by
  apply toPerm_injective
  simp only [map_mul, map_pow, toPerm_hE, toPerm_tE, toPerm_cE]
  decide

set_option maxRecDepth 100000 in
theorem gA_word :
    gA = tE ^ 3 * cE * tE * cE ^ 21 * hE * tE ^ 3 * cE ^ 22 * tE ^ 3 * hE * tE ^ 3 := by
  apply toPerm_injective
  simp only [map_mul, map_pow, toPerm_hE, toPerm_tE, toPerm_cE, toPerm_gA]
  decide

theorem gB_eq : gB = gA * cE := by
  apply toPerm_injective
  simp only [map_mul, toPerm_gA, toPerm_gB, toPerm_cE]
  decide

theorem closure_gA_gB : Subgroup.closure ({gA, gB} : Set (NativeSporadic.Carrier .M23)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  | one => exact Subgroup.one_mem _
  | mul y z _ _ hy hz => exact Subgroup.mul_mem _ hy hz
  | inv y _ hy => exact Subgroup.inv_mem _ hy

end CFSG.EvenSporadicStandard.Wong77.Cls
