module

public import CFSG.LieType.Chevalley.C2E6MinusSixDefs
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Span

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem add_self_zmod_two (a : M) : a + a = 0 := by
  rw [← two_smul (ZMod 2) a, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem mem_span_singleton_zmod_two {a x : M} : x ∈ (ZMod 2) ∙ a ↔ x = 0 ∨ x = a := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem mem_span_pair_zmod_two {a b x : M} :
    x ∈ Submodule.span (ZMod 2) {a, b} ↔ x = 0 ∨ x = a ∨ x = b ∨ x = a + b := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨c, d, rfl⟩
    rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one d with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem linearIndependent_pair_zmod_two {a b : M} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    LinearIndependent (ZMod 2) ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at hst
    exact absurd hst hb
  · simp only [zero_smul, one_smul, add_zero] at hst
    exact absurd hst ha
  · simp only [one_smul] at hst
    refine absurd ?_ hab
    rw [← add_right_cancel_iff (a := b), hst, add_self_zmod_two]

theorem finrank_span_pair_zmod_two {a b : M} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {a, b}) = 2 := by
  have h := finrank_span_eq_card (linearIndependent_pair_zmod_two ha hb hab)
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at h

theorem eq_span_pair_of_finrank_eq_two [FiniteDimensional (ZMod 2) M] {U : Submodule (ZMod 2) M}
    (hU : finrank (ZMod 2) U = 2) {a b : M} (ha : a ∈ U) (hb : b ∈ U) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hab : a ≠ b) : U = Submodule.span (ZMod 2) {a, b} := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨ha, hb⟩
  · rw [finrank_span_pair_zmod_two ha0 hb0 hab, hU]

theorem exists_pair_of_finrank_eq_two {U : Submodule (ZMod 2) M}
    (hU : finrank (ZMod 2) U = 2) : ∃ a ∈ U, ∃ b ∈ U, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  have hne : U ≠ ⊥ := by
    rintro rfl
    simp at hU
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : (ZMod 2) ∙ a < U := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem a U).mpr ha) fun h => ?_
    have := finrank_span_singleton (K := ZMod 2) ha0
    rw [h, hU] at this
    exact absurd this (by norm_num)
  obtain ⟨b, hb, hba⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨a, ha, b, hb, ha0, fun h => hba (h ▸ Submodule.zero_mem _), fun h => hba ?_⟩
  rw [← h]
  exact Submodule.mem_span_singleton_self a

end Span

@[expose] def ptVec : Fin 27 → X :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
    ![1, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0],
    ![1, 1, 1, 1, 0, 0], ![1, 0, 1, 0, 1, 0], ![1, 1, 1, 0, 1, 0], ![0, 1, 0, 1, 1, 0],
    ![1, 1, 0, 1, 1, 0], ![1, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1], ![0, 1, 0, 1, 0, 1], ![1, 1, 0, 1, 0, 1], ![1, 0, 1, 1, 0, 1],
    ![0, 1, 1, 1, 0, 1], ![1, 0, 1, 0, 1, 1], ![1, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1],
    ![1, 1, 0, 1, 1, 1], ![1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1]]

@[expose] def lnA : Fin 45 → Fin 27 :=
  ![0, 2, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3,
    3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 7,
    8, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14]

@[expose] def lnB : Fin 45 → Fin 27 :=
  ![1, 3, 3, 11, 17, 23, 2, 9, 15, 21, 11, 17, 23, 9, 15,
    21, 7, 13, 19, 25, 6, 12, 18, 24, 10, 16, 22, 10, 16, 22,
    9, 15, 21, 18, 20, 17, 19, 16, 19, 15, 20, 16, 17, 15, 18]

@[expose] def lnC : Fin 45 → Fin 27 :=
  ![4, 7, 6, 12, 18, 24, 5, 10, 16, 22, 14, 20, 26, 13, 19,
    25, 8, 14, 20, 26, 8, 13, 19, 25, 14, 20, 26, 12, 18, 24,
    11, 17, 23, 26, 24, 25, 23, 25, 22, 26, 21, 23, 22, 24, 21]

@[expose] def PtOn (i : Fin 27) (j : Fin 45) : Prop :=
  i = lnA j ∨ i = lnB j ∨ i = lnC j

instance : DecidableRel PtOn := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem ptVec_ne_zero : ∀ i, ptVec i ≠ 0 := by decide

theorem Q_ptVec : ∀ i, Q (ptVec i) = 0 := by decide

theorem ptVec_injective : Function.Injective ptVec := by
  intro i j h
  revert i j
  decide

theorem eta_X (v : X) : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
  funext i
  fin_cases i <;> rfl

theorem exists_ptVec_eq_aux : ∀ a b c d e f : ZMod 2, ![a, b, c, d, e, f] ≠ 0 →
    Q ![a, b, c, d, e, f] = 0 → ∃ i, ptVec i = ![a, b, c, d, e, f] := by decide

theorem exists_ptVec_eq {v : X} (hv : v ≠ 0) (hQ : Q v = 0) : ∃ i, ptVec i = v := by
  rw [eta_X v] at hv hQ ⊢
  exact exists_ptVec_eq_aux _ _ _ _ _ _ hv hQ

theorem ptVec_lnC : ∀ j, ptVec (lnC j) = ptVec (lnA j) + ptVec (lnB j) := by decide

theorem lnA_ne_lnB : ∀ j, lnA j ≠ lnB j := by decide

theorem exists_ptOn_aux : ∀ a b : Fin 27, a ≠ b → Q (ptVec a + ptVec b) = 0 →
    ∃ j, PtOn a j ∧ PtOn b j := by decide

theorem eq_of_forall_ptOn_iff : ∀ j j' : Fin 45, (∀ i, PtOn i j ↔ PtOn i j') → j = j' := by
  decide

@[expose] def ptSub (i : Fin 27) : Submodule (ZMod 2) X :=
  (ZMod 2) ∙ ptVec i

@[expose] def lnSub (j : Fin 45) : Submodule (ZMod 2) X :=
  Submodule.span (ZMod 2) {ptVec (lnA j), ptVec (lnB j)}

theorem mem_ptSub {i : Fin 27} {x : X} : x ∈ ptSub i ↔ x = 0 ∨ x = ptVec i :=
  mem_span_singleton_zmod_two

theorem mem_lnSub {j : Fin 45} {x : X} :
    x ∈ lnSub j ↔ x = 0 ∨ x = ptVec (lnA j) ∨ x = ptVec (lnB j) ∨ x = ptVec (lnC j) := by
  rw [lnSub, mem_span_pair_zmod_two, ptVec_lnC]

theorem finrank_ptSub (i : Fin 27) : finrank (ZMod 2) (ptSub i) = 1 :=
  finrank_span_singleton (ptVec_ne_zero i)

theorem finrank_lnSub (j : Fin 45) : finrank (ZMod 2) (lnSub j) = 2 :=
  finrank_span_pair_zmod_two (ptVec_ne_zero _) (ptVec_ne_zero _)
    (fun h => lnA_ne_lnB j (ptVec_injective h))

theorem isTotallySingular_ptSub (i : Fin 27) : IsTotallySingular (ptSub i) := by
  intro x hx
  rcases mem_ptSub.mp hx with rfl | rfl
  · exact QuadraticMap.map_zero Q
  · exact Q_ptVec i

theorem isTotallySingular_lnSub (j : Fin 45) : IsTotallySingular (lnSub j) := by
  intro x hx
  rcases mem_lnSub.mp hx with rfl | rfl | rfl | rfl
  · exact QuadraticMap.map_zero Q
  all_goals exact Q_ptVec _

theorem ptVec_mem_lnSub_iff {i : Fin 27} {j : Fin 45} : ptVec i ∈ lnSub j ↔ PtOn i j := by
  rw [mem_lnSub]
  constructor
  · rintro (h | h | h | h)
    · exact absurd h (ptVec_ne_zero i)
    · exact Or.inl (ptVec_injective h)
    · exact Or.inr (Or.inl (ptVec_injective h))
    · exact Or.inr (Or.inr (ptVec_injective h))
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem ptSub_le_lnSub_iff {i : Fin 27} {j : Fin 45} : ptSub i ≤ lnSub j ↔ PtOn i j := by
  rw [ptSub, Submodule.span_singleton_le_iff_mem, ptVec_mem_lnSub_iff]

theorem ptSub_injective : Function.Injective ptSub := by
  intro i i' h
  have : ptVec i ∈ ptSub i' := h ▸ Submodule.mem_span_singleton_self _
  rcases mem_ptSub.mp this with h0 | h1
  · exact absurd h0 (ptVec_ne_zero i)
  · exact ptVec_injective h1

theorem lnSub_injective : Function.Injective lnSub := by
  intro j j' h
  refine eq_of_forall_ptOn_iff j j' fun i => ?_
  rw [← ptSub_le_lnSub_iff, ← ptSub_le_lnSub_iff, h]

theorem span_ptVec_eq_lnSub {i i' : Fin 27} {j : Fin 45} (hi : PtOn i j) (hi' : PtOn i' j)
    (h : i ≠ i') : Submodule.span (ZMod 2) {ptVec i, ptVec i'} = lnSub j :=
  (eq_span_pair_of_finrank_eq_two (finrank_lnSub j) (ptVec_mem_lnSub_iff.mpr hi)
    (ptVec_mem_lnSub_iff.mpr hi') (ptVec_ne_zero i) (ptVec_ne_zero i')
    fun h' => h (ptVec_injective h')).symm

theorem exists_ptSub_eq {U : Submodule (ZMod 2) X} (hU : IsTotallySingular U)
    (h1 : finrank (ZMod 2) U = 1) : ∃ i, U = ptSub i := by
  have hne : U ≠ ⊥ := by
    rintro rfl
    simp at h1
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨i, rfl⟩ := exists_ptVec_eq hv0 (hU v hv)
  exact ⟨i, eq_span_singleton_of_mem_of_finrank_eq_one h1 hv hv0⟩

theorem exists_lnSub_eq {U : Submodule (ZMod 2) X} (hU : IsTotallySingular U)
    (h2 : finrank (ZMod 2) U = 2) : ∃ j, U = lnSub j := by
  obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := exists_pair_of_finrank_eq_two h2
  obtain ⟨i, rfl⟩ := exists_ptVec_eq ha0 (hU a ha)
  obtain ⟨i', rfl⟩ := exists_ptVec_eq hb0 (hU b hb)
  have hii' : i ≠ i' := fun h => hab (h ▸ rfl)
  obtain ⟨j, hj, hj'⟩ := exists_ptOn_aux i i' hii' (hU _ (U.add_mem ha hb))
  exact ⟨j, (eq_span_pair_of_finrank_eq_two h2 ha hb ha0 hb0 hab).trans
    (span_ptVec_eq_lnSub hj hj' hii')⟩

end CFSG.LieType.Chevalley.C2E6Overlap
