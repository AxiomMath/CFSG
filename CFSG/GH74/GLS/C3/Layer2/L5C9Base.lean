
module

public import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs

@[expose] public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.HF

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5

theorem xor16_comm (a b : Fin 16) : xor16 a b = xor16 b a := Fin.ext (Nat.xor_comm _ _)

theorem xor16_assoc (a b c : Fin 16) : xor16 (xor16 a b) c = xor16 a (xor16 b c) :=
  Fin.ext (Nat.xor_assoc _ _ _)

theorem xor16_zero (a : Fin 16) : xor16 a 0 = a := Fin.ext (by simp [xor16])

theorem zero_xor16 (a : Fin 16) : xor16 0 a = a := by rw [xor16_comm, xor16_zero]

theorem xor16_self (a : Fin 16) : xor16 a a = 0 := Fin.ext (by simp [xor16])

theorem lin_zero {m : Perm (Fin 16)} (h : IsLin16 m) : m 0 = 0 := by
  have := h 0 0
  rw [xor16_self, xor16_self] at this
  exact this

theorem lin_eq {m : Perm (Fin 16)} (h : IsLin16 m) (i : Fin 16) :
    m i = linFun (m 1, m 2, m 4, m 8) i := by
  have h0 : m 0 = 0 := lin_zero h
  have h3 : m 3 = xor16 (m 1) (m 2) := h 1 2
  have h5 : m 5 = xor16 (m 1) (m 4) := h 1 4
  have h6 : m 6 = xor16 (m 2) (m 4) := h 2 4
  have h7 : m 7 = xor16 (m 3) (m 4) := h 3 4
  have h9 : m 9 = xor16 (m 1) (m 8) := h 1 8
  have h10 : m 10 = xor16 (m 2) (m 8) := h 2 8
  have h11 : m 11 = xor16 (m 3) (m 8) := h 3 8
  have h12 : m 12 = xor16 (m 4) (m 8) := h 4 8
  have h13 : m 13 = xor16 (m 5) (m 8) := h 5 8
  have h14 : m 14 = xor16 (m 6) (m 8) := h 6 8
  have h15 : m 15 = xor16 (m 7) (m 8) := h 7 8
  fin_cases i <;> simp [linFun, xor16_zero, zero_xor16, xor16_assoc, h0, h3, h5, h6, h7, h9, h10,
    h11, h12, h13, h14, h15]

theorem invTab_coe (m : Perm (Fin 16)) (j : Fin 16) : invTab (⇑m) j = m.symm j := by
  unfold invTab
  have hex : ((List.finRange 16).find? fun i => decide (m i = j)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨m.symm j, List.mem_finRange _, by simp⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hex
  rw [ha]
  have h1 := List.find?_some ha
  simp only [decide_eq_true_eq] at h1
  simp only [Option.getD_some]
  rw [← h1]
  simp

theorem isPermChk_coe (m : Perm (Fin 16)) : isPermChk (⇑m) = true := by
  simp only [isPermChk, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    decide_eq_true_eq, true_implies, invTab_coe]
  intro i
  simp

theorem mkPerm_coe (m : Perm (Fin 16)) : mkPerm (⇑m) = m := by
  unfold mkPerm
  simp only [isPermChk_coe m, dite_true]
  ext i
  rfl

theorem lin_check2 (g : Fin 16 → Fin 16 → Bool) (c : Perm (Fin 16) → Bool)
    (h : allQ2 g c = true) {m : Perm (Fin 16)} (hm : IsLin16 m) (hg : g (m 1) (m 2) = true) :
    c m = true := by
  simp only [allQ2, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  rcases h (m 1) (m 2) with h1 | h1
  · rw [hg] at h1
    exact absurd h1 (by simp)
  · have h2 := h1 (m 4) (m 8)
    have hq : linFun (m 1, m 2, m 4, m 8) = ⇑m := funext fun i => (lin_eq hm i).symm
    rw [hq] at h2
    rcases h2 with h2 | h2
    · rw [isPermChk_coe] at h2
      exact absurd h2 (by simp)
    · rwa [mkPerm_coe] at h2

theorem isLin16_of_chk {m : Perm (Fin 16)} (h : linChk m = true) : IsLin16 m := by
  intro i j
  simp only [linChk, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies] at h
  exact h i j

theorem getD_tabL (p : Perm (Fin 16)) (j : Fin 16) : (tabL p).getD j.val 0 = p j := by
  simp [tabL, List.getD_eq_getElem?_getD]

theorem tabL_mul (a b : Perm (Fin 16)) : tmulL (tabL a) (tabL b) = tabL (a * b) := by
  simp only [tmulL, tabL, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  rw [← tabL, getD_tabL]
  rfl

theorem tabL_one : tabL 1 = List.finRange 16 := by simp [tabL]

theorem tabL_injective : Function.Injective tabL := by
  intro p q h
  refine Equiv.ext fun i => ?_
  have := (List.map_inj_left.1 h) i (List.mem_finRange i)
  exact this

theorem one_mem_closureL (gens : List (List (Fin 16))) (k : ℕ) :
    List.finRange 16 ∈ closureL gens k := by
  induction k with
  | zero => simp [closureL]
  | succ k ih =>
    simp only [closureL, Function.iterate_succ_apply'] at ih ⊢
    rw [List.mem_dedup, List.mem_append]
    exact Or.inl ih

theorem closureL_sound (gens : List (Perm (Fin 16))) (k : ℕ) :
    ∀ t ∈ closureL (gens.map tabL) k, ∃ g ∈ Subgroup.closure {x | x ∈ gens}, tabL g = t := by
  induction k with
  | zero =>
    intro t ht
    simp only [closureL, Function.iterate_zero, id, List.mem_singleton] at ht
    exact ⟨1, one_mem _, by rw [ht, tabL_one]⟩
  | succ k ih =>
    intro t ht
    simp only [closureL, Function.iterate_succ_apply'] at ht
    rw [List.mem_dedup, List.mem_append, List.mem_flatMap] at ht
    rcases ht with h | ⟨g', hg', ht2⟩
    · exact ih t h
    · rw [List.mem_map] at ht2
      obtain ⟨s', hs', rfl⟩ := ht2
      rw [List.mem_map] at hs'
      obtain ⟨s, hs, rfl⟩ := hs'
      obtain ⟨g, hg, rfl⟩ := ih g' hg'
      exact ⟨g * s, mul_mem hg (Subgroup.subset_closure hs), (tabL_mul g s).symm⟩

theorem mem_closure_of_tab (gens : List (Perm (Fin 16))) (k : ℕ) {A : Perm (Fin 16)}
    (h : tabL A ∈ closureL (gens.map tabL) k) : A ∈ Subgroup.closure {x | x ∈ gens} := by
  obtain ⟨g, hg, hgA⟩ := closureL_sound gens k _ h
  rw [← tabL_injective hgA]
  exact hg

theorem closure_sub_tab (gens : List (Perm (Fin 16))) (T : List (List (Fin 16)))
    (h1 : List.finRange 16 ∈ T)
    (hr : ∀ t ∈ T, ∀ s ∈ gens, tmulL t (tabL s) ∈ T ∧ tmulL t (tabL s⁻¹) ∈ T)
    {y : Perm (Fin 16)} (hy : y ∈ Subgroup.closure {x | x ∈ gens}) : tabL y ∈ T := by
  refine Subgroup.closure_induction_right (s := {x | x ∈ gens})
    (p := fun y _ => tabL y ∈ T) ?_ ?_ ?_ hy
  · rwa [tabL_one]
  · intro x _ s hs ih
    rw [← tabL_mul]
    exact (hr _ ih s hs).1
  · intro x _ s hs ih
    rw [← tabL_mul]
    exact (hr _ ih s hs).2

theorem orbList_mem {gs : List (Perm (Fin 16))} {F : Finset (Finset (Fin 16))} (hQ : Qpl ∈ F)
    (hF : ∀ V ∈ F, ∀ g ∈ gs, V.image g ∈ F) (k : ℕ) : ∀ V ∈ orbList gs k, V ∈ F := by
  induction k with
  | zero =>
    intro V hV
    simp only [orbList, Function.iterate_zero, id, List.mem_singleton] at hV
    rw [hV]
    exact hQ
  | succ k ih =>
    intro V hV
    simp only [orbList, Function.iterate_succ_apply', orbStep] at hV
    have hV' := List.mem_of_mem_take hV
    rw [List.mem_dedup, List.mem_append, List.mem_flatMap] at hV'
    rcases hV' with h | ⟨W, hW, hV2⟩
    · exact ih V h
    · rw [List.mem_map] at hV2
      obtain ⟨g, hg, rfl⟩ := hV2
      exact hF W (ih W hW) g hg

theorem card_double {M : Type*} [Group M] (S : Set M) (x : M) (D : Subgroup M) [Finite D]
    (hS : Subgroup.closure S ≤ D) (hx : x ∈ D) (hxS : x ∉ Subgroup.closure S) :
    2 * Nat.card (Subgroup.closure S) ≤ Nat.card (Subgroup.closure (insert x S)) := by
  have hle : Subgroup.closure S ≤ Subgroup.closure (insert x S) :=
    Subgroup.closure_mono (Set.subset_insert _ _)
  have hlt : Subgroup.closure S < Subgroup.closure (insert x S) :=
    lt_of_le_of_ne hle fun h => hxS (h ▸ Subgroup.subset_closure (Set.mem_insert _ _))
  have hSD : S ⊆ D := fun y hy => hS (Subgroup.subset_closure hy)
  have hK : Subgroup.closure (insert x S) ≤ D :=
    (Subgroup.closure_le D).2 (Set.insert_subset hx hSD)
  have : Finite (Subgroup.closure (insert x S)) :=
    Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)
  have h1 := Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

theorem exists_gen3 {M : Type*} [Group M] (D : Subgroup M) [Finite D] (a : M) (ha : a ∈ D)
    (ha1 : a ≠ 1) (hcard : Nat.card D ≤ 8) :
    ∃ b ∈ D, ∃ c ∈ D, Subgroup.closure {a, b, c} = D := by
  have hbot : Subgroup.closure (∅ : Set M) = ⊥ := Subgroup.closure_empty
  have hnot : a ∉ Subgroup.closure (∅ : Set M) := by
    rw [hbot, Subgroup.mem_bot]
    exact ha1
  have h1 := card_double ∅ a D (by rw [hbot]; exact bot_le) ha hnot
  rw [hbot, Subgroup.card_bot] at h1
  have e1 : (insert a (∅ : Set M)) = {a} := by simp
  rw [e1] at h1
  have haD : ({a} : Set M) ⊆ D := by simpa using ha
  have hle1 : Subgroup.closure ({a} : Set M) ≤ D := (Subgroup.closure_le D).2 haD
  by_cases hD1 : Subgroup.closure ({a} : Set M) = D
  · refine ⟨a, ha, a, ha, ?_⟩
    simpa using hD1
  · obtain ⟨b, hbD, hb⟩ : ∃ b ∈ D, b ∉ Subgroup.closure ({a} : Set M) := by
      by_contra hcon
      refine hD1 (le_antisymm hle1 fun x hx => ?_)
      by_contra hxn
      exact hcon ⟨x, hx, hxn⟩
    have h2 := card_double {a} b D hle1 hbD hb
    have habD : (insert b ({a} : Set M)) ⊆ D := Set.insert_subset hbD haD
    have hle2 : Subgroup.closure (insert b ({a} : Set M)) ≤ D := (Subgroup.closure_le D).2 habD
    by_cases hD2 : Subgroup.closure (insert b ({a} : Set M)) = D
    · refine ⟨b, hbD, b, hbD, ?_⟩
      rw [← hD2]
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · obtain ⟨c, hcD, hc⟩ : ∃ c ∈ D, c ∉ Subgroup.closure (insert b ({a} : Set M)) := by
        by_contra hcon
        refine hD2 (le_antisymm hle2 fun x hx => ?_)
        by_contra hxn
        exact hcon ⟨x, hx, hxn⟩
      have h3 := card_double (insert b {a}) c D hle2 hcD hc
      refine ⟨b, hbD, c, hcD, ?_⟩
      have hle3 : Subgroup.closure (insert c (insert b ({a} : Set M))) ≤ D :=
        (Subgroup.closure_le D).2 (Set.insert_subset hcD habD)
      have e3 : ({a, b, c} : Set M) = insert c (insert b {a}) := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [e3]
      refine Subgroup.eq_of_le_of_card_ge hle3 ?_
      omega

theorem Qpl_image_lin {m : Perm (Fin 16)} (h : IsLin16 m) :
    Qpl.image m = {0, m 1, m 2, xor16 (m 1) (m 2)} := by
  have h3 : m 3 = xor16 (m 1) (m 2) := h 1 2
  simp only [Qpl, Finset.image_insert, Finset.image_singleton, lin_zero h, ← h3]

theorem fam0Chk_iff {m : Perm (Fin 16)} : fam0Chk m = true ↔ ∀ V ∈ fam0, V.image m ∈ fam0 := by
  unfold fam0Chk
  exact decide_eq_true_iff

end CFSG.GH74.GLS.C3.Layer2.L5.HF
