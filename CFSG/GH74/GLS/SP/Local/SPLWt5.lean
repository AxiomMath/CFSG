module

public import CFSG.GH74.GLS.SP.Local.SPLWt4

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

section Lists

theorem eq_filter_of_sorted (l : List ℤ) (hl : l.Pairwise (· < ·)) (P : ℤ → Prop)
    [DecidablePred P] (h : ∀ i, i ∈ l ↔ (1 ≤ i ∧ i ≤ 4) ∧ P i) :
    l = [1, 2, 3, 4].filter (fun i => decide (P i)) := by
  have hL : ([1, 2, 3, 4] : List ℤ).Pairwise (· < ·) := by decide
  have hF := hL.filter (fun i => decide (P i))
  have hnd : l.Nodup := hl.imp (fun h => ne_of_lt h)
  have hnd' : ([1, 2, 3, 4].filter (fun i => decide (P i))).Nodup := hF.imp (fun h => ne_of_lt h)
  have hperm : l.Perm ([1, 2, 3, 4].filter (fun i => decide (P i))) := by
    rw [List.perm_ext_iff_of_nodup hnd hnd']
    intro i
    rw [h i, List.mem_filter]
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨⟨h1, h4⟩, hp⟩
      refine ⟨?_, hp⟩
      omega
    · rintro ⟨hi, hp⟩
      exact ⟨⟨by omega, by omega⟩, hp⟩
  exact hperm.eq_of_pairwise (fun a _ b _ hab hba => le_antisymm hab hba)
    (hl.imp le_of_lt) (hF.imp le_of_lt)

theorem chainProd_reverse (A : ℤ → Subgroup G) (l : List ℤ) :
    chainProd A l.reverse = (chainProd A l)⁻¹ := by
  induction l with
  | nil => simp [chainProd]
  | cons a l ih =>
    simp only [chainProd, List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
      List.map_nil] at ih ⊢
    rw [List.prod_append, List.prod_singleton, mul_inv_rev, ih, inv_coe_set]

theorem chainProd_filter (A : ℤ → Subgroup G) (P : ℤ → Prop) [DecidablePred P] :
    chainProd A ([1, 2, 3, 4].filter (fun i => decide (P i))) =
      (↑(if P 1 then A 1 else ⊥) : Set G) * ↑(if P 2 then A 2 else ⊥) *
        ↑(if P 3 then A 3 else ⊥) * ↑(if P 4 then A 4 else ⊥) := by
  by_cases h1 : P 1 <;> by_cases h2 : P 2 <;> by_cases h3 : P 3 <;> by_cases h4 : P 4 <;>
    simp [chainProd, List.filter, h1, h2, h3, h4, mul_assoc, Set.singleton_one]

theorem prod_map_filter (f : ℤ → ℕ) (P : ℤ → Prop) [DecidablePred P] :
    (([1, 2, 3, 4].filter (fun i => decide (P i))).map f).prod =
      (if P 1 then f 1 else 1) * (if P 2 then f 2 else 1) * (if P 3 then f 3 else 1) *
        (if P 4 then f 4 else 1) := by
  by_cases h1 : P 1 <;> by_cases h2 : P 2 <;> by_cases h3 : P 3 <;> by_cases h4 : P 4 <;>
    simp [List.filter, h1, h2, h3, h4, mul_assoc]

end Lists

section L42

variable [Finite G] (D : SPLNot3 G)

omit [Finite G] in
open Classical in
theorem inf_flag {Z A : Subgroup G} (h : Z ⊓ A = ⊥ ∨ A ≤ Z) :
    Z ⊓ A = if A ≤ Z then A else ⊥ := by
  by_cases hA : A ≤ Z
  · simp [hA]
  · simp [hA, h.resolve_right hA]

theorem l42_inc (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) {Z : Subgroup G} (hZP : Z ≤ D.P) (hZH : Normalizes D.H Z) (l : List ℤ)
    (hl : l.Pairwise (· < ·)) (hlm : ∀ i, i ∈ l ↔ (1 ≤ i ∧ i ≤ 4) ∧ D.root i ≤ Z) :
    (Z : Set G) = chainProd D.root l ∧
      Nat.card ↥Z = (l.map fun i => Nat.card ↥(D.root i)).prod := by
  classical
  have hlF := eq_filter_of_sorted l hl (fun i => D.root i ≤ Z) hlm
  have hP1 := Z_eq_prod D hs h1 h3 hR hZP hZH
  have hP2 := Z_card D hs h1 h3 hR hZP hZH
  have f4 := inf_flag (inf_irred (irred_X₄ D hs h1 h3) hZH (H_X₄ D hs h1 h3))
  have f2 := inf_flag (inf_irred (irred_X₂ D hs h1 h3) hZH (H_X₂ D hs h1 h3.toSPL3X))
  have f3 := inf_flag (inf_irred (irred_X₃ D hs h1 h3) hZH h3.H_X₃)
  have f1 := inf_flag (inf_irred (irred_X₁ D hs h1 h3) hZH h3.H_X₁)
  have hc : ∀ i : ℤ, 1 ≤ i → i ≤ 4 → Nat.card ↥(D.root i) = D.q := fun i hi1 hi4 =>
    root_card D h3 ⟨by omega, by omega⟩
  rw [hlF]
  refine ⟨?_, ?_⟩
  · rw [chainProd_filter, hP1, f4, f2, f3, f1, root_p1, root_p2, root_p3, root_p4]
  · rw [prod_map_filter, hP2, f4, f2, f3, f1, root_p1, root_p2, root_p3, root_p4]
    have e4 := X₄_card D h3
    have e2 := X₂_card D h3
    have e3 := X₃_card D h3
    have e1 := h3.X₁_card
    by_cases c4 : D.X₄ ≤ Z <;> by_cases c2 : D.X₂ ≤ Z <;> by_cases c3 : D.X₃ ≤ Z <;>
      by_cases c1 : D.X₁ ≤ Z <;> simp [c4, c2, c3, c1, e4, e2, e3, e1, mul_assoc]

theorem l42_of (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) : D.L42 := by
  intro Z hZP hZH l hl hlm
  rcases hl with hl | hl
  · exact l42_inc D hs h1 h3 hR hZP hZH l hl hlm
  · have hl' : l.reverse.Pairwise (· < ·) := by
      rw [List.pairwise_reverse]; exact hl
    have hlm' : ∀ i, i ∈ l.reverse ↔ (1 ≤ i ∧ i ≤ 4) ∧ D.root i ≤ Z := fun i => by
      rw [List.mem_reverse]; exact hlm i
    obtain ⟨e1, e2⟩ := l42_inc D hs h1 h3 hR hZP hZH l.reverse hl' hlm'
    refine ⟨?_, ?_⟩
    · have : chainProd D.root l = (chainProd D.root l.reverse)⁻¹ := by
        rw [chainProd_reverse, inv_inv]
      rw [this, ← e1, inv_coe_set]
    · rw [e2, List.map_reverse, List.prod_reverse]

theorem exists_root_le (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) {Z : Subgroup G} (hZP : Z ≤ D.P) (hZH : Normalizes D.H Z) (hne : Z ≠ ⊥) :
    D.X₁ ≤ Z ∨ D.X₂ ≤ Z ∨ D.X₃ ≤ Z ∨ D.X₄ ≤ Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3, c4⟩ := hcon
  have hP1 := Z_eq_prod D hs h1 h3 hR hZP hZH
  have f4 := inf_flag (inf_irred (irred_X₄ D hs h1 h3) hZH (H_X₄ D hs h1 h3))
  have f2 := inf_flag (inf_irred (irred_X₂ D hs h1 h3) hZH (H_X₂ D hs h1 h3.toSPL3X))
  have f3 := inf_flag (inf_irred (irred_X₃ D hs h1 h3) hZH h3.H_X₃)
  have f1 := inf_flag (inf_irred (irred_X₁ D hs h1 h3) hZH h3.H_X₁)
  rw [f4, f2, f3, f1] at hP1
  simp only [c1, c2, c3, c4, ite_false, Subgroup.coe_bot, Set.singleton_mul_singleton, mul_one] at hP1
  apply hne
  rw [eq_bot_iff]
  intro z hz
  have : z ∈ (({1} : Set G)) := by rw [← hP1]; exact hz
  exact Subgroup.mem_bot.mpr (Set.mem_singleton_iff.mp this)

end L42

end CFSG.GH74.GLS.SP.Local
