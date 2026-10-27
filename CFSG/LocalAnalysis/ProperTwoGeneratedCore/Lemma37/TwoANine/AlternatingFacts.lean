module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.AlternatingFactsEight
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.AlternatingFactsThreeCycles
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Finset

private theorem exists_mul_eq_of {k : Fin 9} (n m : Perm (Fin 9)) (hn : Perm.sign n = 1)
    (hm : Perm.sign m = 1) (hn2 : n * n = 1) (hm2 : m * m = 1)
    (hnE : ∀ v : Fin 8, ∃ w : Fin 8,
      tripleWord (aNineEGenX : Perm (Fin 9)) aNineEZeroGenY aNineEZeroGenZ w =
        n * tripleWord (aNineEGenX : Perm (Fin 9)) aNineEZeroGenY aNineEZeroGenZ v * n)
    (hmE : ∀ v : Fin 8, ∃ w : Fin 8,
      tripleWord (aNineEGenX : Perm (Fin 9)) aNineEOneGenY aNineEOneGenZ w =
        m * tripleWord (aNineEGenX : Perm (Fin 9)) aNineEOneGenY aNineEOneGenZ v * m)
    (hnm : n * m = swap 0 k * swap 0 1) :
    ∃ n ∈ Subgroup.normalizer (ANineEZero : Set (alternatingGroup (Fin 9))),
      ∃ m ∈ Subgroup.normalizer (ANineEOne : Set (alternatingGroup (Fin 9))),
        ((n * m : alternatingGroup (Fin 9)) : Perm (Fin 9)) = swap 0 k * swap 0 1 :=
  ⟨⟨n, Perm.mem_alternatingGroup.mpr hn⟩, isRegularTriple_aNineEZero.mem_normalizer hn2 hnE,
    ⟨m, Perm.mem_alternatingGroup.mpr hm⟩, isRegularTriple_aNineEOne.mem_normalizer hm2 hmE, hnm⟩

theorem exists_mul_eq_threeCycle {k : Fin 9} (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk8 : k ≠ 8) :
    ∃ n ∈ Subgroup.normalizer (ANineEZero : Set (alternatingGroup (Fin 9))),
      ∃ m ∈ Subgroup.normalizer (ANineEOne : Set (alternatingGroup (Fin 9))),
        ((n * m : alternatingGroup (Fin 9)) : Perm (Fin 9)) = swap 0 k * swap 0 1 := by
  fin_cases k
  · exact absurd hk0 (by decide)
  · exact absurd hk1 (by decide)
  · exact exists_mul_eq_of (swap 1 2 * swap 5 6) (swap 0 2 * swap 5 6) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
  · exact exists_mul_eq_of (swap 1 3 * swap 5 7) (swap 0 3 * swap 5 7) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
  · exact exists_mul_eq_of (swap 1 4 * swap 3 6) (swap 0 4 * swap 3 6) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
  · exact exists_mul_eq_of (swap 1 5 * swap 3 7) (swap 0 5 * swap 3 7) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
  · exact exists_mul_eq_of (swap 1 6 * swap 3 4) (swap 0 6 * swap 3 4) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
  · exact exists_mul_eq_of (swap 1 7 * swap 3 5) (swap 0 7 * swap 3 5) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
  · exact absurd hk8 (by decide)

theorem normalizer_aNineEZero_sup_normalizer_aNineEOne :
    Subgroup.normalizer (ANineEZero : Set (alternatingGroup (Fin 9))) ⊔
        Subgroup.normalizer (ANineEOne : Set (alternatingGroup (Fin 9))) =
      MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) := by
  refine le_antisymm
    (sup_le normalizer_aNineEZero_le_stabilizer normalizer_aNineEOne_le_stabilizer) ?_
  rw [← closure_aNineThreeCycles, Subgroup.closure_le]
  rintro g ⟨k, hk0, hk1, hk8, hg⟩
  obtain ⟨n, hn, m, hm, hnm⟩ := exists_mul_eq_threeCycle hk0 hk1 hk8
  rw [show g = n * m from Subtype.ext (hg.trans hnm.symm)]
  exact Subgroup.mul_mem_sup hn hm

theorem isCoatom_stabilizer_eight :
    IsCoatom (MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9)) := by
  have : MulAction.IsPreprimitive (alternatingGroup (Fin 9)) (Fin 9) :=
    alternatingGroup.isPreprimitive_of_three_le_card (Fin 9) (by simp)
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive _ (8 : Fin 9)

theorem eq_stabilizer_of_le_of_ne_top {K : Subgroup (alternatingGroup (Fin 9))}
    (hK : MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) ≤ K) (hKtop : K ≠ ⊤) :
    K = MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) :=
  (isCoatom_stabilizer_eight.le_iff_eq hKtop).mp hK

theorem eq_stabilizer_of_normalizer_le_of_ne_top {K : Subgroup (alternatingGroup (Fin 9))}
    (h0 : Subgroup.normalizer (ANineEZero : Set (alternatingGroup (Fin 9))) ≤ K)
    (h1 : Subgroup.normalizer (ANineEOne : Set (alternatingGroup (Fin 9))) ≤ K)
    (hKtop : K ≠ ⊤) : K = MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) :=
  eq_stabilizer_of_le_of_ne_top (normalizer_aNineEZero_sup_normalizer_aNineEOne ▸ sup_le h0 h1)
    hKtop

theorem apply_eight_of_forall_conj_apply_eight {σ : Perm (Fin 9)}
    (hσ : ∀ g : alternatingGroup (Fin 9), (g : Perm (Fin 9)) 8 = 8 →
      (σ * (g : Perm (Fin 9)) * σ⁻¹) 8 = 8) : σ 8 = 8 := by
  by_contra hne
  set i := σ⁻¹ 8 with hi
  have hi8 : i ≠ 8 := fun h => hne (by rw [← Perm.inv_eq_iff_eq.mp h])
  have hc : ∀ i : Fin 9, i ≠ 8 →
      i ≠ (if i = 0 then 2 else 0) ∧ i ≠ (if i = 1 then 2 else 1) ∧
      (if i = 0 then (2 : Fin 9) else 0) ≠ (if i = 1 then 2 else 1) ∧
      (swap i (if i = 0 then 2 else 0) * swap i (if i = 1 then 2 else 1)) 8 = 8 ∧
      (swap i (if i = 0 then 2 else 0) * swap i (if i = 1 then 2 else 1)) i ≠ i := by
    decide
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc i hi8
  have h := hσ ⟨_, (Perm.isThreeCycle_swap_mul_swap_same h1 h2 h3).mem_alternatingGroup⟩ h4
  rw [Perm.mul_apply, Perm.mul_apply, ← hi] at h
  exact h5 (Perm.eq_inv_iff_eq.mpr h)

theorem exists_isThreeCycle_commute_of_card_support_le {σ : Perm (Fin 9)} (h8 : σ 8 = 8)
    (hσ : #σ.support ≤ 6) :
    ∃ c : alternatingGroup (Fin 9), (c : Perm (Fin 9)).IsThreeCycle ∧ (c : Perm (Fin 9)) 8 ≠ 8 ∧
      Commute (c : Perm (Fin 9)) σ := by
  have h8mem : (8 : Fin 9) ∈ σ.supportᶜ := Finset.mem_compl.mpr (Perm.notMem_support.mpr h8)
  have hcard : 1 < #(σ.supportᶜ.erase 8) := by
    rw [Finset.card_erase_of_mem h8mem, Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨hp8, hp⟩ := Finset.mem_erase.mp hp
  obtain ⟨hq8, hq⟩ := Finset.mem_erase.mp hq
  have hσp : σ p = p := Perm.notMem_support.mp (Finset.mem_compl.mp hp)
  have hσq : σ q = q := Perm.notMem_support.mp (Finset.mem_compl.mp hq)
  have hc := Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hp8) (Ne.symm hq8) hpq
  refine ⟨⟨swap 8 p * swap 8 q, hc.mem_alternatingGroup⟩, hc, ?_, ?_⟩
  · show (swap 8 p * swap 8 q) 8 ≠ 8
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hq8 (Ne.symm hpq)]
    exact hq8
  · refine Perm.Disjoint.commute fun x => ?_
    by_cases hx : x = 8 ∨ x = p ∨ x = q
    · rcases hx with rfl | rfl | rfl
      · exact Or.inr h8
      · exact Or.inr hσp
      · exact Or.inr hσq
    · simp only [not_or] at hx
      left
      show (swap 8 p * swap 8 q) x = x
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2.2, swap_apply_of_ne_of_ne hx.1 hx.2.1]

theorem card_support_le_six_of_sign_eq_neg_one {σ : Perm (Fin 9)} (hσ : σ ^ 2 = 1)
    (h8 : σ 8 = 8) (hsign : Perm.sign σ = -1) : #σ.support ≤ 6 := by
  have hsub : σ.support ⊆ Finset.univ.erase 8 := fun x hx =>
    Finset.mem_erase.mpr ⟨fun h => Perm.mem_support.mp hx (by rw [h]; exact h8),
      Finset.mem_univ x⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hle
  have heven := Perm.two_dvd_card_support hσ
  by_contra hlt
  have h4 : #σ.support = 2 * 4 := by omega
  rw [Perm.sign_of_cycleType, (cycleType_eq_replicate_iff_of_sq_eq_one hσ 4).mpr h4,
    Multiset.sum_replicate, Multiset.card_replicate] at hsign
  exact absurd hsign (by decide)

theorem exists_isThreeCycle_commute_of_sign_eq_neg_one {σ : Perm (Fin 9)} (hσ : σ ^ 2 = 1)
    (h8 : σ 8 = 8) (hsign : Perm.sign σ = -1) :
    ∃ c : alternatingGroup (Fin 9), (c : Perm (Fin 9)).IsThreeCycle ∧ (c : Perm (Fin 9)) 8 ≠ 8 ∧
      Commute (c : Perm (Fin 9)) σ :=
  exists_isThreeCycle_commute_of_card_support_le h8
    (card_support_le_six_of_sign_eq_neg_one hσ h8 hsign)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
