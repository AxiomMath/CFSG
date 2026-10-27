module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup

theorem index_le_two_of_forall {G : Type} [Group G] {K : Subgroup G} (s : G)
    (h : ∀ x : G, x ∈ K ∨ s⁻¹ * x ∈ K) : K.index ≤ 2 := by
  have hsurj : Function.Surjective
      (fun b : Bool => (QuotientGroup.mk (if b then s else 1) : G ⧸ K)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rcases h x with hx | hx
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [QuotientGroup.eq]
      simpa using hx
    · refine ⟨true, ?_⟩
      simp only [↓reduceIte]
      rw [QuotientGroup.eq]
      exact hx
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  rwa [Subgroup.index_eq_card]

theorem card_le_four_of_cyclic_index_le_two {G : Type} [Group G] [Finite G] {K : Subgroup G}
    [IsCyclic K] (hK : K.index ≤ 2) {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 4 := by
  have hcard := Subgroup.relIndex_mul_card (H := K) (K := E)
  have hrel : K.relIndex E ≤ K.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top (by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite)
  have hcyc : IsCyclic ↥(K ⊓ E) := isCyclic_of_injective (Subgroup.inclusion inf_le_left)
    (Subgroup.inclusion_injective _)
  have hexp : Monoid.exponent ↥(K ⊓ E) ∣ 2 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    have := hE.2 (x : G) (Subgroup.mem_inf.1 x.2).2
    exact Subtype.ext (by simpa using this)
  have h2 : Nat.card ↥(K ⊓ E) ≤ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  calc Nat.card E = K.relIndex E * Nat.card ↥(K ⊓ E) := hcard.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul (hrel.trans hK) h2
    _ = 4 := by norm_num

end CFSG.EvenSporadicStandard.Induction.Junction
