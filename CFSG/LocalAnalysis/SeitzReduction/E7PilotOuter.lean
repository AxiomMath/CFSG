module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEClasses

public section

namespace CFSG.SeitzReduction.E7Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms


variable {K : Type} [Field K]

theorem isCyclic_outer_adjointGroup_E7 [Finite K] [CharP K 2] :
    IsCyclic (Outer (adjointGroup .E7 K)) := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_eClasses K
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E7 (Or.inl rfl)
  have : IsCyclic (K ≃+* K) := ringAut_isCyclic
  have hinner : inner (adjointGroup .E7 K) = Θ.ker := hker.symm
  let φ : Outer (adjointGroup .E7 K) ≃* (K ≃+* K) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  exact isCyclic_of_surjective φ.symm φ.symm.surjective

theorem center_eq_bot_of_mulEquiv_E7 [Finite K] {L : Type*} [Group L]
    (e : L ≃* adjointGroup .E7 K) : Subgroup.center L = ⊥ := by
  have h := center_map_equiv e
  rw [center_adjointGroup_eq_bot] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h

theorem isCyclic_outer_of_mulEquiv_E7 [Finite K] [CharP K 2] {L : Type*} [Group L]
    (e : L ≃* adjointGroup .E7 K) : IsCyclic (Outer L) := by
  have := isCyclic_outer_adjointGroup_E7 (K := K)
  exact isCyclic_of_surjective (equivalence e).symm (equivalence e).symm.surjective

end CFSG.SeitzReduction.E7Pilot
