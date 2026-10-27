module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneInnerBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptional

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog (conj_injective)

theorem innerInvolutionInput_of_criterion {C : Type*} [Group C]
    (h : ∀ t : C, orderOf (MulAut.conj t) = 2 → InnerCentralizerCriterion t) :
    InnerInvolutionInput C :=
  innerInvolution_noNormalZ4OrZ2xZ4_of_forall h

theorem innerInvolutionInput_of_representatives {C : Type*} [Group C] {T : Set C}
    (hT : ∀ s ∈ T, InnerCentralizerCriterion s)
    (hrep : ∀ t : C, orderOf (MulAut.conj t) = 2 → ∃ ψ : MulAut C, ∃ s ∈ T, ψ s = t) :
    InnerInvolutionInput C :=
  innerInvolution_noNormalZ4OrZ2xZ4_of_representatives hT hrep

variable {K : Type} [Field K]

theorem innerCentralizerCriterion_of_conj_radical
    [Finite K] [CharP K 2] (D : RootWeightDatum K) {J : Set (Fin D.rank)} (hJ : J ≠ Set.univ)
    (g : D.group) {t : D.group}
    (hodd : (D.radicalIn J).map (MulAut.conj g).toMonoidHom ≤
      closure {c : D.group | c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ z ∈ (D.radicalIn J).map (MulAut.conj g).toMonoidHom,
      (∀ u ∈ (D.radicalIn J).map (MulAut.conj g).toMonoidHom, z * u = u * z) →
      (∀ c : D.group, c * t = t * c → Odd (orderOf c) → z * c = c * z) → z ^ 2 = 1)
    (hout : ∀ β : MulAut D.group,
      (∀ u ∈ (D.radicalIn J).map (MulAut.conj g).toMonoidHom, β u = u) → β ∈ D.actors) :
    InnerCentralizerCriterion t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ, -, -, hpt⟩ := D.radical_facts 2 hJ
  have hpt' := pointwise_stabilizer_map_conj D.conj_range_le_actors hpt g
  refine innerCentralizerCriterion_of_pointwise (conj_injective hZ) hodd fun β hβ => ?_
  obtain ⟨z, hz, rfl⟩ := (hpt' β).1 ⟨hout β hβ, hβ⟩
  obtain ⟨hzU, hzc⟩ := mem_map_center_subtype_iff.1 hz
  exact ⟨z, rfl, hcen z hzU hzc⟩

theorem innerCentralizerCriterion_of_conj_radical_of_actors_eq_top
    [Finite K] [CharP K 2] (D : RootWeightDatum K) (hA : D.actors = ⊤) {J : Set (Fin D.rank)}
    (hJ : J ≠ Set.univ) (g : D.group) {t : D.group}
    (hodd : (D.radicalIn J).map (MulAut.conj g).toMonoidHom ≤
      closure {c : D.group | c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ z ∈ (D.radicalIn J).map (MulAut.conj g).toMonoidHom,
      (∀ u ∈ (D.radicalIn J).map (MulAut.conj g).toMonoidHom, z * u = u * z) →
      (∀ c : D.group, c * t = t * c → Odd (orderOf c) → z * c = c * z) → z ^ 2 = 1) :
    InnerCentralizerCriterion t :=
  innerCentralizerCriterion_of_conj_radical D hJ g hodd hcen fun β _ => hA ▸ mem_top β

end CFSG.SeitzReduction
