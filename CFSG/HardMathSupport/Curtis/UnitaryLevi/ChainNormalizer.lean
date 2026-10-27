module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainIso
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.NormalizerStab

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LinearGroups Matrix

theorem exists_chain_iso_normalizer {K : Type} [Field K] [Finite K] [CharP K 2] {r ε f : ℕ}
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (J : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K))
    (S₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K))
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤ J) (hJ : J ≠ ⊤) :
    ∃ (I : Set ℕ) (ψ : hypSU (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε ≃*
        StatedSU (2 * r + ε) (2 ^ f) K),
      I.Nonempty ∧ I ⊆ Set.Icc 1 r ∧
      J = (flagStabilizer (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε I).map
        ψ.toMonoidHom ∧
      (hypScalars (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε).map ψ.toMonoidHom =
        (StatedScalars (Fin (2 * r + ε)) K).subgroupOf (StatedSU (2 * r + ε) (2 ^ f) K) ∧
      ∃ W : ℕ → Submodule K (Fin (2 * r + ε) → K),
        (∀ i ∈ I, Module.finrank K (W i) = i ∧ IsTotallyIsotropicSU (2 ^ f) (W i)) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≤ j → W i ≤ W j) ∧
        (∀ y : StatedSU (2 * r + ε) (2 ^ f) K, y ∈ J ↔
          ∀ i ∈ I, ∀ w ∈ W i, ((y : GL (Fin (2 * r + ε)) K) : Matrix _ _ K) *ᵥ w ∈ W i) ∧
        ∀ u : GL (Fin (2 * r + ε)) K,
          (∀ x y : Fin (2 * r + ε) → K,
            stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε)
              ((u : Matrix _ _ K) *ᵥ x) ((u : Matrix _ _ K) *ᵥ y) =
            stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε) x y) →
          (∀ y y' : StatedSU (2 * r + ε) (2 ^ f) K, (y' : GL (Fin (2 * r + ε)) K) = u * y * u⁻¹ →
            (y ∈ J ↔ y' ∈ J)) →
          ∀ i ∈ I, ∀ w ∈ W i, (u : Matrix _ _ K) *ᵥ w ∈ W i := by
  obtain ⟨I, ψ, hne, hIr, hJψ, hZ, W, hW, hmono, hJW⟩ := exists_chain_iso hr hε hK hf J S₀ hNJ hJ
  refine ⟨I, ψ, hne, hIr, hJψ, hZ, W, hW, hmono, hJW, fun u hu hnorm => ?_⟩
  exact stabilizes_of_normalizes hK hf ((Set.finite_Icc 1 r).subset hIr)
    (fun i hi => (hW i hi).2) hmono (fun i hi => (hW i hi).1) J hJW u hu hnorm

end CFSG.HardMathSupport.Curtis.UnitaryLevi
