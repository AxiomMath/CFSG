module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

@[expose] def OmegaPlusEightThreeA1Similarity : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ (hSL : commutator SL(2, K) = ⊤)
      (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus (2 + 2) K)))),
      (∀ x ∈ oBarTwo (plusOe 2) (statedQuadPlus_plusOe 2) hSL, β x = x) →
      (∀ x ∈ oBarL (plusOe 2) (statedQuadPlus_plusOe 2), β x = x) →
      ∃ (σ : K ≃+* K) (A : GL (Fin (2 + 2) ⊕ Fin (2 + 2)) K) (μ : K), μ ≠ 0 ∧
        (∀ v, StatedQuadPlus (2 + 2) K (A.val *ᵥ fun i => σ (v i)) =
          μ * σ (StatedQuadPlus (2 + 2) K v)) ∧
        ∀ g : StatedOmega (StatedQuadPlus (2 + 2) K),
          ∃ hg : A * glAut σ (g : GL (Fin (2 + 2) ⊕ Fin (2 + 2)) K) * A⁻¹ ∈
            StatedOmega (StatedQuadPlus (2 + 2) K),
            β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩

section Swap

variable {K : Type} [Field K] [CharP K 2]

theorem swapOneGL_sub_one_mulVec (u : Fin 2 ⊕ Fin 2 → K) :
    (((swapOneGL : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) - 1) *ᵥ u =
      (fun w : Fin 2 ⊕ Fin 2 → K => w (.inl 1) + w (.inr 1)) u •
        (uE (.inl 1) + uE (.inr 1)) :=
  swapOneMat_sub_one_mulVec u

theorem exists_swap_mem_plus [Finite K] :
    ∃ s₀ : StatedOmega (StatedQuadPlus (2 + 2) K),
      (s₀ : GL (Fin (2 + 2) ⊕ Fin (2 + 2)) K) = oblkGL (plusOe 2) (swapOneGL, swapOneGL) := by
  have hiso : ∀ v, quadPlus (2 + 2) K
      (((oblkGL (plusOe 2) (swapOneGL, swapOneGL) : GL _ K) : Matrix _ _ K) *ᵥ v) =
        quadPlus (2 + 2) K v := fun v => by
    rw [coe_quadPlus, coe_oblkGL]
    exact quad_oblk_mulVec_eq (statedQuadPlus_plusOe 2) quadPlus_two_swapOneMat
      quadPlus_two_swapOneMat v
  have hev : Even (commRank (oblkGL (plusOe 2)
      (swapOneGL, (swapOneGL : GL (Fin 2 ⊕ Fin 2) K)))) := by
    rw [commRank_oblkGL_swap (φ := fun w : Fin 2 ⊕ Fin 2 → K => w (.inl 1) + w (.inr 1))
      swapOneGL_sub_one_mulVec (b₂ := uE (.inl 1) + uE (.inr 1)) (by
        intro h
        have := congrFun h (.inl 1)
        simp [uE] at this) (w₁ := uE (.inl 1)) (by simp [uE])]
    exact even_two
  have hmem := mem_statedOmega_of (quadPlus (2 + 2) K) (nondegenerate_polarBilin_quadPlus _ K)
    (exists_totallySingular_quadPlus (by norm_num) K) hiso hev
  rw [coe_quadPlus] at hmem
  exact ⟨⟨_, hmem⟩, rfl⟩

end Swap

end CFSG.ComponentClassification.RankTwoClassical
