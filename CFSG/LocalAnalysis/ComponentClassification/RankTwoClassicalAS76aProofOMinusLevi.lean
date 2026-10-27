module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

section Swap

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_swap_mem_minus {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ s₀ : StatedOmega (StatedQuadMinus (1 + 3) K b c),
      (s₀ : GL (Fin (1 + 3 - 1) ⊕ Fin (1 + 3 - 1) ⊕ Fin 2) K) =
        oblkGL (minusOe 1) (swapMinusGL, swapOneGL) := by
  have hiso : ∀ v, quadMinus (1 + 3) K b c
      (((oblkGL (minusOe 1) (swapMinusGL, swapOneGL) : GL _ K) : Matrix _ _ K) *ᵥ v) =
        quadMinus (1 + 3) K b c v := fun v => by
    rw [coe_quadMinus, coe_oblkGL]
    exact quad_oblk_mulVec_eq (statedQuadMinus_minusOe 1 b c) (statedQuadMinus_swapMinusMat b c)
      quadPlus_two_swapOneMat v
  have hev : Even (commRank (oblkGL (minusOe 1)
      ((swapMinusGL : GL (Fin 1 ⊕ Fin 1 ⊕ Fin 2) K), (swapOneGL : GL (Fin 2 ⊕ Fin 2) K)))) := by
    rw [commRank_oblkGL_swap (φ := fun w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → K => w (.inl 0) +
      w (.inr (.inl 0))) swapMinusGL_sub_one_mulVec (b₂ := Pi.single (.inl 0) 1 +
        Pi.single (.inr (.inl 0)) 1) (by
          intro h
          have := congrFun h (.inl 0)
          simp at this) (w₁ := Pi.single (.inl 0) 1) (by simp)]
    exact even_two
  have hmem := mem_statedOmega_of (quadMinus (1 + 3) K b c)
    (nondegenerate_polarBilin_quadMinus_of_finite _ K hbc)
    (exists_totallySingular_quadMinus (by norm_num) K b c) hiso hev
  rw [coe_quadMinus] at hmem
  exact ⟨⟨_, hmem⟩, rfl⟩

end Swap

end CFSG.ComponentClassification.RankTwoClassical
