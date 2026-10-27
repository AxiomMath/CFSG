module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverStated
public import CFSG.ClassicalInvolution.Asc77.AscC5OM16

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ClassicalInvolution.Asc77.C5O.M (phiSL phiM phiM_injective phiM_neg_one mat_phiSL
  negOne negOne_mem_center mat_negOne)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Embedding

variable {F : Type} [Field F] (μ : F) [Fact (¬ IsSquare μ)]

theorem a2l_finite_quadAlg [Finite F] : Finite (QuadraticAlgebra F μ 0) :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd μ 0).symm

theorem a2l_card_quadAlg : Nat.card (QuadraticAlgebra F μ 0) = Nat.card F * Nat.card F := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd μ 0), Nat.card_prod]

theorem a2l_phiSL_injective : Function.Injective (phiSL μ) := fun A B h => by
  refine Subtype.ext (phiM_injective μ ?_)
  have := congrArg (mat 2 F) h
  rwa [mat_phiSL, mat_phiSL] at this

theorem a2l_phiSL_negOne : phiSL μ (a2lNegOne (QuadraticAlgebra F μ 0)) = negOne F :=
  mat_injective (by rw [mat_phiSL, mat_negOne]; exact phiM_neg_one μ)

end Embedding

theorem a2l_centralDatum_psp43 {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    (h2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (hm : LieModel (K ⧸ center K) .PSp 2 3 1) : HypA2.CentralDatum K := by
  haveI : Group.IsPerfect K := hq.1
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  have hF : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have hk : ringChar F ≠ 2 := a2l_ringChar_ne_two (by rw [hF]; decide)
  have hN : Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) < 2 * 2 := by
    rw [a2l_card_scalars_sp_four (by rw [hcard]; decide)]
    norm_num
  obtain ⟨ψ⟩ := a2l_nonempty_equiv_of_cover (a2l_splits_statedSp hk 2) h2 _ e hN
    (a2l_two_le_card_center h2 hZ)
  haveI : Fact (¬ IsSquare (-1 : F)) :=
    ⟨fun h => FiniteField.isSquare_neg_one_iff.1 h (by rw [hF])⟩
  haveI := a2l_finite_quadAlg (-1 : F)
  haveI := Fintype.ofFinite (QuadraticAlgebra F (-1) 0)
  have hE : Fintype.card (QuadraticAlgebra F (-1) 0) = 9 := by
    rw [← Nat.card_eq_fintype_card, a2l_card_quadAlg, hcard]
    norm_num
  have hTU : HypA2.TypU K := by
    have hO : pPrimeCore 2 K = ⊥ := HypA2.pPrimeCore_eq_bot_of_isQuasisimple hq h2
    have hZs : Open.fusionZStar K = center K := HypA2.fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
    exact Or.inr (Or.inr (Or.inl
      (LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZs).symm hm)))
  exact a2l_centralDatum_of_equiv ψ (by decide) (by norm_num) hE (phiSL (-1 : F))
    (a2l_phiSL_injective _) (by rw [a2l_phiSL_negOne]; exact negOne_mem_center) hTU

end CFSG.OddStandard.SmallF3.HypA2Leaves
