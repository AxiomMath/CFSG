module

public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryCocycleGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.ModelFacts (odd_natCard_galoisField_of_pow_eq_three)
open scoped MatrixGroups



section Minus

variable {p f : ℕ} [Fact p.Prime]

theorem fundCorr_minus3 (h3 : p ^ f = 3) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) :
    (∀ R ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)),
        R.map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)) ∈
          fundSet (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)) ∧
      ∀ L ∈ fundSet (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2),
        ∃ R ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)),
          R.map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
            (minusCoeffs p f).2)) = L := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd := odd_natCard_galoisField_of_pow_eq_three h3
  have hlong := ModelFacts.isLongestRoot_single .POmegaMinus n p f Fact.out trivial hadm
  have hsc := ModelFacts.fundamentalSingleClass .POmegaMinus n p f Fact.out trivial hadm
    (by decide) (by decide)
  have hk : (0 : ℕ) + 1 < n - 1 := by omega
  set k₀ : Fin (n - 1) := ⟨0, by omega⟩ with hk₀
  have hij := Twisted.succ_ne_of_lt n (k := k₀) hk
  have hR := Twisted.rankOne_minusRootGroup_of_lt n (minusCoeffs_irr p f) (k := k₀) hk
  have hR₀ : CFSG.LieType.CurtisTits.rankOne (Twisted.minusRootGroup n (minusCoeffs_irr p f)) k₀ ∈
      fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)) :=
    ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 2 < n; omega)), by
      rw [conjSub_one]; rfl⟩
  have hdim : Module.finrank (GaloisField p f)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p f) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hperp : 2 ≤ Module.finrank (GaloisField p f)
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false).perp := by
    have := ModelFacts.finrank_perp_add_four
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false)
    omega
  have himg : (CFSG.LieType.CurtisTits.rankOne (Twisted.minusRootGroup n (minusCoeffs_irr p f))
        k₀).map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)) =
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false).La.range := by
    rw [hR]
    exact ModelFacts.map_longSL2_range
      (Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame hij true false
  exact spin_fund_correspondence hodd
    (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p f) (minusCoeffs_irr p f))
    hR₀ (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR => hsc _ hR₀ R hR) _ himg hperp

end Minus

end CFSG.ClassicalInvolution.RouteD.Exotic
