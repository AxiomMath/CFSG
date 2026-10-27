module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Bridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.FStarFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.QuotTransfer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Inputs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem residual_or_kDatum_of_vertical (hI : Phase1Inputs) (hL : Leaves1) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hZ : IsPGroup 2 ↥(center K))
    (hcat : Catalog (K ⧸ center K)) {σ : MulAut K} (hσ : ∀ y, σ (σ y) = y) {X : Subgroup K}
    (hXF : X ≤ fixedSubgroup σ) (hX : IsPComponent 2 (X.subgroupOf (fixedSubgroup σ)))
    (hXFS : IsFStar ↥X) (hKFS : ¬ IsFStar K) : IsResidualA2 K ∨ KDatum K := by
  have hXtop : X ≠ ⊤ := by
    intro hXeq
    apply hKFS
    exact (isFStar_congr ((MulEquiv.subgroupCongr hXeq).trans Subgroup.topEquiv)).1 hXFS
  obtain ⟨σ', P, hP, ⟨e⟩⟩ := exists_properFixedComponent_quotient hK hσ hXF hX hXtop
  have hXqFS : FStarSimple (↥X ⧸ Open.fusionZStar ↥X) := fStarSimple_of_isFStar hXFS
  have hPFS : FStarSimple (↥P ⧸ Open.fusionZStar ↥P) := (fStarSimple_congr e).1 hXqFS
  have hP3 : HarrisLit.IsSimpleChevalleyOver 3 (↥P ⧸ Open.fusionZStar ↥P) :=
    isSimpleChevalleyOver_three_of_fStarSimple hPFS
  have hclaim : IsResidualA2 K ∨ HarrisLit.IsSimpleChevalleyOver 3 (K ⧸ center K) := by
    by_cases hinX : GH74.GLS.InChev2 (↥X ⧸ Open.fusionZStar ↥X)
    ·
      rcases hL.tableC K hK hZ hcat σ hσ X hXF hX hXFS hinX hKFS with h | h
      · exact Or.inr h
      · exact Or.inl h
    ·
      have hnotP : ¬ GH74.GLS.InChev2 (↥P ⧸ Open.fusionZStar ↥P) :=
        fun h => hinX ((inChev2_congr e).2 h)
      rcases hI.p1 (K ⧸ center K) hK.2.1 hK.2.2 hcat σ' P hP 3 Nat.prime_three
          (by norm_num) hP3 hnotP with h | h
      · exact Or.inr h.1
      · exact False.elim (false_of_fStarSimple_psl_two_seventeen hPFS h.2)
  rcases hclaim with hres | h3
  · exact Or.inl hres
  · by_cases hFS : FStarSimple (K ⧸ center K)
    ·
      have hne : center K ≠ ⊥ := by
        intro hc
        apply hKFS
        have hO : pPrimeCore 2 K = ⊥ := pPrimeCore_eq_bot_of_isQuasisimple hK hZ
        have eK : K ⧸ center K ≃* K :=
          (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
        exact isFStar_of_fStarSimple hO ((fStarSimple_congr eK).1 hFS)
      exact Or.inr (Or.inl (hL.coverDatum K hK hZ hne hFS hKFS))
    ·
      rcases hL.chev3Datum K hK hZ h3 hFS σ hσ X hXF hX hXFS with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

end CFSG.OddStandard.SmallF3.HypA2
