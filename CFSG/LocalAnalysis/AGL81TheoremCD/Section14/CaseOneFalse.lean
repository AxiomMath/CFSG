module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenSeven
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenEightA
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenEightC
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenNine

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

section Certs44

theorem caseOneCtx_false
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) (h143 : FourteenThreeCaseOneAt M)
    (h145 : FourteenFiveCaseOneAt M)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (h7145 : CFSG.LocalAnalysis.RankThreeUC.S15.K7145) (h1410 : KFact1410a)
    (h4143 : K4143NoExtraspecial) : False := by
  have h7 : FourteenSevenData M H Q R T := c.fourteenSevenData h142 h143
  have h1 : ∀ p ∈ sigmaSet G M,
      CFSG.Open.pRank p (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ≤ 1 :=
    fun p hp => c.fourteenEight_one h142 h145 hp
  have h2 : CFSG.pCore 3 (threeStar M) = ⊥ := c.fourteenEight_two h142 h145
  obtain ⟨L, h8⟩ := c.exists_fourteenEightData h142 h1 h2 h7145
  have h9 : FourteenNineData M L T := c.fourteenNineData_of h7 h8
  exact caseOne_false_of_data c h142 h8 h9 c.inf_D_eq_bot c.pRank_threeStar_le
    hFF h1410 h4143

theorem caseOneFalse_of
    {M : Subgroup G} (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (h142 : FourteenTwoCaseOneAt M)
    (h143 : FourteenThreeCaseOneAt M) (h145 : FourteenFiveCaseOneAt M)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (h7145 : CFSG.LocalAnalysis.RankThreeUC.S15.K7145) (h1410 : KFact1410a)
    (h4143 : K4143NoExtraspecial) : CaseOneFalse M := by
  intro H E Q J hS hA
  obtain ⟨R, T, c⟩ := exists_caseOneCtx hS hA hpre hU hL
  exact caseOneCtx_false c h142 h143 h145 hFF h7145 h1410 h4143

theorem caseOneFalse_gen
    (h142 : FourteenTwoCaseOneGen)
    (h143 : FourteenThreeCaseOneGen) (h145 : FourteenFiveCaseOneGen)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (h7145 : CFSG.LocalAnalysis.RankThreeUC.S15.K7145) (h1410 : KFact1410a)
    (h4143 : K4143NoExtraspecial)
    (hstd : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleTypes M ∧ NineNineOneAt M ∧ PLayerNotLeAt M) :
    ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → CaseOneFalse M := by
  intro G _ _ hC M hM hσ
  obtain ⟨hpre, hU, hL⟩ := hstd G hC M hM hσ
  exact caseOneFalse_of hpre hU hL (h142 G M) (h143 G M) (h145 G M) hFF h7145 h1410 h4143

end Certs44

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
