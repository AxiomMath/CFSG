module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Chain
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3K2Holds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDAssemble
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact131Holds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401OmegaMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2715
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactAutAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGAltSixFactMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGFiveProved
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaFieldAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaRed
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongK64ii
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291ConsumersHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4HoldsE3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5Frontier
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614ForP622
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotsFrontier

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614 (KFact64ii KFact64iiThree KFact292
  slotP614Core_of_kFact64ii slotP614CaseDelta_of_open p622CaseDelta4_holds)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD (s622KFactD_of_kfacts)

section FrontierNc3

theorem n4_coreLarge_core_nc3
    (hKF : KFact64iiL) (hAutO : KFactAutAltOrder)
    (hAutE : KFactAutAltEmbed) (h2024 : KG2024) (h2401 : KFact2401Three) (h2715 : KFact2715)
    (h131 : KFact131) (hpc : KFactParabolicCover) (hNC : KGNoncycCentE3) (hT : KGTransvCent)
    (h241 : KFact2401ThreeOmega) {G : Type} [Group G] [Finite G] (hS : Setting G) {p : ℕ}
    (hp5 : 5 ≤ p) {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {H S : Subgroup G} (hopt : Fail614OptimalGen p M x z H S)
    (hO : rankThreePrimeCore p H ≤ M)
    (hΩ : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z)
    (h65 : ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M → Nat.Coprime p (Nat.card F) → Odd (Nat.card F) →
      zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M)
    (hγ : IsPGroup 2 (rankThreePrimeCore p H) → ¬ HasPrimeConstraint (G := M) p → False) :
    False := by
  have h2 : IsPGroup 2 (rankThreePrimeCore p H) :=
    n4_isPGroup_two_primeCore hS hsit hx hz hopt hO fun F hF1 hFO hFo hBF =>
      h65 F hF1 (hFO.trans hO)
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hFO)
          (CFSG.AGLEmbedding.glbPrimeCore_coprime p H)) hFo hBF
  by_cases hα : HasPrimeConstraint (G := M) p
  · exact n4_false_of_alpha_nc3 hKF CFSG.LocalAnalysis.RankFourTheoremC.kFactZJFactorizationGe_holds
      hAutO hAutE h2024 h2401 kGAltSix_holds h2715 h131 hpc kfact282_holds
      (kgStep6NoncycE3_of_inputs hNC) hT h241 hS hsit hp5 hx hz hopt hO hΩ h2 hα
  · exact hγ h2 hα

theorem slotP614CoreLargeU0_of_steps_nc3
    (hP65 : StepP65OddE3U0) (hγ : SlotP614GammaE3U0)
    (hKF : KFact64iiL) (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (h2715 : KFact2715) (h131 : KFact131)
    (hpc : KFactParabolicCover) (hNC : KGNoncycCentE3) (hT : KGTransvCent)
    (h241 : KFact2401ThreeOmega) : SlotP614CoreLargeU0 := by
  intro G _ _ hS hD1 hU0 p hp5 P M hsit x z hx hz H S hopt hO hΩ
  exact n4_coreLarge_core_nc3 hKF hAutO hAutE h2024 h2401 h2715 h131 hpc hNC hT h241 hS hp5 hsit
    hx hz hopt hO hΩ (fun F hF1 hFM hcop hodd hBF =>
      hP65 G hS hD1 hU0 p hp5 P M hsit x z hx hz F hF1 hFM hcop hodd hBF)
    (fun h2 hα => hγ G hS hD1 hU0 p hp5 P M hsit x z hx hz H S hopt hO hΩ h2 hα)

theorem slotP614CoreLargeU0_of_fieldAut_nc3
    (hP65 : StepP65OddE3U0)
    (hfield : SlotP614GammaFieldAutE3U0) (hβ : NoTwoComponentsGen) (hγc : N3.GammaCentP)
    (hKF : KFact64iiL) (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (h2715 : KFact2715) (h131 : KFact131) (hpc : KFactParabolicCover)
    (hNC : KGNoncycCentE3) (hT : KGTransvCent) (h241 : KFact2401ThreeOmega) :
    SlotP614CoreLargeU0 :=
  slotP614CoreLargeU0_of_steps_nc3 hP65
    (slotP614GammaE3U0_of_fieldAut_nc3 hfield hβ hγc hKF
      CFSG.LocalAnalysis.RankFourTheoremC.kFactZJFactorizationGe_holds hAutO hAutE h2024 h2401
      kGAltSix_holds h2715 h131 hpc kfact282_holds (kgStep6NoncycE3_of_inputs hNC) hT h241)
    hKF hAutO hAutE h2024 h2401 h2715 h131 hpc hNC hT h241

theorem slotP614GammaFieldAutE3U0_of_kfacts_E3_nc3
    (hNC : KGNoncycCentE3)
    (hPara : KFactGammaParaE3) : SlotP614GammaFieldAutE3U0 :=
  slotP614GammaFieldAutE3U0_of_facts_E3_nc3 noTwoComponentsGen_holds N3.gammaCentP_holds
    CFSG.LocalAnalysis.RankFourTheoremC.kFactZJFactorizationGe_holds kFactAutAltOrder_holds
    kFact2715_holds kFact131_holds kfact282_holds (kgStep6NoncycE3_of_inputs hNC) kgTransvCent_holds
    hPara

theorem slotP614CoreLargeU0_of_frontierE3'_nc3
    (hK1 : KFactP65RankThree)
    (hLevi : KFactGammaLeviE3) (hpc : KFactParabolicCover)
    (hNC : KGNoncycCentE3) : SlotP614CoreLargeU0 :=
  slotP614CoreLargeU0_of_fieldAut_nc3
    (stepP65OddE3U0_of_kfactsE3 hK1.toS kFactP65RankTwoS_holds)
    (slotP614GammaFieldAutE3U0_of_kfacts_E3_nc3 hNC
      (kFactGammaParaE3_of_inputs hLevi kFactFieldAutLieE3_holds))
    noTwoComponentsGen_holds N3.gammaCentP_holds (kFact64iiL_of_outer kFact64iiOuterSylow_holds)
    kFactAutAltOrder_holds kFactAutAltEmbed_holds
    kg2024_holds kFact2401Three_holds kFact2715_holds kFact131_holds hpc hNC kgTransvCent_holds
    kFact2401ThreeOmega_holds

theorem slotP614CoreLargeU0_of_frontierE3_nc3
    (hK1 : KFactP65RankThree)
    (hLevi : KFactGammaLeviE3) (hpc : KFactParabolicCover)
    (hNC : KGNoncycCentE3) : SlotP614CoreLargeU0 :=
  slotP614CoreLargeU0_of_frontierE3'_nc3 hK1 hLevi hpc hNC

theorem slotP614LargeD2_of_frontierE3_nc3
    (hK1 : KFactP65RankThree)
    (hLevi : KFactGammaLeviE3) (hpc : KFactParabolicCover)
    (hNC : KGNoncycCentE3) : SlotP614LargeD2 :=
  slotP614LargeD2_of_coreU0 (slotP614CoreLargeU0_of_frontierE3_nc3 hK1 hLevi hpc hNC)

theorem gl83SmallRankInterfaceE3_of_frontierE3_nc3
    (hK1 : KFactP65RankThree) (hLevi : KFactGammaLeviE3)
    (hpc : KFactParabolicCover) (hNC : KGNoncycCentE3) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
      GL83SmallRankInterfaceW G :=
  gl83SmallRankInterfaceE3_of_open' (slotP614Three_of_frontier
      (Parrott.P614.kFact64iiThree_of_kFact64ii FongK64ii.kFact64ii_holds))
    (slotP614LargeD2_of_frontierE3_nc3 hK1 hLevi hpc hNC)
    (slotFitting628Five_of_prop65 (slotProp65Five_of_two_kfactsE3 hK1.toS kFactP65RankTwoS_holds))

theorem gl83SmallRankLemma630E3_of_frontierE3_nc3
    (hK1 : KFactP65RankThree) (hLevi : KFactGammaLeviE3)
    (hpc : KFactParabolicCover) (hNC : KGNoncycCentE3) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
      GL83SmallRankLemma630Res G :=
  gl83SmallRankLemma630E3_of_open' (slotP614Three_of_frontier
      (Parrott.P614.kFact64iiThree_of_kFact64ii FongK64ii.kFact64ii_holds))
    (slotP614LargeD2_of_frontierE3_nc3 hK1 hLevi hpc hNC)
    (slotLemma630FiveCond_of_prop65 (slotProp65Five_of_two_kfactsE3 hK1.toS kFactP65RankTwoS_holds))

theorem slotP614CoreLargeU0_of_frontierE3_L34
    (hK1 : KFactP65RankThree)
    (hLevi : KFactGammaLeviE3) (hpc : KFactParabolicCover)
    (hL34 : KGNoncycCentL34) : SlotP614CoreLargeU0 :=
  slotP614CoreLargeU0_of_frontierE3_nc3 hK1 hLevi hpc (FongOut.kgNoncycCentE3_of_L34 hL34)

theorem gl83SmallRankInterfaceE3_of_frontierE3_L34
    (hK1 : KFactP65RankThree)
    (hLevi : KFactGammaLeviE3) (hpc : KFactParabolicCover) (hL34 : KGNoncycCentL34) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
      GL83SmallRankInterfaceW G :=
  gl83SmallRankInterfaceE3_of_frontierE3_nc3 hK1 hLevi hpc (FongOut.kgNoncycCentE3_of_L34 hL34)

theorem gl83SmallRankLemma630E3_of_frontierE3_L34
    (hK1 : KFactP65RankThree)
    (hLevi : KFactGammaLeviE3) (hpc : KFactParabolicCover) (hL34 : KGNoncycCentL34) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
      GL83SmallRankLemma630Res G :=
  gl83SmallRankLemma630E3_of_frontierE3_nc3 hK1 hLevi hpc (FongOut.kgNoncycCentE3_of_L34 hL34)

end FrontierNc3

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
