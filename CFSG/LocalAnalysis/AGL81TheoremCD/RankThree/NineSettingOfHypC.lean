module

public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.TheoremCThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTenBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineNineOneHolds

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
  CFSG.LocalAnalysis.AGL81TheoremCD.Section14

variable {G : Type} [Group G] [Finite G]

namespace RankThree

theorem cStarSetting_of_isWitness (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) {p : ℕ}
    (hp : p ∈ CFSG.Open.rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) : CStarSetting G M :=
  ⟨hS, hUC, hw.maxLocal, p, ⟨hp, by rw [(hw.pRank_eq_three hS hp).2]; omega⟩, P, hw⟩

end RankThree

namespace Section14.HypCGen

variable {M : Subgroup G} {q : ℕ} {E H : Subgroup G}

theorem toNineSetting (hC : CStarSetting G M) (h : HypCGen G M q E H) :
    NineSetting G M q E H E 2 :=
  nineSetting_iff_gen.mpr ⟨hC, h.toNineSettingGen⟩

theorem not_mem_sigmaM (h : HypCGen G M q E H) :
    q ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
  simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
    CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet

theorem nineTenConclusion (h10 : NineTen) (hC : CStarSetting G M) (h : HypCGen G M q E H) :
    NineTenConclusion G M E H E q :=
  h10 G M E H E q (h.toNineSetting hC) h.mem_H2Fam h.not_mem_sigmaM

theorem nineTwelveConclusion (h912 : NineTwelve) (hC : CStarSetting G M)
    (h : HypCGen G M q E H) : NineTwelveConclusion G M E H E q :=
  h912 G M E H E q (h.toNineSetting hC) h.mem_H2Fam h.not_mem_sigmaM

theorem nineSevenTwoInputConclusion (h97 : NineSevenTwoInput) (hC : CStarSetting G M)
    (h : HypCGen G M 3 E H) : NineSevenTwoInputConclusion G M E H E :=
  h97 G M E H E (h.toNineSetting hC) h.mem_H2Fam h.not_mem_sigmaM

end Section14.HypCGen

namespace RankThree

theorem nineNineOneAt_of_nineTenInputs (hI : NineTenInputs) {M : Subgroup G}
    (hC : CStarSetting G M) : NineNineOneAt M :=
  fun q E H h => CFSG.LocalAnalysis.AGL81TheoremCD.Section14.nineNineOneInput_holds G M E H E q (h.toNineSetting hC).toGen h.not_mem_sigmaM

theorem agl81TheoremC_of_fourteenFifteenAt (hS : Standing G) (hD : AGL81TheoremD G)
    (h1415 : ∀ M : Subgroup G, CStarSetting G M → FourteenFifteenAt M) : AGL81TheoremC G := by
  intro hUC p hp P M hw
  exact theoremCAt_of_theoremDAt (cStarGen_of_rankThreeUC hS hUC) hw.maxLocal
    (h1415 M (cStarSetting_of_isWitness hS hUC hp hw)) (hD hUC p hp P M hw)

end RankThree

end CFSG.LocalAnalysis.AGL81TheoremCD
