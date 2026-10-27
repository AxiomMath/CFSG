module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O97Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Red
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Normalize
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Shape
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15 (O97Red o97Red_starImg KFactThreeFiveInner
  KFactThreeSevenTwoThree exists_component_not_centralizing starImg_eq_barInf)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem starImg_pCoreOf_inf_ne_bot (h : NineSettingGen G M p Q H E k)
    (hne : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) : starImg p H (pCoreOf 2 (H ⊓ M)) ≠ ⊥ :=
  fun hbot => hne (h.pCoreOf_inf_eq_of_le (h.le_relPPrimeCore_of_starImg_eq_bot
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left) hbot))

theorem o97Red (h : NineSettingGen G M 3 Q H E 2) (h3 : 3 ∉ sigmaM G M) :
    O97Red (StarGroup 3 H) (starImg 3 H E) (starImg 3 H M)
      (starImg 3 H (pCoreOf 2 (H ⊓ M))) := by
  obtain ⟨-, hEQ, hE, hEcard, hΓE⟩ := h.stdE
  obtain ⟨hHne, hQH, -⟩ := mem_HFam_iff.mp h.mem_H
  have h3S : 3 ∉ CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet, sigmaM] using h3
  exact o97Red_starImg h.setting.cstar hHne (hEQ.trans hQH) hE
    (by rw [hEcard]; norm_num) (hEQ.trans (QSet.le_of_mem h.mem_Q)) hΓE
    (h.setting.cstar.pRank_le_three_of_not_mem_sigmaSet h.setting.maxLocal Nat.prime_three
      (by norm_num) h3S)
    (h.nineFiveGen h3).1 (pCoreOf_isPGroup 2 (H ⊓ M))
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)) (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M))

end NineSettingGen

theorem nineSevenTwoInputGen_of_kFacts (hK35 : KFactThreeFiveInner)
    (hK37 : KFactThreeSevenTwoThree) : NineSevenTwoInputGen := by
  intro G _ _ M Q H E hnine _ h3 hne
  have hred := hnine.o97Red h3
  obtain ⟨L, hLc, hLM, hLcent⟩ := exists_component_not_centralizing hnine
    (pCoreOf_isPGroup 2 (H ⊓ M)) (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M))
    (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M)) (hnine.starImg_pCoreOf_inf_ne_bot hne)
  have hLcomp : CFSG.IsComponent (starImg 3 H L) := isComponent_starImg hLc
  have hLY : ¬ starImg 3 H L ≤ starImg 3 H M :=
    fun hle => hLM ((hnine.le_iff_starImg_le hLc.1).mpr hle)
  have hL : IsL34Type ↥(starImg 3 H L) ∨ IsA11Type ↥(starImg 3 H L) := by
    rcases hred.shape_k37 hK37 hLcomp hLY
        (fun hle => hLcent (Subgroup.le_centralizer_iff.mp hle))
        (hred.le_normalizer_E hLcomp hLY) (hred.le_normalizer_S hK35 hLcomp hLY) with
      ⟨h34, -⟩ | h11
    · exact Or.inl (IsL34Type.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := starImg 3 H L))) h34)
    · exact Or.inr (IsA11Type.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := starImg 3 H L))) h11)
  exact ⟨starImg 3 H L, hLcomp, by rwa [← starImg_eq_barInf], hL⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
