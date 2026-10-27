module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenRed
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightA
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSevenA
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Quot
import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenCF
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15 (starImgMulEquiv isElemAbelian_starImg_iff
  rankThreeGamma_starImg_le pPrimeCore_starGroup catalogSimpleSections_starGroup
  starImg_normalizes)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G}

namespace NineSettingGen

theorem exists_pComponent_not_centralizing {k : ℕ} (h : NineSettingGen G M p Q H E k)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSY : S ≤ H ⊓ M)
    (hSn : H ⊓ M ≤ Subgroup.normalizer (S : Set G)) (hSne : starImg p H S ≠ ⊥) :
    ∃ L : Subgroup G, IsPComponentIn p L H ∧ ¬ L ≤ M ∧
      ¬ starImg p H L ≤ Subgroup.centralizer
        ((starImg p H S : Subgroup (StarGroup p H)) : Set (StarGroup p H)) := by
  classical
  have hSH : S ≤ H := hSY.trans inf_le_left
  have hP := h.starImg_le_centralizer_pCore hS2 hSY
    (fun y hy s hs => (Subgroup.mem_normalizer_iff.mp (hSn hy) s).mp hs)
  have hex : ∃ L : Subgroup G, IsPComponentIn p L H ∧
      ¬ (∀ a ∈ S, ∀ l ∈ L, l * a * l⁻¹ ∈ S) ∧
      ¬ starImg p H L ≤ Subgroup.centralizer
        ((starImg p H S : Subgroup (StarGroup p H)) : Set (StarGroup p H)) := by
    by_contra hno
    have hL : ∀ L : Subgroup G, IsPComponentIn p L H →
        (∀ a ∈ S, ∀ l ∈ L, l * a * l⁻¹ ∈ S) ∨
          starImg p H L ≤ Subgroup.centralizer
            ((starImg p H S : Subgroup (StarGroup p H)) : Set (StarGroup p H)) := by
      intro L hL
      by_cases hN : ∀ a ∈ S, ∀ l ∈ L, l * a * l⁻¹ ∈ S
      · exact Or.inl hN
      · refine Or.inr ?_
        by_contra hC
        exact hno ⟨L, hL, hN, hC⟩
    exact hSne (h.starImg_eq_bot hSH hS2 hP hL)
  obtain ⟨L, hLcomp, hLnor, hLcent⟩ := hex
  refine ⟨L, hLcomp, ?_, hLcent⟩
  intro hLM
  apply hLnor
  intro a ha l hl
  exact (Subgroup.mem_normalizer_iff.mp (hSn ⟨hLcomp.1 hl, hLM hl⟩) a).mp ha

theorem nineSevenRed (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSY : S ≤ H ⊓ M)
    (hSn : H ⊓ M ≤ Subgroup.normalizer (S : Set G)) :
    NineSevenRed p (StarGroup p H) (starImg p H E) (starImg p H M) (starImg p H S) := by
  obtain ⟨-, hEQ, hE, hEcard, hΓE⟩ := h.stdE
  have hEH : E ≤ H := hEQ.trans h.Q_le_H
  have hEM : E ≤ M := hEQ.trans h.Q_le_M
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  have hX : CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) ≤ 3 :=
    h.pRank_star_le_three hH2 hp
  refine ⟨h.prime, h.ne_two, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact catalogSimpleSections_starGroup
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper h.setting.cstar.kProper H h.ne_top)
  · exact pPrimeCore_starGroup h.prime
  · exact (isElemAbelian_starImg_iff h.prime hEH hEp).mpr hE
  · rw [← Nat.card_congr (starImgMulEquiv h.prime hEH hEp).toEquiv, hEcard]
  · exact starImg_mono hEM
  · refine rankThreeGamma_starImg_le (k := 1) h.prime hEH hEp ?_
    intro D hDE hD
    exact inf_le_left.trans ((gamma_le_iff 1 p E M).mp hΓE D hDE hD)
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top).trans hX
  · intro T _ _
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top).trans hX
  · show IsPGroup 2 (starImg p H S)
    exact (hS2.comap_subtype (K := H)).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
  · exact starImg_mono (hSY.trans inf_le_right)
  · have hY : starImg p H (H ⊓ M) = starImg p H M := by
      unfold starImg
      rw [show (H ⊓ M).subgroupOf H = M.subgroupOf H from ?_]
      ext y
      simp only [Subgroup.mem_subgroupOf]
      exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
    rw [← hY]
    exact starImg_normalizes (S := S) (Y := H ⊓ M)
      (fun y hy s hs => (Subgroup.mem_normalizer_iff.mp (hSn hy) s).mp hs)

theorem fi22_of_pCoreOf_ne (hB5 : KFactThreeSevenTwoGe5) (h5c : KFactCenterRankFive)
    (h2c : KFactCenterRankTwo) (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) (h5 : 5 ≤ p) (hne : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    p = 5 ∧ ∃ L : Subgroup (StarGroup p H), CFSG.IsComponent L ∧ ¬ L ≤ starImg p H M ∧
      CFSG.AGLEmbedding.IsFi22 ↥L := by
  let S : Subgroup G := pCoreOf 2 (H ⊓ M)
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 (H ⊓ M)
  have hSY : S ≤ H ⊓ M := CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)
  have hSn : H ⊓ M ≤ Subgroup.normalizer (S : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 (H ⊓ M)
  have hSH : S ≤ H := hSY.trans inf_le_left
  have hSne : starImg p H S ≠ ⊥ := fun hbot =>
    hne (h.pCoreOf_inf_eq_of_le (h.le_relPPrimeCore_of_starImg_eq_bot hSH hbot))
  obtain ⟨L₀, hL₀, hL₀M, hL₀c⟩ := h.exists_pComponent_not_centralizing hS2 hSY hSn hSne
  have hred := h.nineSevenRed hH2 hp hS2 hSY hSn
  have hX := h.pRank_star_le_three hH2 hp
  have hL : CFSG.IsComponent (starImg p H L₀) := isComponent_starImg hL₀
  have hLY : ¬ starImg p H L₀ ≤ starImg p H M := fun hle =>
    hL₀M ((h.le_iff_starImg_le hL₀.1).mpr hle)
  have hSL : ¬ starImg p H S ≤
      Subgroup.centralizer ((starImg p H L₀ : Subgroup (StarGroup p H)) : Set (StarGroup p H)) :=
    fun hle => hL₀c (Subgroup.le_centralizer_iff.mp hle)
  have hEN := hred.le_normalizer_E hL hLY
  have hSN := hred.le_normalizer_S h5c h2c h5 hX hL hLY
  obtain ⟨hp5, hFi⟩ := hred.fi22_of_kFact hB5 h5 hL hLY hSL hEN hSN
  exact ⟨hp5, starImg p H L₀, hL, hLY, hFi⟩

end NineSettingGen

theorem five_le_pRank_three_of_fi22 (hFi : KFactFi22ThreeRank) {L : Subgroup (StarGroup p H)}
    (hL : CFSG.AGLEmbedding.IsFi22 ↥L) : 5 ≤ CFSG.Open.pRank 3 H := by
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let P : Subgroup ↥H := L.comap π
  have hφ : Function.Surjective (π.subgroupComap L) :=
    π.subgroupComap_surjective L (QuotientGroup.mk'_surjective _)
  have h5 : 5 ≤ CFSG.pRank 3 ↥(⊤ : Subgroup ↥P) := hFi ↥P ↥L hL (π.subgroupComap L) hφ
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h5
  have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) P.subtype P.subtype_injective
    (⊤ : Subgroup ↥P)
  have h2 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) H.subtype H.subtype_injective
    ((⊤ : Subgroup ↥P).map P.subtype)
  have h3 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
    (Subgroup.map_subtype_le ((⊤ : Subgroup ↥P).map P.subtype))
  omega

theorem nineSevenOne_of_kFacts (hB5 : KFactThreeSevenTwoGe5) (hFi : KFactFi22ThreeRank)
    (h5c : KFactCenterRankFive) (h2c : KFactCenterRankTwo) : NineSevenOne := by
  intro G _ _ M Q H E p h hH2 hp h5
  by_contra hne
  obtain ⟨-, L, -, -, hL⟩ := h.toGen.fi22_of_pCoreOf_ne hB5 h5c h2c hH2 hp h5 hne
  have h3 : CFSG.Open.pRank 3 H ≤ 3 := (h.pRank_le_of_mem_H2Fam hH2 hp).2.2
  have h5' := five_le_pRank_three_of_fi22 hFi hL
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
