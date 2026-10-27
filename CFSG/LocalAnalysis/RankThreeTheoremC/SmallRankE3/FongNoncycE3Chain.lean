module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4GammaA
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaE3Chain
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N5GammaCyc
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N5GammaStep4
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N5GammaTrans

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.GH74.Uniqueness.SU

section KGData

variable {G : Type} [Group G] [Finite G]

theorem pRank_three_le_of_twoLocal
    (hS : CFSG.LocalAnalysis.RankThreeTheoremC.Setting G) {H : Subgroup G}
    (hH : IsTwoLocal H) : CFSG.Open.pRank 3 H ≤ 3 := by
  have h3 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) H hH
  rw [hS.rank] at h3
  exact h3

theorem n4_false_of_kgData3_nc3 (hzj : CFSG.LocalAnalysis.RankFourTheoremC.KFactZJFactorizationGe)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix) (h2715 : KFact2715) (h131 : KFact131)
    (hpc : KFactParabolicCover) (h282 : KFact282) (h6n : KGStep6NoncycE3) (hT : KGTransvCent)
    (h241 : KFact2401ThreeOmega) {A : Type} [Group A] [Finite A] {p : ℕ}
    {H D S B L M : Subgroup A} {z : A} (d3 : KGC.KGData3 p H D S B L M z)
    (hG : KGC.KGStrongEmb p M z) (hH3 : CFSG.Open.pRank 3 H ≤ 3) : False := by
  haveI : (D.subgroupOf H).Normal := d3.toData.normal_subgroupOf
  have hchev := d3.chev_or_alt hzj
  have hc := KGQ.kgroup_step4 d3.toData.cfg (d3.toData.strong_img hG) hAutO hAutE h2024 h2401
    hAlt6 hchev
  by_cases hbot : KGC.img H D S ⊓ KGC.img H D L = ⊥
  · by_cases hcyc : IsCyclic ↥(KGC.img H D S)
    · haveI := hcyc
      exact KGSix.false_of_data hT h241 d3 hG hc hbot
    · exact h6n _ p _ _ _ _ _ d3.toData.cfg hc hbot hcyc
        (pRank_three_img_le L d3.toData.D_two hH3)
  · by_cases hsyl : CFSG.ABGLocalTools.IsSylowOf 2
        (KGC.img H D S ⊓ KGC.img H D L) (KGC.img H D L)
    · by_cases hB : fusionIsBenderGroup ↥(KGC.img H D L)
      · exact KGQ.false_of_bender_sylow d3.toData.cfg h2715 hsyl hB
      · exact KGFive.false_of_sylow h282 d3 hc hsyl hB
    · exact kgStep5Para_of_inputs h131 hpc _ p _ _ _ _ _ d3.toData.cfg (d3.toData.strongEmb_img hG)
        hc hbot hsyl

theorem n4_false_of_alpha_nc3 (hKF : KFact64iiL)
    (hzj : CFSG.LocalAnalysis.RankFourTheoremC.KFactZJFactorizationGe)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix) (h2715 : KFact2715) (h131 : KFact131)
    (hpc : KFactParabolicCover) (h282 : KFact282) (h6n : KGStep6NoncycE3) (hT : KGTransvCent)
    (h241 : KFact2401ThreeOmega) {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Setting G)
    (hsit : SmallRankSituation G p P M) (hp5 : 5 ≤ p) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {H S : Subgroup G} (hopt : Fail614OptimalGen p M x z H S)
    (hO : rankThreePrimeCore p H ≤ M)
    (hΩ : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z)
    (h2 : IsPGroup 2 (rankThreePrimeCore p H)) (hα : HasPrimeConstraint (G := M) p) : False := by
  obtain ⟨L, d3⟩ := n4_exists_kgData3 hKF hS hsit hp5 hx hz hopt hO hΩ h2
  exact n4_false_of_kgData3_nc3 hzj hAutO hAutE h2024 h2401 hAlt6 h2715 h131 hpc h282 h6n hT h241
    d3 (n4_strong_of_alpha hS hsit hz hα)
    (pRank_three_le_of_twoLocal hS hopt.ext.pair.isTwoLocal)

theorem n4_false_of_centralizing_nc3
    (hzj : CFSG.LocalAnalysis.RankFourTheoremC.KFactZJFactorizationGe)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix) (h2715 : KFact2715) (h131 : KFact131)
    (hpc : KFactParabolicCover) (h282 : KFact282) (h6n : KGStep6NoncycE3) (hT : KGTransvCent)
    (h241 : KFact2401ThreeOmega) {p : ℕ} {H D S B L M : Subgroup G} {z : G} (hp2 : p ≠ 2)
    (d : KGData3Pre p H D S B L M z) (hH3 : CFSG.Open.pRank 3 H ≤ 3) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbL : ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ D)
    (hbS : ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ D)
    (hγ : CFSG.HallHigman.IsPSolvable p ↥(M ⊓ centralizer ({b} : Set G))) : False := by
  haveI : Fact p.Prime := ⟨d.prime⟩
  have hbH : b ∈ H := d.B_le_H hbB
  obtain ⟨hBc, hBp⟩ := SU1.isElemAbelian_iff.mp d.B_elem
  have hbo : orderOf b = p := orderOf_eq_prime (hBp b hbB) hb1
  set C : Subgroup G := H ⊓ centralizer ({b} : Set G) with hC
  set Gs : Subgroup G := D ⊔ C with hGs
  have hCH : C ≤ H := inf_le_left
  have hGH : Gs ≤ H := sup_le d.D_le_H hCH
  have hDGs : D ≤ Gs := le_sup_left
  have hCGs : C ≤ Gs := le_sup_right
  have hdec : ∀ {w : G}, w ∈ H → (∃ d₀ ∈ D, ∃ c ∈ centralizer ({b} : Set G), w = d₀ * c) →
      w ∈ Gs := by
    rintro w hwH ⟨d₀, hd₀, c, hc, rfl⟩
    have hcH : c ∈ H := by
      have : d₀⁻¹ * (d₀ * c) ∈ H := H.mul_mem (H.inv_mem (d.D_le_H hd₀)) hwH
      simpa using this
    exact Gs.mul_mem (hDGs hd₀) (hCGs (show c ∈ C from ⟨hcH, hc⟩))
  have hL : L ≤ Gs := fun l hl =>
    hdec (d.L_le_H hl) (n4_exists_mul_centralizer hp2 d.D_le_H d.H_le_D d.D_two hbH hbo
      (d.L_le_H hl) (hbL l hl))
  have hS : S ≤ Gs := fun s hs =>
    hdec (d.S_le_H hs) (n4_exists_mul_centralizer hp2 d.D_le_H d.H_le_D d.D_two hbH hbo
      (d.S_le_H hs) (hbS s hs))
  have hB : B ≤ Gs := fun b' hb' => by
    exact hCGs (show b' ∈ C from ⟨d.B_le_H hb',
      Subgroup.mem_centralizer_singleton_iff.mpr (hBc b hbB b' hb').symm⟩)
  have hzB : z ∈ B := d.z_mem_B
  have hstrong : ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → ∀ Y : Subgroup ↥Gs, Y ≤ M.subgroupOf Gs →
      (⟨z, hB hzB⟩ : ↥Gs) ∈ Y → S622IsSimpleSection Y (rankThreePrimeCore p Y) →
      f ∣ (rankThreePrimeCore p Y).relIndex Y →
      CFSG.Open.GLBStronglyEmbedded f (M.subgroupOf Gs) := by
    intro f _ _ _ Y hYM hzY hsec _
    exfalso
    haveI hDn : (D.subgroupOf Gs).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDGs).mpr (hGH.trans d.H_le_D)
    have hD2 : IsPGroup 2 (D.subgroupOf Gs) :=
      d.D_two.of_equiv (Subgroup.subgroupOfEquivOfLe hDGs).symm
    have hCM : (M ⊓ H ⊓ centralizer ({b} : Set G)) ≤ M ⊓ centralizer ({b} : Set G) :=
      fun x hx => ⟨hx.1.1, hx.2⟩
    have hCGs' : (M ⊓ H ⊓ centralizer ({b} : Set G)) ≤ Gs := fun x hx =>
      hCGs (show x ∈ C from ⟨hx.1.2, hx.2⟩)
    have hCs : CFSG.HallHigman.IsPSolvable p ↥((M ⊓ H ⊓ centralizer ({b} : Set G)).subgroupOf Gs) :=
      n4_pSolvable_subgroupOf hCM hCGs' hγ
    refine n4_no_simple_section (p := p) hp2 (D := D.subgroupOf Gs)
      (C := (M ⊓ H ⊓ centralizer ({b} : Set G)).subgroupOf Gs) (Y := Y) hD2 hCs ?_ hzY ?_ hsec
    · intro y hy
      have hyM : (y : G) ∈ M := hYM hy
      obtain ⟨d₀, hd₀, c₀, hc₀, hyc⟩ := (n4_mem_sup_iff d.D_le_H hCH d.H_le_D).mp y.2
      have hc₀M : c₀ ∈ M := by
        have : d₀⁻¹ * (y : G) ∈ M := M.mul_mem (M.inv_mem (d.D_le_M hd₀)) hyM
        rw [hyc] at this
        simpa using this
      refine ⟨⟨d₀, hDGs hd₀⟩, hd₀, ⟨c₀, hCGs hc₀⟩, ⟨⟨hc₀M, hc₀.1⟩, hc₀.2⟩, ?_⟩
      exact Subtype.ext hyc
    · rw [Subgroup.orderOf_mk]
      exact d.z_order
  have d3 := d.restrict hGH hDGs hS hB hL
  have hGs3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Gs) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Gs]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) hGH).trans hH3
  exact n4_false_of_kgData3_nc3 hzj hAutO hAutE h2024 h2401 hAlt6 h2715 h131 hpc h282 h6n hT h241
    d3 hstrong hGs3

theorem slotP614GammaE3U0_of_fieldAut_nc3 (hfield : SlotP614GammaFieldAutE3U0)
    (hβ : NoTwoComponentsGen) (hγc : N3.GammaCentP) (hKF : KFact64iiL)
    (hzj : CFSG.LocalAnalysis.RankFourTheoremC.KFactZJFactorizationGe)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix) (h2715 : KFact2715) (h131 : KFact131)
    (hpc : KFactParabolicCover) (h282 : KFact282) (h6n : KGStep6NoncycE3) (hT : KGTransvCent)
    (h241 : KFact2401ThreeOmega) : SlotP614GammaE3U0 := by
  intro G _ _ hS hD1 hU0 p hp5 P M hsit x z hx hz H S hopt hO hΩ h2 hcon
  obtain ⟨L, d⟩ := n4_exists_kgData3Pre hKF hS hsit hp5 hx hz hopt hO hΩ h2
  by_cases hb : ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
      (∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ rankThreePrimeCore p H) ∧
      (∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ rankThreePrimeCore p H)
  · obtain ⟨b, hbB, hbZ, hbL, hbS⟩ := hb
    have hb1 : b ≠ 1 := fun h => hbZ (h ▸ one_mem _)
    exact n4_false_of_centralizing_nc3 hzj hAutO hAutE h2024 h2401 hAlt6 h2715 h131 hpc h282 h6n
      hT h241 (sigmaA_odd p hsit.mem_sigmaA) d (pRank_three_le_of_twoLocal hS
        hopt.ext.pair.isTwoLocal) hbB hb1 hbL hbS
      (n4_pSolvable_centralizer_of_gammaCent hγc hβ hS hsit hp5 hcon hx hz hbB hbZ)
  · exact hfield G hS hD1 hU0 p hp5 P M hsit x z hx hz H S L hopt hO h2 hcon d
      fun b hbB hbZ hh => hb ⟨b, hbB, hbZ, hh.1, hh.2⟩

end KGData

section Gamma

theorem n5_false_of_kgData3_E3_nc3
    (hzj : CFSG.LocalAnalysis.RankFourTheoremC.KFactZJFactorizationGe)
    (hAutO : KFactAutAltOrder) (h2715 : KFact2715) (h131 : KFact131) (h282 : KFact282)
    (h6n : KGStep6NoncycE3) (hT : KGTransvCent) (hPara : KFactGammaParaE3)
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp2 : p ≠ 2) {H D S B L M : Subgroup G} {z : G}
    [hDn : (D.subgroupOf H).Normal] (d3 : KGC.KGData3 p H D S B L M z)
    (hrk : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → CFSG.Open.pRank ℓ (KGC.img H D L) ≤ 3)
    (hfield : ∀ b ∈ B, b ∉ zpowers z →
      ¬ ((∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ D) ∧ (∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ D)))
    (hcent : ∀ b ∈ B, b ∉ zpowers z →
      CFSG.HallHigman.IsPSolvable p ↥(M ⊓ centralizer ({b} : Set G))) : False := by
  haveI : Fact p.Prime := ⟨d3.toData.prime⟩
  have hnb := n5_hnb d3 hfield
  have hchev := d3.chev_or_alt hzj
  have hc := n5_kgroup_step4 d3.toData.cfg hnb hAutO hchev
  by_cases hbot : KGC.img H D S ⊓ KGC.img H D L = ⊥
  · by_cases hcyc : IsCyclic ↥(KGC.img H D S)
    · haveI := hcyc
      exact n5_false_of_cyclic hT d3 hc hbot hnb
    · exact h6n _ p _ _ _ _ _ d3.toData.cfg hc hbot hcyc (hrk 3 Nat.prime_three (by norm_num))
  · by_cases hsyl : CFSG.ABGLocalTools.IsSylowOf 2
        (KGC.img H D S ⊓ KGC.img H D L) (KGC.img H D L)
    · by_cases hB : fusionIsBenderGroup ↥(KGC.img H D L)
      · exact KGQ.false_of_bender_sylow d3.toData.cfg h2715 hsyl hB
      · exact KGFive.false_of_sylow h282 d3 hc hsyl hB
    · refine n5_false_of_not_sylow_E3 d3.toData.cfg hc.1 h131 hbot hsyl hPara hnb hrk ?_
      intro y hy hyz
      obtain ⟨y', hy'B, rfl⟩ := KGC.mem_img.mp hy
      have hy'z : (y' : G) ∉ zpowers z := by
        intro hmem
        obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hmem
        apply hyz
        have hyeq : y' = (⟨z, d3.toData.z_mem_H⟩ : ↥H) ^ i := Subtype.ext (by simpa using hi.symm)
        rw [hyeq, map_zpow]
        exact zpow_mem_zpowers _ i
      have hy'1 : (y' : G) ≠ 1 := by
        intro h1
        apply hyz
        have : y' = 1 := Subtype.ext h1
        rw [this, map_one]
        exact one_mem _
      have hy'o : orderOf (y' : G) = p :=
        orderOf_eq_prime (d3.toData.B_elem.2 _ hy'B) hy'1
      exact n5_pSolvable_img hp2 d3.toData.D_le_H d3.toData.H_le_D d3.toData.D_two
        d3.toData.D_le_M y'.2 hy'o (hcent _ hy'B hy'z)

theorem slotP614GammaFieldAutE3U0_of_facts_E3_nc3 (hβ : NoTwoComponentsGen)
    (hγc : N3.GammaCentP) (hzj : CFSG.LocalAnalysis.RankFourTheoremC.KFactZJFactorizationGe)
    (hAutO : KFactAutAltOrder) (h2715 : KFact2715) (h131 : KFact131) (h282 : KFact282)
    (h6n : KGStep6NoncycE3) (hT : KGTransvCent) (hPara : KFactGammaParaE3) :
    SlotP614GammaFieldAutE3U0 := by
  intro G _ _ hS hD1 hU0 p hp5 P M hsit x z hx hz H S L hopt hO h2 hcon d hfield
  have d3 := d.toKGData3
  haveI : ((rankThreePrimeCore p H).subgroupOf H).Normal := d3.toData.normal_subgroupOf
  exact n5_false_of_kgData3_E3_nc3 hzj hAutO h2715 h131 h282 h6n hT hPara (by omega) d3
    (n5_pRank_img_le_three hS L hopt.ext.pair.isTwoLocal h2) hfield
    (fun b hbB hbZ => n4_pSolvable_centralizer_of_gammaCent hγc hβ hS hsit hp5 hcon hx hz hbB hbZ)

end Gamma

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
