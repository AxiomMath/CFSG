module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11GammaTwoSet
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixStar
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Quasithin.Background.RonanE111Sub
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Fixed
import CFSG.RankThree.PartTwo.Sec14.Ronan148RH2Inner
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55
import CFSG.GH74.Constrained
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C

private theorem eq_one_of_mem_centralizer_of_pow_three {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hZ : Subgroup.center L = ⊥) {c : X}
    (hLrank : 3 ≤ CFSG.Open.pRank 3 L)
    (hranktop : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    (hc : c ∈ Subgroup.centralizer (L : Set X)) (hc3 : c ^ 3 = 1) : c = 1 := by
  by_contra hcne
  have hcC : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_iff.mp hc l hl
  have hcL : c ∉ L := by
    intro hcL
    have hcenter : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcC g g.2)
    rw [hZ, Subgroup.mem_bot] at hcenter
    exact hcne (congrArg Subtype.val hcenter)
  have hdisj : L ⊓ Subgroup.zpowers c = ⊥ := by
    rw [inf_comm]
    exact CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.zpowers_inf_eq_bot
      Nat.prime_three hc3 hcL
  have hcop : Nat.Coprime 3 (Nat.card (L ⊓ Subgroup.zpowers c : Subgroup X)) := by
    rw [hdisj]
    simp
  have hcomm : ∀ a ∈ L, ∀ b ∈ Subgroup.zpowers c, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr hc hb) a ha
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hcne
  have hrankc : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers c) := by
    have hcard : Nat.card (Subgroup.zpowers c) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hcord]
      norm_num
    exact CFSG.SectionRank.le_pRank (p := 3) (k := 1) (by norm_num) le_rfl
      (CFSG.Open.isElemAbelian_zpowers hc3) (by simpa using hcard)
  have hsum := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
    (q := 3) Nat.prime_three (A := L) (B := Subgroup.zpowers c) hcomm hcop
  have hmono := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num : 1 < 3)
    (le_top : L ⊔ Subgroup.zpowers c ≤ (⊤ : Subgroup X))
  omega

private theorem component_unique_and_normal {X : Type} [Group X] [Finite X]
    (hK : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore 3 X = ⊥) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLrank : 3 ≤ CFSG.Open.pRank 3 L)
    (hranktop : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) : L.Normal := by
  have huniq : ∀ I : Subgroup X, CFSG.IsComponent I → I = L := by
    intro I hI
    by_contra hne
    have h := pRank_add_one_le_of_ne hK hO hI hL hne
    omega
  refine Subgroup.Normal.mk fun l hl x => ?_
  have hmap : L.map (MulAut.conj x).toMonoidHom = L :=
    huniq _ (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hL)
  have hxN : x ∈ Subgroup.normalizer (L : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  exact (Subgroup.mem_normalizer_iff.mp hxN l).mp hl

private theorem starImg_isElemAbelian_card_nine {G : Type} [Group G] [Finite G]
    {M Q H E : Subgroup G} (hT : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q) :
    IsElemAbelian 3 (starImg 3 H E) ∧ Nat.card (starImg 3 H E) = 9 := by
  obtain ⟨-, hEQ, hEab, hEcard, -⟩ := hT.stdE
  have hEH : E ≤ H := hEQ.trans (mem_H2Fam_iff.mp hH2).2.1
  have hEp : IsPGroup 3 E := hEab.isPGroup
  constructor
  · exact (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.isElemAbelian_starImg_iff
      Nat.prime_three hEH hEp).mpr hEab
  · rw [CFSG.LocalAnalysis.RankThreeUC.AGL81C.card_starImg_eq Nat.prime_three hEH hEp,
      hEcard]
    norm_num

private theorem gamma_barInf_of_stdE {G : Type} [Group G] [Finite G]
    {M Q H E : Subgroup G} (hT : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q) :
    CFSG.Open.rankThreeGamma 1 3 (starImg 3 H E) ≤ barInf 3 M H := by
  obtain ⟨-, hEQ, hEab, -, hΓ⟩ := hT.stdE
  have hEH : E ≤ H := hEQ.trans (mem_H2Fam_iff.mp hH2).2.1
  have hEp : IsPGroup 3 E := hEab.isPGroup
  have hΓ' : CFSG.Open.rankThreeGamma 1 3 E ≤ M := by simpa using hΓ
  have hM : ∀ D : Subgroup G, D ≤ E → 1 ≤ CFSG.Open.pRank 3 D →
      Subgroup.normalizer (D : Set G) ⊓ H ≤ M := by
    intro D hDE hD
    have hgamma : CFSG.RankThree.PartTwo.gamma 1 E ≤ M := hΓ'
    have hle : Subgroup.normalizer (D : Set G) ≤ M :=
      (CFSG.RankThree.PartTwo.gamma_le_iff (k := 1) (A := E) (M := M)).mp
        hgamma D hDE hD
    exact inf_le_left.trans hle
  have hΓstar : CFSG.Open.rankThreeGamma 1 3 (starImg 3 H E) ≤ starImg 3 H M :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.rankThreeGamma_starImg_le
      (p := 3) (k := 1) (B := E) (M := M) (H := H) Nat.prime_three hEH hEp hM
  simpa [CFSG.LocalAnalysis.AGL81TheoremCD.Section15.starImg_eq_barInf] using hΓstar

private theorem normalizer_le_barInf {X : Type} [Group X] [Finite X]
    (Ebar Mbar : Subgroup X) (hEab : IsElemAbelian 3 Ebar)
    (hΓbar : CFSG.Open.rankThreeGamma 1 3 Ebar ≤ Mbar) :
    ∀ B : Subgroup X, B ≤ Ebar → B ≠ ⊥ →
      Subgroup.normalizer (B : Set X) ≤ Mbar := by
  intro B hB hBne
  have hBpos : 1 ≤ CFSG.Open.pRank 3 B := by
    have hBab : IsElemAbelian 3 B := hEab.mono hB
    letI : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
    obtain ⟨x, hxne⟩ := exists_ne (1 : ↥B)
    have hx3 : (x : X) ^ 3 = 1 := hBab.2 (x : X) x.2
    have hxord : orderOf (x : X) = 3 := orderOf_eq_prime hx3 (by
      intro hx1
      exact hxne (Subtype.ext hx1))
    have hcard : Nat.card (Subgroup.zpowers (x : X)) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hxord]
      norm_num
    exact CFSG.SectionRank.le_pRank (p := 3) (k := 1) (by norm_num)
      (Subgroup.zpowers_le.mpr x.2) (CFSG.Open.isElemAbelian_zpowers hx3)
      (by simpa using hcard)
  exact (CFSG.RankThree.PartTwo.normalizer_le_gamma hB hBpos).trans hΓbar

private theorem starImg_le_component {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hLrank : 3 ≤ CFSG.Open.pRank 3 L)
    (hranktop : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) (hLnormal : L.Normal)
    (Ebar : Subgroup X) (hEab : IsElemAbelian 3 Ebar)
    (e : ↥L ≃* alternatingGroup (Fin 11)) : Ebar ≤ L := by
  have hZ : Subgroup.center L = ⊥ :=
    CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
      (by norm_num : 4 ≤ 11) e
  have hcube : CFSG.RankThree.PartTwo.Sec4.CubeInner ↥L :=
    CFSG.RankThree.PartTwo.Sec4.CubeInner.of_mulEquiv
      (CFSG.RankThree.PartTwo.Sec4.cubeInner_of_not_three_dvd_card_outer
        (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup 11 (by norm_num) 3
          Nat.prime_three (by norm_num))) e
  intro x hx
  have hx3 : x ^ 3 = 1 := hEab.2 x hx
  have hxN : x ∈ Subgroup.normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLnormal]
    exact Subgroup.mem_top x
  obtain ⟨r, hrL, hr3, hconj⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148R.exists_inner_rep hZ hcube hxN hx3
  let c : X := r⁻¹ * x
  have hcC : c ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hxl : x * l = (r * l * r⁻¹) * x := by
      rw [← hconj l hl]
      group
    have hcl : c * l = l * c := by
      calc c * l = r⁻¹ * (x * l) := by simp [c, mul_assoc]
        _ = r⁻¹ * ((r * l * r⁻¹) * x) := by rw [hxl]
        _ = l * (r⁻¹ * x) := by group
        _ = l * c := by simp [c]
    exact hcl.symm
  have hcomm_rc : Commute r c := Subgroup.mem_centralizer_iff.mp hcC r hrL
  have hx_eq : x = r * c := by
    show x = r * (r⁻¹ * x)
    group
  have hc3 : c ^ 3 = 1 := by
    have h : (r * c) ^ 3 = 1 := by rwa [← hx_eq]
    rw [hcomm_rc.mul_pow, hr3, one_mul] at h
    exact h
  have hc1 : c = 1 := eq_one_of_mem_centralizer_of_pow_three hZ hLrank hranktop hcC hc3
  rw [hx_eq, hc1, mul_one]
  exact hrL

private theorem normalizer_subgroupOf_le {X : Type} [Group X] [Finite X]
    {L Ebar Mbar : Subgroup X} (hEsubL : Ebar ≤ L)
    (hNorm : ∀ B : Subgroup X, B ≤ Ebar → B ≠ ⊥ →
      Subgroup.normalizer (B : Set X) ≤ Mbar) :
    ∀ F₀ : Subgroup ↥L, F₀ ≤ Ebar.subgroupOf L → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set ↥L) ≤ Mbar.subgroupOf L := by
  intro F₀ hF₀le hF₀ne y hy
  have hmaple : F₀.map L.subtype ≤ Ebar := by
    rw [Subgroup.map_le_iff_le_comap]
    exact hF₀le
  have hmapsne : F₀.map L.subtype ≠ ⊥ := by
    intro hbot
    exact hF₀ne ((Subgroup.map_eq_bot_iff_of_injective F₀ (f := L.subtype)
      L.subtype_injective).mp hbot)
  have hyN : (y : X) ∈ Subgroup.normalizer (F₀.map L.subtype : Set X) :=
    (CFSG.Quasithin.RonanE111.mem_normalizer_map_subtype_iff F₀ y).mp hy
  exact hNorm (F₀.map L.subtype) hmaple hmapsne hyN

private theorem five_dvd_card_a11TwoSetStab {i j : Fin 11} (hij : i ≠ j) :
    5 ∣ Nat.card (a11TwoSetStab i j) := by
  have hA11 : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hcard := Subgroup.card_mul_index (H := a11TwoSetStab i j)
  rw [a11TwoSetStab_index hij, hA11] at hcard
  have h : Nat.card (a11TwoSetStab i j) = 362880 := by omega
  rw [h]
  norm_num

private theorem five_dvd_barInf_of_kFact {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (e : ↥L ≃* alternatingGroup (Fin 11))
    (Mbar : Subgroup X) (hLnotle : ¬ L ≤ Mbar)
    (Ebar : Subgroup X) (hEab : IsElemAbelian 3 Ebar) (hEcard : Nat.card Ebar = 9)
    (hEsubL : Ebar ≤ L)
    (hcond : ∀ F₀ : Subgroup ↥L, F₀ ≤ Ebar.subgroupOf L → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set ↥L) ≤ Mbar.subgroupOf L) :
    5 ∣ Nat.card Mbar := by
  let Y : Subgroup ↥L := Mbar.subgroupOf L
  let F : Subgroup ↥L := Ebar.subgroupOf L
  have hFcard : Nat.card F = 9 := by
    have h1 : Nat.card F = Nat.card Ebar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEsubL).toEquiv
    rw [h1, hEcard]
  have hFabel : IsElemAbelian 3 F := hEab.subgroupOf L
  have hmain := KFactA11GammaTwoSet.of_mulEquiv kFactA11GammaTwoSet_holds e
    F Y hFabel hFcard hcond
  rcases hmain with hYtop | ⟨i, j, hij, hYmap⟩
  · have hLM : L ≤ Mbar := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥L) ∈ Y := by
        rw [hYtop]
        exact Subgroup.mem_top _
      exact hx'
    exact absurd hLM hLnotle
  · have h5stab : 5 ∣ Nat.card (a11TwoSetStab i j) := five_dvd_card_a11TwoSetStab hij
    have hcardYmap : Nat.card (Y.map e.toMonoidHom) = Nat.card Y :=
      Subgroup.card_map_of_injective e.injective
    have h5Y : 5 ∣ Nat.card Y := by
      rw [← hcardYmap, hYmap]
      exact h5stab
    have hYeq : Y = (Mbar ⊓ L).subgroupOf L := by
      ext z
      change (z : X) ∈ Mbar ↔ (z : X) ∈ Mbar ⊓ L
      rw [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h, z.2⟩, fun h => h.1⟩
    have hcardY : Nat.card Y = Nat.card (Mbar ⊓ L : Subgroup X) := by
      rw [hYeq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Mbar ⊓ L ≤ L)).toEquiv
    rw [hcardY] at h5Y
    exact h5Y.trans (Subgroup.card_dvd_of_le
      (inf_le_left : Mbar ⊓ L ≤ Mbar))

theorem threeFiveA11InputGen_holds :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.ThreeFiveA11InputGen := by
  intro G _ _ M Q H E hT hH2 h3
  rintro ⟨L, hLcomp, hLnotle, ⟨e⟩⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := ↥H ⧸ CFSG.pPrimeCore 3 ↥H
  let Ebar : Subgroup X := starImg 3 H E
  let Mbar : Subgroup X := barInf 3 M H
  have hK : CFSG.Open.IsKGroup X :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen.isKGroup_quotient hT 3
  have hO : CFSG.pPrimeCore 3 X = ⊥ :=
    CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot (↥H) 3
  have hranktop : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup X)]
    exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen.pRank_quotient_le_three_of_mem_H2Fam
      hT hH2 h3
  have hLrank : 3 ≤ CFSG.Open.pRank 3 L :=
    CFSG.AGLEmbeddingD2.AltDegree.three_le_pRank_of_mulEquiv_alternating
      Nat.prime_three (by norm_num) (by norm_num : 3 * 3 ≤ 11) e
  have hLnormal : L.Normal :=
    component_unique_and_normal hK hO hLcomp hLrank hranktop
  obtain ⟨hEab0, hEcard0⟩ := starImg_isElemAbelian_card_nine hT hH2
  have hEab : IsElemAbelian 3 Ebar := hEab0
  have hEcard : Nat.card Ebar = 9 := hEcard0
  have hΓbar0 : CFSG.Open.rankThreeGamma 1 3 (starImg 3 H E) ≤ barInf 3 M H :=
    gamma_barInf_of_stdE hT hH2
  have hΓbar : CFSG.Open.rankThreeGamma 1 3 Ebar ≤ Mbar := hΓbar0
  have hNorm := normalizer_le_barInf Ebar Mbar hEab hΓbar
  have hEsubL : Ebar ≤ L :=
    starImg_le_component hLrank hranktop hLnormal Ebar hEab e
  have hcond := normalizer_subgroupOf_le hEsubL hNorm
  have hLnotle' : ¬ L ≤ Mbar := hLnotle
  change 5 ∣ Nat.card Mbar
  exact five_dvd_barInf_of_kFact e Mbar hLnotle' Ebar hEab hEcard hEsubL hcond

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
