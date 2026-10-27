module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.StrongEmbedInput
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CThreeComponents
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixStarEGen
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.Walter.Bender1970.S3.TransitivitySetup
import CFSG.GroupTheory.CoprimeQuotientNormalizer
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.Prop95Iii
import CFSG.RankThree.PartOne.S8.ResidualBound
import CFSG.GroupTheory.RegularModuleThree
import CFSG.GroupTheory.SylowNormalIndex
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
import CFSG.LocalAnalysis.RankThreeUC.Notation
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem normalizer_le_M_of_mem_sigmaSet (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M) {F : Subgroup G}
    (hF : IsPGroup d F) (hFM : F ≤ M) (hF1 : F ≠ ⊥) :
    Subgroup.normalizer (F : Set G) ≤ M := by
  haveI : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  obtain ⟨-, -, hstr⟩ := isStronglyPEmbedded_of_twelveCtx' h hns d hd
  obtain ⟨n, hn⟩ := hF.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hF1 (Subgroup.card_eq_one.mp hn)
  have hdF : d ∣ Nat.card F := by
    rw [hn]
    exact dvd_pow_self d hn0
  intro g hg
  by_contra hgM
  have hFg : F ≤ M.map (MulAut.conj g).toMonoidHom := by
    have hmap : F.map (MulAut.conj g).toMonoidHom = F :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hle : F.map (MulAut.conj g).toMonoidHom ≤ M.map (MulAut.conj g).toMonoidHom :=
      Subgroup.map_mono hFM
    rwa [hmap] at hle
  exact hstr g hgM (hdF.trans (Subgroup.card_dvd_of_le (le_inf hFM hFg)))

theorem isSylowOf_H_of_isSylowOf_inf (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf d D H := by
  haveI : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hD.le.trans inf_le_left, hD.isPGroup, ?_⟩
  intro hdvd
  obtain ⟨S, hDS⟩ := (hD.isPGroup.comap_subtype (K := H)).exists_le_sylow
  have hD₁ : CFSG.ABGLocalTools.IsSylowOf d ((S : Subgroup H).map H.subtype) H := ⟨S, rfl⟩
  have hDD₁ : D ≤ (S : Subgroup H).map H.subtype := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hD.le.trans inf_le_left hx⟩, hDS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hne : D ≠ (S : Subgroup H).map H.subtype := by
    intro heq
    exact ((CFSG.ABGLocalTools.isSylowOf_iff.mp (heq ▸ hD₁)).2.2) hdvd
  have hlt : D < (S : Subgroup H).map H.subtype := lt_of_le_of_ne hDD₁ hne
  have hgrow := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hD₁.isPGroup hlt
  have hND : (S : Subgroup H).map H.subtype ⊓ Subgroup.normalizer (D : Set G) ≤ M :=
    inf_le_right.trans (normalizer_le_M_of_mem_sigmaSet h hns hd hD.isPGroup
      (hD.le.trans inf_le_right) hD1)
  have hQK : (S : Subgroup H).map H.subtype ⊓ Subgroup.normalizer (D : Set G) ≤ H ⊓ M :=
    le_inf (inf_le_left.trans hD₁.le) hND
  have heq := CFSG.ABGLocalTools.IsSylowOf.eq_of_le hD hgrow.le hQK
    (hD₁.isPGroup.to_le inf_le_left)
  exact hgrow.ne' heq

theorem not_dvd_card_primeComplementCore_of_twelveCtx (h : TwelveCtx G M p Q H) {d : ℕ}
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) :
    ¬ d ∣ Nat.card (primeComplementCore (G := ↥H) p) := by
  intro hdvd
  apply hXM
  have hcard : Nat.card (primeComplementCore (G := ↥H) p) = Nat.card (relPPrimeCore p H) := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
      h.p_prime H, Subgroup.card_map_of_injective H.subtype_injective]
  rw [hcard] at hdvd
  exact hdvd.trans (Subgroup.card_dvd_of_le (le_inf (relPPrimeCore_le_xSub h.p_prime M H)
    (relPPrimeCore_le_M_of_twelveCtx h)))

theorem starImg_ne_bot_of_not_dvd {d : ℕ} (hd : d.Prime)
    (hO : ¬ d ∣ Nat.card (primeComplementCore (G := ↥H) p)) {D : Subgroup G} (hDH : D ≤ H)
    (hD : IsPGroup d D) (hD1 : D ≠ ⊥) : starImg p H D ≠ ⊥ := by
  haveI : Fact d.Prime := ⟨hd⟩
  intro hbot
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  have hle : D.subgroupOf H ≤ O := by
    have hmap : (D.subgroupOf H).map (QuotientGroup.mk' O) = ⊥ := hbot
    simpa [O, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff (D.subgroupOf H)).mp hmap
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hD1 (Subgroup.card_eq_one.mp hn)
  have hcard : Nat.card (D.subgroupOf H) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
  have hdvdO : d ∣ Nat.card O := by
    have h1 : d ∣ Nat.card (D.subgroupOf H) := by
      rw [hcard, hn]
      exact dvd_pow_self d hn0
    exact h1.trans (Subgroup.card_dvd_of_le hle)
  exact hO (by simpa [O] using hdvdO)

theorem isSylowOf_starImg_top_of_prime {d : ℕ} (hd : d.Prime) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D H) :
    CFSG.ABGLocalTools.IsSylowOf d (starImg p H D) ⊤ := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨Q, hQ⟩ := hD
  let π : ↥H →* StarGroup p H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let Q' : Sylow d (StarGroup p H) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
  refine ⟨Q'.subtype le_top, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_top]
  have hQH : ((Q : Subgroup ↥H).map H.subtype).subgroupOf H = (Q : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [Sylow.coe_mapSurjective]
  calc (Q : Subgroup ↥H).map π
      = ((((Q : Subgroup ↥H).map H.subtype).subgroupOf H).map π) := by rw [hQH]
    _ = (D.subgroupOf H).map π := by rw [hQ]
    _ = starImg p H D := rfl

private theorem starImg_map_subtype (p : ℕ) (A : Subgroup ↥H) :
    starImg p H (A.map H.subtype) =
      A.map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
  simp only [starImg, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

theorem starImg_normalizer_eq_of_not_dvd {d : ℕ} (hd : d.Prime)
    (hO : ¬ d ∣ Nat.card (primeComplementCore (G := ↥H) p)) {D : Subgroup G} (hDH : D ≤ H)
    (hD : IsPGroup d D) :
    Subgroup.normalizer (starImg p H D : Set (StarGroup p H)) =
      starImg p H (Subgroup.normalizer (D : Set G) ⊓ H) := by
  haveI : Fact d.Prime := ⟨hd⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hD' : IsPGroup d (D.subgroupOf H) := hD.comap_subtype (K := H)
  have h := CFSG.GroupTheory.normal_coprime_quotient_normalizer d O hO (D.subgroupOf H) hD'
  have hleft : (D.subgroupOf H).map π = starImg p H D := rfl
  rw [hleft] at h
  rw [← h]
  rw [← starImg_map_subtype p
    (Subgroup.normalizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H))]
  rw [← Subgroup.subgroupOf_normalizer_eq hDH]
  rw [← Subgroup.inf_subgroupOf_right]
  rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]

theorem le_M_and_normalizer_le_of_le (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    {E : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) {R : Subgroup G} (hR : IsPGroup p R) (hER : E ≤ R) :
    R ≤ M ∧ Subgroup.normalizer (R : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  have hgen : NineSettingGen G M p Q H E 2 := nineSettingGen h hEQ hE hEc hΓ
  have hp : p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := h.p_not_mem_sigma
  have hU : NineNineOne M p := hI G M Q H E p hgen hp
  have hEM : E ≤ M := hEQ.trans h.Q_le_M
  have hnorm : ∀ {Y : Subgroup G}, E ≤ Y → Y ≤ M →
      Subgroup.normalizer (Y : Set G) ≤ M := fun hEY hYM =>
    NineNineOne.normalizer_le h.maxLocal hU hEM hE hEc hΓ hEY hYM
  have hRM : R ≤ M := by
    by_contra hRM
    have hlt : R ⊓ M < R := lt_of_le_of_ne inf_le_left fun heq => hRM (inf_eq_left.mp heq)
    have hgrow := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hR hlt
    have hle : R ⊓ Subgroup.normalizer (R ⊓ M : Set G) ≤ M :=
      inf_le_right.trans (hnorm (le_inf hER hEM) inf_le_right)
    exact hgrow.not_ge (le_inf inf_le_left hle)
  exact ⟨hRM, hnorm hER hRM⟩

theorem isKGroupCat_of_starGroup (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (h : TwelveCtx G M p Q H) (N : Subgroup (StarGroup p H)) (K : Subgroup ↥N) :
    CFSG.SectionRank.IsKGroupCat ↥K := by
  have hopen : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper h.H_ne_top
  have hcat : CFSG.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.isKGroup_catalog_of_open hopen
  have hH : CFSG.SectionRank.IsKGroupCat ↥H :=
    CFSG.RankThree.PartOne.isKGroupCat_of_isKGroup hbridge hcat
  have hstar : CFSG.SectionRank.IsKGroupCat (StarGroup p H) :=
    hH.quotient (CFSG.pPrimeCore p ↥H)
  exact (hstar.subgroup N).subgroup K

private theorem starImg_map_conj_symm {x : StarGroup p H} (hx : x ∈ starImg p H M) :
    (starImg p H M).map (MulAut.conj x).symm.toMonoidHom = starImg p H M := by
  have hconj : (MulAut.conj x).symm = MulAut.conj x⁻¹ := by
    rw [← MulAut.inv_def, ← map_inv]
  rw [hconj]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer ((starImg p H M).inv_mem hx))

private theorem conj_data_of_mem_starImg {D : Subgroup G} (hDM : D ≤ H ⊓ M)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C)
    (hCM : ¬ C ≤ starImg p H M) {x : StarGroup p H} (hx : x ∈ starImg p H D) :
    CFSG.IsComponent (C.map (MulAut.conj x).toMonoidHom) ∧
      CFSG.IsComponent (C.map (MulAut.conj (x ^ 2)).toMonoidHom) ∧
      ¬ C.map (MulAut.conj x).toMonoidHom ≤ starImg p H M ∧
      ¬ C.map (MulAut.conj (x ^ 2)).toMonoidHom ≤ starImg p H M := by
  have hxM : x ∈ starImg p H M := starImg_mono (fun _ h => (hDM h).2) hx
  have hMinvmap := starImg_map_conj_symm (M := M) (p := p) (H := H) hxM
  have hmap1 : (C.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      C.map (MulAut.conj (x ^ 2)).toMonoidHom := by
    rw [pow_two]
    exact CFSG.Walter.Bender37.map_conj_map_conj x x C
  have hC1M : ¬ C.map (MulAut.conj x).toMonoidHom ≤ starImg p H M := by
    intro hle
    apply hCM
    calc C = (C.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).symm.toMonoidHom :=
          (CFSG.LocalCores.map_map_symm (MulAut.conj x) C).symm
      _ ≤ (starImg p H M).map (MulAut.conj x).symm.toMonoidHom := Subgroup.map_mono hle
      _ = starImg p H M := hMinvmap
  have hC2Mraw : ¬ (C.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom ≤
      starImg p H M := by
    intro hle
    apply hC1M
    calc C.map (MulAut.conj x).toMonoidHom =
          ((C.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom).map
            (MulAut.conj x).symm.toMonoidHom :=
          (CFSG.LocalCores.map_map_symm (MulAut.conj x)
            (C.map (MulAut.conj x).toMonoidHom)).symm
      _ ≤ (starImg p H M).map (MulAut.conj x).symm.toMonoidHom := Subgroup.map_mono hle
      _ = starImg p H M := hMinvmap
  have hC2M : ¬ C.map (MulAut.conj (x ^ 2)).toMonoidHom ≤ starImg p H M := by
    rw [← hmap1]
    exact hC2Mraw
  exact ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hC,
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (x ^ 2)) hC, hC1M, hC2M⟩

private theorem conj_ne_self_of_mem_starImg {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    {D : Subgroup G} (hD : IsPGroup d D) {x : StarGroup p H}
    {C : Subgroup (StarGroup p H)} (hx : x ∈ starImg p H D)
    (hxN : x ∉ Subgroup.normalizer (C : Set (StarGroup p H))) :
    C ≠ C.map (MulAut.conj x).toMonoidHom ∧
      C ≠ C.map (MulAut.conj (x ^ 2)).toMonoidHom := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hDstar : IsPGroup d (starImg p H D) := by
    change IsPGroup d ((D.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)))
    exact (hD.comap_subtype (K := H)).map _
  have hodd : Odd (orderOf x) := by
    obtain ⟨k, hk⟩ := hDstar.exists_orderOf_eq_pow ⟨x, hx⟩
    have hk' : orderOf x = d ^ k := by simpa using hk
    rw [hk']
    exact (hd.odd_of_ne_two hd2).pow
  refine ⟨?_, ?_⟩
  · intro heq
    exact hxN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm)
  · intro heq
    have hx2N : x ^ 2 ∈ Subgroup.normalizer (C : Set (StarGroup p H)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hodd.coprime_two_left
    refine hxN ?_
    have hmem : (x ^ 2) ^ m ∈ Subgroup.normalizer (C : Set (StarGroup p H)) :=
      (Subgroup.normalizer (C : Set (StarGroup p H))).pow_mem hx2N m
    rwa [hm] at hmem

private theorem conj_conj_ne_of_mem_starImg {x : StarGroup p H}
    {C : Subgroup (StarGroup p H)}
    (hxN : x ∉ Subgroup.normalizer (C : Set (StarGroup p H))) :
    C.map (MulAut.conj x).toMonoidHom ≠ C.map (MulAut.conj (x ^ 2)).toMonoidHom := by
  have hmap1 : (C.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      C.map (MulAut.conj (x ^ 2)).toMonoidHom := by
    rw [pow_two]
    exact CFSG.Walter.Bender37.map_conj_map_conj x x C
  intro heq
  have hxC1 : x ∈ Subgroup.normalizer
      (C.map (MulAut.conj x).toMonoidHom : Set (StarGroup p H)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hmap1.trans heq.symm)
  have hNmap : (Subgroup.normalizer (C : Set (StarGroup p H))).map
      (MulAut.conj x).toMonoidHom = Subgroup.normalizer
        (C.map (MulAut.conj x).toMonoidHom : Set (StarGroup p H)) :=
    Subgroup.map_equiv_normalizer_eq C (MulAut.conj x)
  rw [← hNmap] at hxC1
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxC1
  have hyx : y = x := by
    have h1 : x * y * x⁻¹ = x := by simpa [MulAut.conj_apply] using hxy
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = x⁻¹ * x * x := by rw [h1]
      _ = x := by group
  rw [hyx] at hy
  exact hxN hy

private theorem four_le_pRank_of_moved_component (h : TwelveCtx G M p Q H) {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) {D : Subgroup G} (hD : IsPGroup d D) (hDM : D ≤ H ⊓ M)
    {E : Subgroup G} (hS : NineSettingGen G M p Q H E 2)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) (hCM : ¬ C ≤ starImg p H M)
    {x : StarGroup p H} (hx : x ∈ starImg p H D)
    (hxN : x ∉ Subgroup.normalizer (C : Set (StarGroup p H))) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) := by
  have hp : p.Prime := h.p_prime
  obtain ⟨hC1, hC2, hC1M, hC2M⟩ := conj_data_of_mem_starImg hDM hC hCM hx
  obtain ⟨h01, h02⟩ := conj_ne_self_of_mem_starImg hd hd2 hD hx hxN
  have h12 := conj_conj_ne_of_mem_starImg hxN
  have hdC : p ∣ Nat.card C :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card hp
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup (H := H) hp) hC
  have hdC1 : p ∣ Nat.card (C.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card hp
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup (H := H) hp) hC1
  have hdC2 : p ∣ Nat.card (C.map (MulAut.conj (x ^ 2)).toMonoidHom) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card hp
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup (H := H) hp) hC2
  exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.four_le_pRank_of_three_components hp h.p_odd
    hC hC1 hC2 h01 h02 h12 hdC hdC1 hdC2 hS.isElemAbelian_starImg_E_gen
    hS.card_starImg_E_gen
    (hS.starImg_E_le_normalizer_gen hC hCM)
    (hS.starImg_E_le_normalizer_gen hC1 hC1M)
    (hS.starImg_E_le_normalizer_gen hC2 hC2M)
    (fun f hf hf1 => hS.not_le_centralizer_of_mem_starImg_E_gen hCM hf hf1)

theorem starImg_le_normalizer_of_isComponent (h : TwelveCtx G M p Q H) {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) {D : Subgroup G} (hD : IsPGroup d D) (hDM : D ≤ H ⊓ M)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) (hCM : ¬ C ≤ starImg p H M) :
    starImg p H D ≤ Subgroup.normalizer (C : Set (StarGroup p H)) := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hS : NineSettingGen G M p Q H E 2 := nineSettingGen h hEQ hE hEc hΓ
  by_contra hnot
  obtain ⟨x, hx, hxN⟩ := SetLike.not_le_iff_exists.mp hnot
  have h4 := four_le_pRank_of_moved_component h hd hd2 hD hDM hS hC hCM hx hxN
  have h3 := hS.pRank_star_le_three h.H_mem_H2Star.1 h.p_not_mem_sigma
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
