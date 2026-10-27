module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenAtQuotKer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenThree
import CFSG.RankThree.PartOne.CTP.StrongPQuotient
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineApplyInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeYTransport
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineGamma
import CFSG.LocalAnalysis.AGL81I.Section3.SL3BorelOvergroups
import CFSG.LocalAnalysis.AGL81I.Section3.SL3Parabolic
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.LocalAnalysis.AGL81I.Section3.GammaBasics
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenConstrained
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeConclusion
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HSubFinal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpPrimeCoreLe
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCoreCharacteristic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.StrongEmbedInput
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListNormal
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
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

abbrev StarQuotP (p : ℕ) (H : Subgroup G) : Type :=
  StarGroup p H ⧸ CFSG.pCore p (StarGroup p H)

@[expose] noncomputable def oneMap (p : ℕ) (H : Subgroup G) : ↥H →* StarQuotP p H :=
  (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))).comp
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))

@[expose] noncomputable def oneImg (p : ℕ) (H A : Subgroup G) : Subgroup (StarQuotP p H) :=
  (A.subgroupOf H).map (oneMap p H)

@[expose] noncomputable def oneAmb (p : ℕ) (M H D : Subgroup G) : Subgroup (StarQuotP p H) :=
  oneImg p H (kSub p M H) ⊔ oneImg p H D

theorem not_dvd_card_ker_oneMap (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M) :
    ¬ d ∣ Nat.card (oneMap p H).ker := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hle := comap_pCore_starGroup_le_normalCore hI h
  have hN := not_dvd_card_normalCore_of_twelveCtx h hns hd
  have hker : (oneMap p H).ker =
      (CFSG.pCore p (StarGroup p H)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
    rw [oneMap, ← MonoidHom.comap_ker (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H)))
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)), QuotientGroup.ker_mk']
  rw [hker]
  intro hdvd
  exact hN (hdvd.trans (Subgroup.card_dvd_of_le hle))

theorem nonempty_oneImg_kSub_mulEquiv (h : TwelveCtx G M p Q H) (hle : pLayerIn p H ≤ M) :
    Nonempty (↥(oneImg p H (kSub p M H)) ≃* KStarQuot p M H) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : (kStar p M H).Normal := kStar_normal_of_le hle
  have hEq : oneImg p H (kSub p M H) =
      (kStar p M H).map (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))) := by
    rw [oneImg, oneMap, ← Subgroup.map_map]
    rfl
  obtain ⟨e⟩ := CFSG.LocalAnalysis.RankThreeUC.AGL81C.nonempty_quot_pCore_mulEquiv_map
    (p := p) (K := kStar p M H)
  exact ⟨(MulEquiv.subgroupCongr hEq).trans e.symm⟩

omit [Finite G] in
private theorem oneMap_surjective : Function.Surjective (oneMap p H) :=
  (QuotientGroup.mk'_surjective (CFSG.pCore p (StarGroup p H))).comp
    (QuotientGroup.mk'_surjective (primeComplementCore (G := ↥H) p))

omit [Finite G] in
private theorem oneMap_ker_eq :
    (oneMap p H).ker = (CFSG.pCore p (StarGroup p H)).comap
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
  rw [oneMap, ← MonoidHom.comap_ker (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H)))
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)), QuotientGroup.ker_mk']

private theorem oneImg_kSub_normal (hle : pLayerIn p H ≤ M) :
    (oneImg p H (kSub p M H)).Normal :=
  (kSub_normal_of_le hle).map (oneMap p H) oneMap_surjective

private theorem oneImg_sylow_d (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf d (oneImg p H D) ⊤ ∧ oneImg p H D ≠ ⊥ := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hDsylH : CFSG.ABGLocalTools.IsSylowOf d D H :=
    isSylowOf_H_of_isSylowOf_inf h hns hd hD hD1
  have hDsylH' : CFSG.ABGLocalTools.IsSylowOf d (D.subgroupOf H) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := d) H
      (A := D.subgroupOf H) (B := ⊤)]
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hD.le.trans inf_le_left),
      Subgroup.map_top, Subgroup.range_subtype]
  have hsyl : CFSG.ABGLocalTools.IsSylowOf d (oneImg p H D) ⊤ := by
    dsimp only [oneImg]
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hDsylH' ⊢
    obtain ⟨-, hDp, hDind⟩ := hDsylH'
    rw [Subgroup.relIndex_top_right] at hDind
    refine ⟨le_top, hDp.map _, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact fun hdvd => hDind (hdvd.trans (Subgroup.index_map_dvd
      (f := oneMap p H) (H := D.subgroupOf H) oneMap_surjective))
  refine ⟨hsyl, ?_⟩
  intro hbot
  let N := (oneMap p H).ker
  have hle : D.subgroupOf H ≤ N := by
    have hmap : (D.subgroupOf H).map (oneMap p H) = ⊥ := hbot
    simpa only [N] using (Subgroup.map_eq_bot_iff (D.subgroupOf H)).mp hmap
  obtain ⟨n, hn⟩ := hD.isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hD1 (Subgroup.card_eq_one.mp hn)
  have hdvdD : d ∣ Nat.card D := by
    rw [hn]; exact dvd_pow_self d hn0
  have hcard : Nat.card (D.subgroupOf H) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hD.le.trans inf_le_left)).toEquiv
  exact not_dvd_card_ker_oneMap hI h hns hd
    (hdvdD.trans (hcard ▸ Subgroup.card_dvd_of_le hle))

private theorem isStronglyPEmbedded_subgroupOf_M (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded d ((H ⊓ M).subgroupOf H) := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  obtain ⟨n, hn⟩ := hD.isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [pow_zero] at hn; exact hD1 (Subgroup.card_eq_one.mp hn)
  have hdvdD : d ∣ Nat.card D := by rw [hn]; exact dvd_pow_self d hn0
  have hdvdHM : d ∣ Nat.card (H ⊓ M : Subgroup G) :=
    hdvdD.trans (Subgroup.card_dvd_of_le hD.le)
  exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.subgroupOf
    (isStronglyPEmbedded_of_twelveCtx' h hns d hd) h.not_H_le_M hdvdHM

private theorem pCore_le_map_subgroupOf_M (hI : NineNineOneInput) (h : TwelveCtx G M p Q H) :
    CFSG.pCore p (StarGroup p H) ≤
      ((H ⊓ M).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
  rw [← Subgroup.map_comap_eq_self_of_surjective
    (H := CFSG.pCore p (StarGroup p H))
    (QuotientGroup.mk'_surjective (primeComplementCore (G := ↥H) p))]
  refine Subgroup.map_mono ?_
  exact (comap_pCore_starGroup_le_normalCore hI h).trans
    (by simpa [inf_comm] using (Subgroup.normalCore_le ((M ⊓ H).subgroupOf H)))

private theorem not_dvd_card_pCore (h : TwelveCtx G M p Q H) {d : ℕ}
    (hd : d ∈ sigmaSet G M) :
    ¬ d ∣ Nat.card (CFSG.pCore p (StarGroup p H)) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have : Finite (StarQuotP p H) :=
    Finite.of_surjective (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H)))
      (QuotientGroup.mk'_surjective _)
  have : Finite ↥(CFSG.pCore p (StarGroup p H)) := Subtype.finite
  have hpo : IsPGroup p (CFSG.pCore p (StarGroup p H)) := CFSG.pCore_isPGroup
  obtain ⟨n, hn⟩ := hpo.exists_card_eq
  intro hdvd
  rw [hn] at hdvd
  exact (mem_sigma_prime_odd_ne_p h hd).2.2
    ((Nat.prime_dvd_prime_iff_eq (Fact.out : d.Prime) h.p_prime).mp
      ((Fact.out : d.Prime).dvd_of_dvd_pow hdvd))

private theorem isStronglyPEmbedded_oneImg (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded d (oneImg p H M) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hHM : (H ⊓ M).subgroupOf H = M.subgroupOf H := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hsub := isStronglyPEmbedded_subgroupOf_M h hns hd hD hD1
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let πO : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hOleY : O ≤ (H ⊓ M).subgroupOf H := by
    simpa [inf_comm] using primeComplementCore_le_subgroupOf_of_twelveCtx h
  have hOcore : O ≤ Subgroup.normalCore ((M ⊓ H).subgroupOf H) :=
    Subgroup.normal_le_normalCore.mpr (by simpa [inf_comm] using hOleY)
  have hOnot : ¬ d ∣ Nat.card O := fun hdvd =>
    not_dvd_card_normalCore_of_twelveCtx h hns hd
      (hdvd.trans (Subgroup.card_dvd_of_le hOcore))
  have hstep1 := CFSG.RankThree.PartOne.IsStronglyPEmbedded.map_quotient hsub hOleY hOnot
  let πP : StarGroup p H →* StarQuotP p H := QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))
  let πH : ↥H →* StarQuotP p H := oneMap p H
  have hπeq : πH = πP.comp πO := rfl
  have hYle := pCore_le_map_subgroupOf_M hI h
  have hkerP := not_dvd_card_pCore h hd
  have hstep2 := CFSG.RankThree.PartOne.IsStronglyPEmbedded.map_quotient hstep1 hYle hkerP
  rw [hHM] at hstep2
  rwa [oneImg, oneMap, ← Subgroup.map_map]

private theorem oneAmb_not_le_oneImg_M (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    {D : Subgroup G} :
    ¬ oneAmb p M H D ≤ oneImg p H M := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  intro hBM
  have hKleM : oneImg p H (kSub p M H) ≤ oneImg p H M := le_sup_left.trans hBM
  have hsub : (kSub p M H).subgroupOf H ≤ M.subgroupOf H := by
    have hc := Subgroup.comap_mono (f := oneMap p H) hKleM
    dsimp only [oneImg] at hc
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, oneMap_ker_eq,
      sup_eq_left.mpr ((comap_pCore_starGroup_le_normalCore hI h).trans
        (Subgroup.normalCore_le _ |>.trans (Subgroup.subgroupOf_mono H inf_le_left)))] at hc
    exact le_trans le_sup_left hc
  exact (not_kSub_le_M_of_nineNineOne h hI)
    (fun x hx => Subgroup.mem_subgroupOf.mp
      (hsub (show (⟨x, kSub_le p M H hx⟩ : ↥H) ∈ (kSub p M H).subgroupOf H from hx)))

private theorem oPPrimeHull_oneAmb_le (h : TwelveCtx G M p Q H) (hle : pLayerIn p H ≤ M)
    {D : Subgroup G} :
    oneImg p H (kSub p M H) ≤ oPPrimeHull p (oneAmb p M H D) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hEqK : oneImg p H (kSub p M H) =
      (kStar p M H).map (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))) := by
    rw [oneImg, oneMap, ← Subgroup.map_map]
    rfl
  have hK1hull : oPPrimeHull p (oneImg p H (kSub p M H)) = oneImg p H (kSub p M H) := by
    rw [hEqK, oPPrimeHull_map_kStar h.p_prime hle]
  have hK1le : oneImg p H (kSub p M H) ≤ oneAmb p M H D := le_sup_left
  calc oneImg p H (kSub p M H) = oPPrimeHull p (oneImg p H (kSub p M H)) := hK1hull.symm
    _ ≤ oPPrimeHull p (oneAmb p M H D) := by
      rw [oPPrimeHull, oPPrimeHull]
      exact Subgroup.closure_mono fun x hx => ⟨hK1le hx.1, hx.2⟩

private theorem oPPrimeHull_oneAmb_ge (h : TwelveCtx G M p Q H) (hle : pLayerIn p H ≤ M)
    {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) :
    oPPrimeHull p (oneAmb p M H D) ≤ oneImg p H (kSub p M H) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨hxB, k, hk⟩
  rw [oneAmb] at hxB
  have : (oneImg p H (kSub p M H)).Normal := oneImg_kSub_normal hle
  obtain ⟨y, hyK, z, hzD, hyz⟩ := (Subgroup.mem_sup_of_normal_left).mp hxB
  have hq : QuotientGroup.mk' (oneImg p H (kSub p M H)) z = 1 := by
    let q : StarQuotP p H →* StarQuotP p H ⧸ oneImg p H (kSub p M H) :=
      QuotientGroup.mk' _
    have hx : q x = q z := by
      rw [← hyz, map_mul]
      have : q y = 1 := (QuotientGroup.eq_one_iff y).mpr hyK
      rw [this, one_mul]
    have hxp : orderOf (q z) ∣ p ^ k := by
      obtain ⟨c, hc⟩ := orderOf_map_dvd q x
      refine ⟨c, ?_⟩
      rw [← hk]
      simpa [hx] using hc
    have hD1p : IsPGroup d (oneImg p H D) :=
      (hD.isPGroup.comap_subtype (K := H)).map (oneMap p H)
    obtain ⟨m, hm⟩ := hD1p.exists_orderOf_eq_pow ⟨z, hzD⟩
    have hzd : orderOf (q z) ∣ d ^ m := by
      obtain ⟨c, hc⟩ := orderOf_map_dvd q z
      have hzord : orderOf z = d ^ m := by simpa using hm
      refine ⟨c, ?_⟩
      rw [← hc, hzord]
    have hcop : Nat.Coprime (p ^ k) (d ^ m) := by
      refine Nat.Coprime.pow k m ?_
      exact (Nat.coprime_primes h.p_prime (Fact.out : d.Prime)).mpr
        (fun hpd : p = d => (mem_sigma_prime_odd_ne_p h hd).2.2 hpd.symm)
    have hone : orderOf (q z) = 1 := Nat.eq_one_of_dvd_coprimes hcop hxp hzd
    exact orderOf_eq_one_iff.mp hone
  rw [← hyz]
  exact (oneImg p H (kSub p M H)).mul_mem hyK ((QuotientGroup.eq_one_iff z).mp hq)

private theorem oPPrimeHull_oneAmb_eq (h : TwelveCtx G M p Q H) (hle : pLayerIn p H ≤ M)
    {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) :
    oPPrimeHull p (oneAmb p M H D) = oneImg p H (kSub p M H) :=
  le_antisymm (oPPrimeHull_oneAmb_ge h hle hd hD) (oPPrimeHull_oneAmb_le h hle)

private theorem isSylowOf_map_of_isSylowOf {q : ℕ} [Fact q.Prime] {R K : Subgroup ↥H}
    (hR : CFSG.ABGLocalTools.IsSylowOf q R K) (hkerK : (oneMap p H).ker ≤ K) :
    CFSG.ABGLocalTools.IsSylowOf q (R.map (oneMap p H)) (K.map (oneMap p H)) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hR ⊢
  obtain ⟨hRK, hp, hind⟩ := hR
  refine ⟨Subgroup.map_mono hRK, hp.map _, ?_⟩
  rw [Subgroup.relIndex_map_map, sup_eq_left.mpr hkerK]
  exact fun hdvd => hind
    (hdvd.trans (Subgroup.relIndex_dvd_of_le_left (H := R)
      (K := R ⊔ (oneMap p H).ker) (L := K) le_sup_left))

private theorem isSylowOf_of_isSylowOf_le {q : ℕ} [Fact q.Prime]
    {P K B : Subgroup (StarQuotP p H)}
    (hP : CFSG.ABGLocalTools.IsSylowOf q P K) (hKB : K ≤ B)
    (hcop : q.Coprime (K.relIndex B)) : CFSG.ABGLocalTools.IsSylowOf q P B := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
  obtain ⟨hPK, hp, hind⟩ := hP
  refine ⟨hPK.trans hKB, hp, ?_⟩
  intro hdvd
  have hmul := Subgroup.relIndex_mul_relIndex (H := P) (K := K) (L := B) hPK hKB
  have hdiv : q ∣ P.relIndex K * K.relIndex B := by rwa [hmul]
  exact hind (((Fact.out : q.Prime).dvd_mul.mp hdiv).resolve_right
    ((Fact.out : q.Prime).coprime_iff_not_dvd.mp hcop))

private theorem exists_sylowP_preimage (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hle : pLayerIn p H ≤ M) :
    ∃ R : Subgroup ↥H,
      CFSG.ABGLocalTools.IsSylowOf p R
        ((kSub p M H).subgroupOf H ⊔ (oneMap p H).ker) ∧
      R ≤ (M ⊓ H).subgroupOf H ∧
      Subgroup.normalizer (R.map H.subtype : Set G) ≤ M := by
  let N := (oneMap p H).ker
  let Kpre : Subgroup ↥H := (kSub p M H).subgroupOf H ⊔ N
  have hNK : N ≤ Kpre := le_sup_right
  have hkK : (kSub p M H).subgroupOf H ≤ Kpre := le_sup_left
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hEH : E ≤ H := hEQ.trans h.Q_le_H
  have hEk : E ≤ kSub p M H := le_kSub_of_le h.p_prime hle hEH (fun a ha => hE.2 a ha)
  let E' : Subgroup ↥H := E.subgroupOf H
  have hE'p : IsPGroup p E' := hE.isPGroup.comap_subtype (K := H)
  have hE'K : E' ≤ Kpre := hkK.trans' (Subgroup.subgroupOf_mono H hEk)
  obtain ⟨R, hE'R⟩ := (hE'p.comap_subtype (K := Kpre)).exists_le_sylow
  let Rsub : Subgroup ↥H := (R : Subgroup Kpre).map Kpre.subtype
  have hRsylK : CFSG.ABGLocalTools.IsSylowOf p Rsub Kpre := ⟨R, rfl⟩
  have hE'Rsub : E' ≤ Rsub := by
    have h := Subgroup.map_mono (f := Kpre.subtype) hE'R
    change (E'.subgroupOf Kpre).map Kpre.subtype ≤ (R : Subgroup Kpre).map Kpre.subtype at h
    rwa [Subgroup.map_subgroupOf_eq_of_le hE'K] at h
  have hER : E ≤ Rsub.map H.subtype := by
    rw [← (show E'.map H.subtype = E by
      dsimp only [E']
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEH])]
    exact Subgroup.map_mono hE'Rsub
  obtain ⟨hRM, hNRM⟩ := le_M_and_normalizer_le_of_le hI h hEQ hE hEc hΓ
    (hRsylK.isPGroup.map H.subtype) hER
  have hRsubM : Rsub ≤ (M ⊓ H).subgroupOf H := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := H)]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    exact le_inf hRM (Subgroup.map_subtype_le Rsub)
  exact ⟨Rsub, by simpa only [Kpre, N] using hRsylK, hRsubM, hNRM⟩

private theorem p_coprime_relIndex_oneAmb (h : TwelveCtx G M p Q H) (hle : pLayerIn p H ≤ M)
    {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) :
    p.Coprime ((oneImg p H (kSub p M H)).relIndex (oneAmb p M H D)) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have : (oneImg p H (kSub p M H)).Normal := oneImg_kSub_normal hle
  have hrel : (oneImg p H (kSub p M H)).relIndex (oneAmb p M H D) =
      (oneImg p H (kSub p M H)).relIndex (oneImg p H D) := by
    rw [show oneAmb p M H D = oneImg p H (kSub p M H) ⊔ oneImg p H D from rfl,
      Subgroup.relIndex_sup_left]
  rw [hrel]
  have hdvd : (oneImg p H (kSub p M H)).relIndex (oneImg p H D) ∣
      Nat.card (oneImg p H D) :=
    Subgroup.relIndex_dvd_card (H := oneImg p H (kSub p M H)) (K := oneImg p H D)
  have hD1p : IsPGroup d (oneImg p H D) :=
    (hD.isPGroup.comap_subtype (K := H)).map (oneMap p H)
  obtain ⟨m, hm⟩ := hD1p.exists_card_eq
  rw [hm] at hdvd
  exact h.p_prime.coprime_iff_not_dvd.mpr fun hpdvd =>
    (mem_sigma_prime_odd_ne_p h hd).2.2
      ((Nat.prime_dvd_prime_iff_eq h.p_prime (Fact.out : d.Prime)).mp
        (h.p_prime.dvd_of_dvd_pow (hpdvd.trans hdvd))).symm

private theorem exists_sylowP_oneAmb (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hle : pLayerIn p H ≤ M) {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) :
    ∃ P : Subgroup (StarQuotP p H),
      CFSG.ABGLocalTools.IsSylowOf p P (oneAmb p M H D) ∧
        P ≤ oneImg p H (kSub p M H) ∧
        Subgroup.normalizer (P : Set (StarQuotP p H)) ≤ oneImg p H M := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨R, hRsylK, hRsubM, hNRM⟩ := exists_sylowP_preimage hI h hle
  let π := oneMap p H
  let N := π.ker
  let Kpre : Subgroup ↥H := (kSub p M H).subgroupOf H ⊔ N
  have hNK : N ≤ Kpre := le_sup_right
  have hNM : (oneMap p H).ker ≤ (M ⊓ H).subgroupOf H := by
    rw [oneMap_ker_eq]
    exact (comap_pCore_starGroup_le_normalCore hI h).trans
      (Subgroup.normalCore_le ((M ⊓ H).subgroupOf H))
  have hNKle : Subgroup.normalizer ((R ⊔ N : Subgroup ↥H) : Set ↥H) ≤
      (M ⊓ H).subgroupOf H :=
    normalizer_sup_le_of_isSylowOf hNK
      (by simpa only [Kpre, N, π] using hRsylK.le)
      (by simpa only [Kpre, N, π] using hRsylK) hRsubM
      (by simpa only [N, π] using hNM)
      (normalizer_le_subgroupOf_of_normalizer_map_le hNRM)
  let P : Subgroup (StarQuotP p H) := R.map π
  have hKpreMap : Kpre.map π = oneImg p H (kSub p M H) := by
    dsimp only [Kpre, N, oneImg]
    rw [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq]
  have hPsylK : CFSG.ABGLocalTools.IsSylowOf p P (oneImg p H (kSub p M H)) := by
    rw [← hKpreMap]
    exact isSylowOf_map_of_isSylowOf (by simpa only [Kpre, N, π] using hRsylK) hNK
  have hPnorm : Subgroup.normalizer (P : Set (StarQuotP p H)) ≤ oneImg p H M := by
    have hpre : (Subgroup.normalizer (P : Set (StarQuotP p H))).comap π =
        Subgroup.normalizer ((R ⊔ N : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.comap_normalizer_eq_of_surjective _ oneMap_surjective,
        Subgroup.comap_map_eq]
    intro x hx
    obtain ⟨x', rfl⟩ := oneMap_surjective x
    have hx' : x' ∈ (Subgroup.normalizer (P : Set (StarQuotP p H))).comap π := hx
    rw [hpre] at hx'
    exact Subgroup.mem_map_of_mem _ ((Subgroup.subgroupOf_mono H inf_le_left) (hNKle hx'))
  exact ⟨P, isSylowOf_of_isSylowOf_le hPsylK le_sup_left
    (p_coprime_relIndex_oneAmb h hle hd hD), hPsylK.le, hPnorm⟩

private theorem isSylowOf_subgroupOf_top {q : ℕ} [Fact q.Prime]
    {A B : Subgroup (StarQuotP p H)} (h : CFSG.ABGLocalTools.IsSylowOf q A B) :
    CFSG.ABGLocalTools.IsSylowOf q (A.subgroupOf B) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨hAB, hp, hind⟩ := h
  refine ⟨le_top, hp.comap_subtype, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact hind

omit [Finite G] in
private theorem normalizer_subgroupOf_le {A B Y : Subgroup (StarQuotP p H)} (hAB : A ≤ B)
    (h : Subgroup.normalizer (A : Set (StarQuotP p H)) ≤ Y) :
    Subgroup.normalizer ((A.subgroupOf B : Subgroup ↥B) : Set ↥B) ≤
      (Y ⊓ B).subgroupOf B := by
  intro x hx
  have hx' : x ∈ (Subgroup.normalizer (A : Set (StarQuotP p H))).subgroupOf B := by
    rwa [Subgroup.subgroupOf_normalizer_eq hAB]
  exact Subgroup.mem_subgroupOf.mpr ⟨h hx', x.2⟩

private theorem normalizer_subgroupOf_D_le_M (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥)
    {F : Subgroup ↥(oneAmb p M H D)}
    (hF : F ≤ (oneImg p H D).subgroupOf (oneAmb p M H D)) (hFne : F ≠ ⊥) :
    Subgroup.normalizer (F : Set ↥(oneAmb p M H D)) ≤
      (oneImg p H M ⊓ oneAmb p M H D).subgroupOf (oneAmb p M H D) := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hstrong := isStronglyPEmbedded_oneImg hI h hns hd hD hD1
  let B := oneAmb p M H D
  let D1 := oneImg p H D
  let M1 := oneImg p H M
  have hD1p : IsPGroup d D1 :=
    (hD.isPGroup.comap_subtype (K := H)).map (oneMap p H)
  have hD1leM : D1 ≤ M1 :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H (hD.le.trans inf_le_right))
  have hD1leB : D1 ≤ B := le_sup_right
  have hFmap_le : F.map B.subtype ≤ D1 := by
    have h := Subgroup.map_mono (f := B.subtype) hF
    rwa [Subgroup.map_subgroupOf_eq_of_le hD1leB] at h
  have hFmap_ne : F.map B.subtype ≠ ⊥ := by
    intro hbot
    apply hFne
    have hle : F ≤ (B.subtype).ker := (Subgroup.map_eq_bot_iff F).mp hbot
    simpa using hle
  have hFA : (F.map B.subtype).subgroupOf B = F := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      rwa [hyx'] at hy
    · intro hx
      exact ⟨⟨x.val, x.2⟩, hx, rfl⟩
  have hnorm := normalizer_subgroupOf_le (A := F.map B.subtype) (B := B) (Y := M1)
    (Subgroup.map_subtype_le F) (hstrong.normalizer_le hFmap_ne
      (hD1p.to_le hFmap_le) (hFmap_le.trans hD1leM))
  rw [← hFA]
  exact hnorm

private theorem gammaIn_oneAmb_le (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    gammaIn 1 d ((oneImg p H D).subgroupOf (oneAmb p M H D))
        ((oneImg p H (kSub p M H)).subgroupOf (oneAmb p M H D) ⊔
          (oneImg p H D).subgroupOf (oneAmb p M H D)) ≤
      (oneImg p H M ⊓ oneAmb p M H D).subgroupOf (oneAmb p M H D) := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  let B := oneAmb p M H D
  let D1 := oneImg p H D
  have hD1leB : D1 ≤ B := le_sup_right
  refine (CFSG.LocalAnalysis.AGL81I.Section3.gammaIn_le_gammaOver (Fact.out : d.Prime).one_lt
    (D1.subgroupOf B) ((oneImg p H (kSub p M H)).subgroupOf B ⊔ D1.subgroupOf B)).trans ?_
  rw [CFSG.LocalAnalysis.AGL81TheoremCD.Section12.gammaOver]
  refine iSup₂_le fun F hF => iSup_le fun hrank => ?_
  have hFne : F ≠ ⊥ := by
    rintro rfl
    rw [CFSG.AGLEmbedding.pRank_bot_eq_zero
      (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1)] at hrank
    omega
  exact inf_le_left.trans
    (normalizer_subgroupOf_D_le_M hI h hns hd hD hD1 hF hFne)

private theorem oneAmb_I_eq (h : TwelveCtx G M p Q H) (hle : pLayerIn p H ≤ M)
    {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) :
    (oneImg p H (kSub p M H)).subgroupOf (oneAmb p M H D) =
      oPPrimeHull p (⊤ : Subgroup ↥(oneAmb p M H D)) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have h4 := oPPrimeHull_oneAmb_eq h hle hd hD
  rw [← h4, oPPrimeHull_subgroupOf_of_le (A := oneAmb p M H D)
    (K := oneAmb p M H D) le_rfl, Subgroup.subgroupOf_self]

private theorem oneAmb_D_sylow_ne (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf d
        ((oneImg p H D).subgroupOf (oneAmb p M H D)) ⊤ ∧
      (oneImg p H D).subgroupOf (oneAmb p M H D) ≠ ⊥ := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  obtain ⟨hD1syl, hD1ne⟩ := oneImg_sylow_d hI h hns hd hD hD1
  let B := oneAmb p M H D
  let D1 := oneImg p H D
  have hD1leB : D1 ≤ B := le_sup_right
  have hDsylB : CFSG.ABGLocalTools.IsSylowOf d D1 B := hD1syl.of_le hD1leB le_top
  refine ⟨isSylowOf_subgroupOf_top hDsylB, ?_⟩
  intro hbot
  apply hD1ne
  have hmap := congrArg (Subgroup.map B.subtype) hbot
  rw [Subgroup.map_subgroupOf_eq_of_le hD1leB, Subgroup.map_bot] at hmap
  exact hmap

private theorem oneAmb_Y_lt (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    {D : Subgroup G} :
    (oneImg p H M ⊓ oneAmb p M H D).subgroupOf (oneAmb p M H D) <
      (oneImg p H (kSub p M H)).subgroupOf (oneAmb p M H D) ⊔
        (oneImg p H D).subgroupOf (oneAmb p M H D) := by
  let B := oneAmb p M H D
  let D1 := oneImg p H D
  let M1 := oneImg p H M
  let I := (oneImg p H (kSub p M H)).subgroupOf B
  let Dsub := D1.subgroupOf B
  let Y := (M1 ⊓ B).subgroupOf B
  have hID : I ⊔ Dsub = ⊤ := by
    dsimp only [I, Dsub, D1, B, oneAmb]
    change (oneImg p H (kSub p M H)).subgroupOf
          (oneImg p H (kSub p M H) ⊔ oneImg p H D) ⊔
        (oneImg p H D).subgroupOf
          (oneImg p H (kSub p M H) ⊔ oneImg p H D) = ⊤
    rw [← Subgroup.subgroupOf_sup (le_sup_left :
      oneImg p H (kSub p M H) ≤ oneImg p H (kSub p M H) ⊔ oneImg p H D)
      (le_sup_right : oneImg p H D ≤ oneImg p H (kSub p M H) ⊔ oneImg p H D)]
    exact Subgroup.subgroupOf_self (oneImg p H (kSub p M H) ⊔ oneImg p H D)
  have hYne_top : Y ≠ ⊤ := by
    intro htop
    apply oneAmb_not_le_oneImg_M hI h
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥B) ∈ Y := by rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hx').1
  rw [hID]
  exact lt_top_iff_ne_top.mpr hYne_top

theorem exists_threeTenHyp_oneAmb (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M) (hle : pLayerIn p H ≤ M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    ∃ P : Subgroup ↥(oneAmb p M H D),
      CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenHyp
        ((oneImg p H (kSub p M H)).subgroupOf (oneAmb p M H D))
        ((oneImg p H D).subgroupOf (oneAmb p M H D)) P
        ((oneImg p H M ⊓ oneAmb p M H D).subgroupOf (oneAmb p M H D)) p d := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hd' := mem_sigma_prime_odd_ne_p h hd
  obtain ⟨P1, hPsylB, hP1le, hP1norm⟩ := exists_sylowP_oneAmb hI h hle hd hD
  let B := oneAmb p M H D
  let D1 := oneImg p H D
  let M1 := oneImg p H M
  let I := (oneImg p H (kSub p M H)).subgroupOf B
  let Dsub := D1.subgroupOf B
  let Y := (M1 ⊓ B).subgroupOf B
  have hIfield : I = oPPrimeHull p (⊤ : Subgroup ↥B) := by
    dsimp only [I]
    exact oneAmb_I_eq h hle hd hD
  obtain ⟨hDfield, hDne⟩ := oneAmb_D_sylow_ne hI h hns hd hD hD1
  have hPfield : CFSG.ABGLocalTools.IsSylowOf p (P1.subgroupOf B) ⊤ :=
    isSylowOf_subgroupOf_top hPsylB
  have hYlt : Y < I ⊔ Dsub := by
    dsimp only [Y, I, Dsub]
    exact oneAmb_Y_lt hI h
  have hNfield : Subgroup.normalizer (P1.subgroupOf B : Set ↥B) ⊓ I ≤ Y :=
    inf_le_left.trans (normalizer_subgroupOf_le (A := P1) (B := B) (Y := M1)
      (hP1le.trans le_sup_left) hP1norm)
  refine ⟨P1.subgroupOf B, h.p_prime, h.p_odd, hd'.1, hd'.2.1, hd'.2.2, hIfield,
    hDfield, hDne, hPfield, hYlt, ?_, hNfield⟩
  simpa only [I, Dsub, Y, B, M1] using gammaIn_oneAmb_le hI h hns hd hD hD1

omit [Finite G] in
private theorem map_subgroupOf_subgroupOf_equiv {A B P : Subgroup (StarQuotP p H)}
    (hAB : A ≤ B) :
    ((P.subgroupOf B).subgroupOf (A.subgroupOf B)).map
        (Subgroup.subgroupOfEquivOfLe hAB).toMonoidHom = P.subgroupOf A := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : ((y : ↥(A.subgroupOf B)) : StarQuotP p H) ∈ P :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)
    have hxval : (x : StarQuotP p H) = ((y : ↥(A.subgroupOf B)) : StarQuotP p H) := by
      rw [← hyx]; rfl
    exact Subgroup.mem_subgroupOf.mpr (hxval.symm ▸ hy')
  · intro hx
    refine ⟨⟨⟨x.val, hAB x.property⟩, x.property⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
    rfl

theorem isMaxParabolicP_oneImg_of_oneAmb [Fact p.Prime] {D : Subgroup G}
    (hP : IsMaxParabolicP p ((oneImg p H (kSub p M H)).subgroupOf (oneAmb p M H D))
      ((oneImg p H M ⊓ oneAmb p M H D).subgroupOf (oneAmb p M H D))) :
    IsMaxParabolicP p (oneImg p H (kSub p M H)) (oneImg p H M ⊓ oneImg p H (kSub p M H)) := by
  let K : Subgroup (StarQuotP p H) := oneImg p H (kSub p M H)
  let Amb : Subgroup (StarQuotP p H) := oneAmb p M H D
  let M1 : Subgroup (StarQuotP p H) := oneImg p H M
  let P' : Subgroup (StarQuotP p H) := M1 ⊓ K
  have hK : K ≤ Amb := le_sup_left
  have hP'K : P' ≤ K := inf_le_right
  have hPle : (M1 ⊓ Amb).subgroupOf Amb ≤ K.subgroupOf Amb := hP.1.1
  have hPeq : (M1 ⊓ Amb).subgroupOf Amb = P'.subgroupOf Amb := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, -⟩ := Subgroup.mem_subgroupOf.mp hx
      have hxK : (x : Amb) ∈ K.subgroupOf Amb := hPle hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hx1, Subgroup.mem_subgroupOf.mp hxK⟩
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp hx).1, x.2⟩
  have hmain : IsMaxParabolicP p (K.subgroupOf Amb) (P'.subgroupOf Amb) := by
    rw [← hPeq]
    exact hP
  let e : ↥(K.subgroupOf Amb) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK
  have hPK' : P'.subgroupOf Amb ≤ K.subgroupOf Amb :=
    Subgroup.subgroupOf_mono Amb hP'K
  have hmain_sub : IsMaxParabolicP p (⊤ : Subgroup ↥(K.subgroupOf Amb))
      ((P'.subgroupOf Amb).subgroupOf (K.subgroupOf Amb)) :=
    (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_subgroupOf_iff hPK').mp hmain
  have hmain' : IsMaxParabolicP p (⊤ : Subgroup ↥K)
      (((P'.subgroupOf Amb).subgroupOf (K.subgroupOf Amb)).map e.toMonoidHom) := by
    have h := (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_map_iff e).mp hmain_sub
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
  have himg : ((P'.subgroupOf Amb).subgroupOf (K.subgroupOf Amb)).map e.toMonoidHom =
      P'.subgroupOf K :=
    map_subgroupOf_subgroupOf_equiv (A := K) (B := Amb) (P := P') hK
  rw [himg] at hmain'
  exact (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_subgroupOf_iff hP'K).mpr hmain'

theorem isCyclic_of_isCyclic_oneImg (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hDd : IsPGroup d D) (hDH : D ≤ H) (hc : IsCyclic ↥(oneImg p H D)) : IsCyclic ↥D := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hker := not_dvd_card_ker_oneMap hI h hns hd
  let e : ↥(D.subgroupOf H) ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDH
  let f : ↥(D.subgroupOf H) →* ↥(oneImg p H D) := (oneMap p H).subgroupMap (D.subgroupOf H)
  have hfker : f.ker = ⊥ := by
    apply Subgroup.card_eq_one.mp
    have hdiv1 : Nat.card f.ker ∣ Nat.card (D.subgroupOf H) :=
      Subgroup.card_subgroup_dvd_card f.ker
    have hdiv2 : Nat.card f.ker ∣ Nat.card (oneMap p H).ker := by
      have hle : (f.ker).map (D.subgroupOf H).subtype ≤ (oneMap p H).ker := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        have hy1 : f y = 1 := hy
        change (f y : ↥(oneImg p H D)).val = 1
        simpa using congrArg Subtype.val hy1
      have hcard : Nat.card (f.ker.map (D.subgroupOf H).subtype) = Nat.card f.ker :=
        Subgroup.card_map_of_injective (D.subgroupOf H).subtype_injective
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    have hnot : ¬ d ∣ Nat.card f.ker := fun h => hker (h.trans hdiv2)
    obtain ⟨n, hn⟩ := hDd.exists_card_eq
    have hcardD : Nat.card (D.subgroupOf H) = d ^ n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv, hn]
    have hdvd : Nat.card f.ker ∣ d ^ n := hcardD ▸ hdiv1
    have hcop : Nat.Coprime (d ^ n) (Nat.card f.ker) :=
      ((Fact.out : d.Prime).coprime_iff_not_dvd.mpr hnot).pow_left n
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd (dvd_refl _)
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, hfker]
  have hcyc : IsCyclic ↥(D.subgroupOf H) := isCyclic_of_injective f hfinj
  have : IsCyclic ↥(D.subgroupOf H) := hcyc
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
