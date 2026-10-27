module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineApplyInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineGamma
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefL3QuotResidual
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
public import CFSG.LocalAnalysis.AGL81I.Section3.GammaBasics
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenConstrained
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem not_dvd_card_normalCore_of_twelveCtx (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M) :
    ¬ d ∣ Nat.card (Subgroup.normalCore ((M ⊓ H).subgroupOf H)) := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  let N : Subgroup G := (Subgroup.normalCore ((M ⊓ H).subgroupOf H)).map H.subtype
  have hNsub : N.subgroupOf H = Subgroup.normalCore ((M ⊓ H).subgroupOf H) := by
    dsimp only [N]
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hN_normal : (N.subgroupOf H).Normal := by
    rw [hNsub]
    exact Subgroup.normalCore_normal _
  have hNH : N ≤ H := Subgroup.map_subtype_le _
  have hNM : N ≤ M := by
    dsimp only [N]
    rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]
    exact (Subgroup.normalCore_le _).trans (Subgroup.subgroupOf_mono H inf_le_left)
  have hnot := not_dvd_card_of_normal_le (isStronglyPEmbedded_of_twelveCtx' h hns d hd)
    h.not_H_le_M hN_normal hNH hNM
  have hcard : Nat.card N = Nat.card (Subgroup.normalCore ((M ⊓ H).subgroupOf H)) := by
    dsimp only [N]
    exact Subgroup.card_map_of_injective H.subtype_injective
  rwa [hcard] at hnot

theorem primeComplementCore_le_subgroupOf_of_twelveCtx (h : TwelveCtx G M p Q H) :
    primeComplementCore (G := ↥H) p ≤ (M ⊓ H).subgroupOf H := by
  have hrel : CFSG.Open.relPPrimeCore p H ≤ M := relPPrimeCore_le_M_of_twelveCtx h
  have hmapO : (primeComplementCore (G := ↥H) p).map H.subtype ≤ M ⊓ H := by
    refine le_inf ?_ (Subgroup.map_subtype_le _)
    rw [← CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
      h.p_prime H]
    exact hrel
  rw [← Subgroup.map_subtype_le_map_subtype (G' := H)]
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  exact hmapO

private theorem opPp_le_subgroupOf (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hOle : primeComplementCore (G := ↥H) p ≤ (M ⊓ H).subgroupOf H) :
    CFSG.Op_p'p p ↥H ≤ (M ⊓ H).subgroupOf H := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hEH : E ≤ H := hEQ.trans h.Q_le_H
  let E' : Subgroup ↥H := E.subgroupOf H
  let A : Subgroup ↥H := CFSG.Op_p'p p ↥H
  let G' : Subgroup ↥H := A ⊔ E'
  have hE'p : IsPGroup p E' := hE.isPGroup.comap_subtype (K := H)
  have hE'p' : IsPGroup p (E'.subgroupOf G') := hE'p.comap_subtype (K := G')
  obtain ⟨S, hE'S⟩ := hE'p'.exists_le_sylow
  let U : Subgroup ↥H := (S : Subgroup G').map G'.subtype
  have hUS : CFSG.ABGLocalTools.IsSylowOf p U G' := ⟨S, rfl⟩
  have hE'U : E' ≤ U := by
    have h := Subgroup.map_mono (f := G'.subtype) hE'S
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right] at h
    exact h
  have hER : E ≤ U.map H.subtype := by
    rw [← (show E'.map H.subtype = E by
      dsimp only [E']
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEH])]
    exact Subgroup.map_mono hE'U
  obtain ⟨hRM, -⟩ := le_M_and_normalizer_le_of_le hI h hEQ hE hEc hΓ
    (hUS.isPGroup.map H.subtype) hER
  have hUle : U ≤ (M ⊓ H).subgroupOf H := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := H)]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    exact le_inf hRM (Subgroup.map_subtype_le U)
  have hAn : A.Normal := by
    dsimp only [A]
    infer_instance
  have hG'norm : G' ≤ Subgroup.normalizer (A : Set ↥H) := Subgroup.le_normalizer_of_normal
  have hUAsyl : CFSG.ABGLocalTools.IsSylowOf p (U ⊓ A) A :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hUS le_sup_left hG'norm
  have hsup := (CFSG.ABGLocalTools.sup_eq_Op_p'p_iff_isSylowOf
    (H := ↥H) hUAsyl.isPGroup).mpr hUAsyl
  rw [← hsup]
  exact sup_le hOle (le_trans inf_le_left hUle)

theorem comap_pCore_starGroup_le_normalCore (hI : NineNineOneInput) (h : TwelveCtx G M p Q H) :
    (CFSG.pCore p (StarGroup p H)).comap (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
      ≤ Subgroup.normalCore ((M ⊓ H).subgroupOf H) := by
  change CFSG.Op_p'p p ↥H ≤ Subgroup.normalCore ((M ⊓ H).subgroupOf H)
  have : (CFSG.Op_p'p p ↥H).Normal := inferInstance
  exact Subgroup.normal_le_normalCore.mpr
    (opPp_le_subgroupOf hI h (primeComplementCore_le_subgroupOf_of_twelveCtx h))

@[expose] noncomputable def quotKerImg (M H A : Subgroup G) : Subgroup (QuotKer M H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (Subgroup.normalCore ((M ⊓ H).subgroupOf H)))

private theorem isSylowOf_quotKerImg {d : ℕ} [Fact d.Prime] {D B : Subgroup ↥H}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D B) (hB : d.Coprime B.index) :
    CFSG.ABGLocalTools.IsSylowOf d
      (D.map (QuotientGroup.mk' (Subgroup.normalCore ((M ⊓ H).subgroupOf H)))) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hD ⊢
  obtain ⟨hDB, hDp, hDind⟩ := hD
  refine ⟨le_top, hDp.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro hdvd
  have hdDind : d ∣ D.index := hdvd.trans (Subgroup.index_map_dvd
    (f := QuotientGroup.mk' (Subgroup.normalCore ((M ⊓ H).subgroupOf H))) (H := D)
    (QuotientGroup.mk'_surjective _))
  have hmul : D.relIndex B * B.index = D.index := Subgroup.relIndex_mul_index hDB
  have hB' : ¬ d ∣ B.index := (Fact.out : d.Prime).coprime_iff_not_dvd.mp hB
  refine hDind ?_
  rw [← hmul] at hdDind
  exact ((Fact.out : d.Prime).dvd_mul.mp hdDind).resolve_right hB'

omit [Finite G] in
theorem normalizer_le_subgroupOf_of_normalizer_map_le {R : Subgroup ↥H}
    (hNRM : Subgroup.normalizer (R.map H.subtype : Set G) ≤ M) :
    Subgroup.normalizer (R : Set ↥H) ≤ (M ⊓ H).subgroupOf H := by
  have hEq : (Subgroup.normalizer (R.map H.subtype : Set G)).subgroupOf H =
      Subgroup.normalizer (R : Set ↥H) := by
    rw [Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le R)]
    have hR : (R.map H.subtype).subgroupOf H = R := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hR]
  intro x hx
  have h1 : x ∈ (Subgroup.normalizer (R.map H.subtype : Set G)).subgroupOf H := by
    rw [hEq]; exact hx
  exact Subgroup.mem_subgroupOf.mpr
    ⟨hNRM (Subgroup.mem_subgroupOf.mp h1), x.2⟩

theorem normalizer_sup_le_of_isSylowOf [Fact p.Prime] {B R N : Subgroup ↥H}
    (hNB : N ≤ B) (hRB : R ≤ B) (hRsyl : CFSG.ABGLocalTools.IsSylowOf p R B)
    (hRM : R ≤ (M ⊓ H).subgroupOf H) (hNM : N ≤ (M ⊓ H).subgroupOf H)
    (hNHR : Subgroup.normalizer (R : Set ↥H) ≤ (M ⊓ H).subgroupOf H) :
    Subgroup.normalizer ((R ⊔ N : Subgroup ↥H) : Set ↥H) ≤ (M ⊓ H).subgroupOf H := by
  let K : Subgroup ↥H := R ⊔ N
  have hNK : N ≤ K := le_sup_right
  have hRK : R ≤ K := le_sup_left
  have hRsylK : CFSG.ABGLocalTools.IsSylowOf p R K := hRsyl.of_le hRK (sup_le hRB hNB)
  have hNKmem : K ≤ (M ⊓ H).subgroupOf H := sup_le hRM hNM
  intro g hg
  have hKg : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hconj : CFSG.ABGLocalTools.IsSylowOf p (R.map (MulAut.conj g).toMonoidHom) K := by
    have h := CFSG.GroupTheory.isSylowOf_map_conj hRsylK g
    rwa [hKg] at h
  obtain ⟨k, hkK, hk⟩ := hRsylK.exists_mem_conj hconj
  have hmapk : ∀ x : ↥H, x ∈ R.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * x * k ∈ R := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change k⁻¹ * (MulAut.conj k) y * k ∈ R
      rw [MulAut.conj_apply]
      rwa [show k⁻¹ * (k * y * k⁻¹) * k = y by group]
    · intro hx
      refine ⟨k⁻¹ * x * k, hx, ?_⟩
      change (MulAut.conj k) (k⁻¹ * x * k) = x
      rw [MulAut.conj_apply]
      group
  have hReq : R.map (MulAut.conj g).toMonoidHom = R.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [hk x, hmapk x]
  have hNorm : k⁻¹ * g ∈ Subgroup.normalizer (R : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hReq
    rw [CFSG.Walter.Bender37.map_conj_map_conj, CFSG.Walter.Bender37.map_conj_map_conj] at h
    rw [inv_mul_cancel] at h
    rw [show MulAut.conj (1 : ↥H) = 1 from map_one _] at h
    have h1 : MulEquiv.toMonoidHom (1 : MulAut ↥H) = MonoidHom.id ↥H := by
      ext x; rfl
    rw [h1, Subgroup.map_id] at h
    exact h
  have hgEq : g = k * (k⁻¹ * g) := by group
  rw [hgEq]
  exact (M ⊓ H).subgroupOf H |>.mul_mem (hNKmem hkK) (hNHR hNorm)

private theorem normalizer_quotKerImg_le {p : ℕ} [Fact p.Prime] {B R : Subgroup ↥H}
    (hNB : Subgroup.normalCore ((M ⊓ H).subgroupOf H) ≤ B)
    (hNM : Subgroup.normalCore ((M ⊓ H).subgroupOf H) ≤ (M ⊓ H).subgroupOf H)
    (hRB : R ≤ B) (hRsyl : CFSG.ABGLocalTools.IsSylowOf p R B)
    (hRM : R ≤ (M ⊓ H).subgroupOf H)
    (hNRM : Subgroup.normalizer (R.map H.subtype : Set G) ≤ M) :
    Subgroup.normalizer (R.map (QuotientGroup.mk' (Subgroup.normalCore
      ((M ⊓ H).subgroupOf H))) : Set (QuotKer M H)) ≤ quotKerImg M H M := by
  let N : Subgroup ↥H := Subgroup.normalCore ((M ⊓ H).subgroupOf H)
  let π : ↥H →* QuotKer M H := QuotientGroup.mk' N
  have hNKle : Subgroup.normalizer ((R ⊔ N : Subgroup ↥H) : Set ↥H) ≤ (M ⊓ H).subgroupOf H :=
    normalizer_sup_le_of_isSylowOf hNB hRB hRsyl hRM hNM
      (normalizer_le_subgroupOf_of_normalizer_map_le hNRM)
  have hpre : (Subgroup.normalizer (R.map π : Set (QuotKer M H))).comap π =
      Subgroup.normalizer ((R ⊔ N : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective N),
      Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  intro x hx
  obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective N x
  have hx' : x' ∈ (Subgroup.normalizer (R.map π : Set (QuotKer M H))).comap π := hx
  rw [hpre] at hx'
  exact Subgroup.mem_map_of_mem _ ((Subgroup.subgroupOf_mono H inf_le_left) (hNKle hx'))

omit [Finite G] in
private theorem kSub_le_oPPrimeHull_of_pLayerIn_le {p : ℕ} [Fact p.Prime]
    (hle : pLayerIn p H ≤ M) : kSub p M H ≤ oPPrimeHull p H := by
  rw [kSub, if_pos hle]
  refine sSup_le ?_
  rintro Y ⟨hYH, hYcard⟩ x hxY
  rw [oPPrimeHull]
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  · refine Subgroup.subset_closure ⟨hYH hxY, 1, ?_⟩
    have hdiv : orderOf x ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hxY
    rw [hYcard] at hdiv
    have hxord : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    simpa using ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdiv).resolve_left hxord

private theorem quotKerImg_ne_bot_of_not_dvd {d : ℕ} (hd : d.Prime)
    (hN : ¬ d ∣ Nat.card (Subgroup.normalCore ((M ⊓ H).subgroupOf H)))
    {D : Subgroup G} (hDH : D ≤ H) (hD : IsPGroup d D) (hD1 : D ≠ ⊥) :
    quotKerImg M H D ≠ ⊥ := by
  have : Fact d.Prime := ⟨hd⟩
  intro hbot
  let N : Subgroup ↥H := Subgroup.normalCore ((M ⊓ H).subgroupOf H)
  let π : ↥H →* QuotKer M H := QuotientGroup.mk' N
  have hmap : (D.subgroupOf H).map π = ⊥ := hbot
  have hle : D.subgroupOf H ≤ N := by
    simpa [π, N, QuotientGroup.ker_mk'] using
      (Subgroup.map_eq_bot_iff (D.subgroupOf H)).mp hmap
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hD1 (Subgroup.card_eq_one.mp hn)
  have hdvdD : d ∣ Nat.card D := by
    rw [hn]
    exact dvd_pow_self d hn0
  have hcard : Nat.card (D.subgroupOf H) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
  exact hN (hdvdD.trans (hcard ▸ Subgroup.card_dvd_of_le hle))

private theorem quotKerImg_sylow_d (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf d (quotKerImg M H D) ⊤ ∧ quotKerImg M H D ≠ ⊥ := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hDsylH : CFSG.ABGLocalTools.IsSylowOf d D H :=
    isSylowOf_H_of_isSylowOf_inf h hns hd hD hD1
  have hDsylH' : CFSG.ABGLocalTools.IsSylowOf d (D.subgroupOf H) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := d) H
      (A := D.subgroupOf H) (B := ⊤)]
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hD.le.trans inf_le_left),
      Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨isSylowOf_quotKerImg hDsylH' (by simp),
    quotKerImg_ne_bot_of_not_dvd (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1)
      (not_dvd_card_normalCore_of_twelveCtx h hns hd)
      (hD.le.trans inf_le_left) hD.isPGroup hD1⟩

private theorem oPPrimeHull_le_M_of_quotKerImg_le (h : TwelveCtx G M p Q H)
    (hIleM : oPPrimeHull p (⊤ : Subgroup (QuotKer M H)) ≤ quotKerImg M H M) :
    oPPrimeHull p H ≤ M := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  let N : Subgroup ↥H := Subgroup.normalCore ((M ⊓ H).subgroupOf H)
  let π : ↥H →* QuotKer M H := QuotientGroup.mk' N
  have hHullB : oPPrimeHull p (⊤ : Subgroup ↥H) ≤ (quotKerImg M H M).comap π := by
    rw [← Subgroup.map_le_iff_le_comap]
    rw [CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.map_oPPrimeHull π ⊤,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact hIleM
  have hBleM : oPPrimeHull p (⊤ : Subgroup ↥H) ≤ (M ⊓ H).subgroupOf H := by
    intro x hx
    have hx' := hHullB hx
    dsimp only [π, N, quotKerImg] at hx'
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr ((Subgroup.normalCore_le _).trans
        (Subgroup.subgroupOf_mono H inf_le_left))] at hx'
    exact Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hx', x.2⟩
  rw [← map_subtype_oPPrimeHull_top H p]
  exact (Subgroup.map_mono hBleM).trans (by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    exact inf_le_left)

private theorem quotKerImg_inf_sup_ne (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hle : pLayerIn p H ≤ M) {D : Subgroup G} :
    quotKerImg M H M ⊓
        (oPPrimeHull p (⊤ : Subgroup (QuotKer M H)) ⊔ quotKerImg M H D) ≠
      oPPrimeHull p (⊤ : Subgroup (QuotKer M H)) ⊔ quotKerImg M H D := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  intro heq
  have hIleM : oPPrimeHull p (⊤ : Subgroup (QuotKer M H)) ≤ quotKerImg M H M :=
    le_sup_left.trans (heq.ge.trans inf_le_left)
  exact (not_kSub_le_M_of_nineNineOne h hI)
    ((kSub_le_oPPrimeHull_of_pLayerIn_le hle).trans
      (oPPrimeHull_le_M_of_quotKerImg_le h hIleM))

omit [Finite G] in
private theorem subgroupOf_le_comap_oPPrimeHull {p : ℕ} [Fact p.Prime]
    (π : ↥H →* QuotKer M H) {E : Subgroup G} (hE : IsPGroup p E) :
    E.subgroupOf H ≤ (oPPrimeHull p (⊤ : Subgroup (QuotKer M H))).comap π := by
  intro x hx
  rw [Subgroup.mem_comap]
  let E' : Subgroup ↥H := E.subgroupOf H
  have hE'p : IsPGroup p E' := hE.comap_subtype (K := H)
  have hx' : x ∈ E' := hx
  obtain ⟨k, hk⟩ := (hE'p.map π).exists_orderOf_eq_pow
    ⟨π x, Subgroup.mem_map_of_mem π hx'⟩
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, k, ?_⟩
  simpa using hk
private theorem exists_sylowP_quotKer (hI : NineNineOneInput) (h : TwelveCtx G M p Q H) :
    ∃ P : Subgroup (QuotKer M H), CFSG.ABGLocalTools.IsSylowOf p P ⊤ ∧
      Subgroup.normalizer (P : Set (QuotKer M H)) ≤ quotKerImg M H M := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  let N : Subgroup ↥H := Subgroup.normalCore ((M ⊓ H).subgroupOf H)
  let π : ↥H →* QuotKer M H := QuotientGroup.mk' N
  let I : Subgroup (QuotKer M H) := oPPrimeHull p (⊤ : Subgroup (QuotKer M H))
  let B : Subgroup ↥H := I.comap π
  have : Finite (QuotKer M H) :=
    Finite.of_surjective π (QuotientGroup.mk'_surjective N)
  have hBindex : B.index = I.index :=
    Subgroup.index_comap_of_surjective (H := I) (f := π) (QuotientGroup.mk'_surjective N)
  have hIcop : p.Coprime I.index := by
    rw [show I = CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual p
        (QuotKer M H) from CFSG.GroupTheory.oPPrimeHull_top_eq_primeResidual]
    exact CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_coprime_index p _
  have hNleB : N ≤ B := by
    dsimp only [N, B]
    simpa only [π, QuotientGroup.ker_mk'] using Subgroup.ker_le_comap (f := π) I
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hEH : E ≤ H := hEQ.trans h.Q_le_H
  let E' : Subgroup ↥H := E.subgroupOf H
  have hE'p : IsPGroup p E' := hE.isPGroup.comap_subtype (K := H)
  have hE'B : E' ≤ B := subgroupOf_le_comap_oPPrimeHull π hE.isPGroup
  obtain ⟨R, hE'R⟩ := (hE'p.comap_subtype (K := B)).exists_le_sylow
  let Rsub : Subgroup ↥H := (R : Subgroup B).map B.subtype
  have hRsylB : CFSG.ABGLocalTools.IsSylowOf p Rsub B := ⟨R, rfl⟩
  have hRB : Rsub ≤ B := Subgroup.map_subtype_le _
  have hE'Rsub : E' ≤ Rsub := by
    have h := Subgroup.map_mono (f := B.subtype) hE'R
    change (E'.subgroupOf B).map B.subtype ≤ (R : Subgroup B).map B.subtype at h
    rwa [Subgroup.map_subgroupOf_eq_of_le hE'B] at h
  have hER : E ≤ Rsub.map H.subtype := by
    rw [← (show E'.map H.subtype = E by
      dsimp only [E']
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEH])]
    exact Subgroup.map_mono hE'Rsub
  obtain ⟨hRM, hNRM⟩ := le_M_and_normalizer_le_of_le hI h hEQ hE hEc hΓ
    (hRsylB.isPGroup.map H.subtype) hER
  have hRsubM : Rsub ≤ (M ⊓ H).subgroupOf H := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := H)]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    exact le_inf hRM (Subgroup.map_subtype_le Rsub)
  let P : Subgroup (QuotKer M H) := Rsub.map π
  refine ⟨P, isSylowOf_quotKerImg hRsylB (by rw [hBindex]; exact hIcop), ?_⟩
  exact normalizer_quotKerImg_le hNleB (Subgroup.normalCore_le _) hRB hRsylB hRsubM hNRM

private theorem isStronglyPEmbedded_quotKerImg (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded d (quotKerImg M H M) := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  obtain ⟨n, hn⟩ := hD.isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hD1 (Subgroup.card_eq_one.mp hn)
  have hdvdD : d ∣ Nat.card D := by
    rw [hn]; exact dvd_pow_self d hn0
  have hdvdHM : d ∣ Nat.card (H ⊓ M : Subgroup G) := hdvdD.trans (Subgroup.card_dvd_of_le hD.le)
  let N : Subgroup ↥H := Subgroup.normalCore ((M ⊓ H).subgroupOf H)
  let π : ↥H →* QuotKer M H := QuotientGroup.mk' N
  have hHM_eq : (H ⊓ M).subgroupOf H = M.subgroupOf H := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hMbar_eq : ((H ⊓ M).subgroupOf H).map π = quotKerImg M H M := by
    rw [hHM_eq]; rfl
  rw [← hMbar_eq]
  have hsub : CFSG.RankThree.PartOne.IsStronglyPEmbedded d ((H ⊓ M).subgroupOf H) :=
    CFSG.RankThree.PartOne.IsStronglyPEmbedded.subgroupOf
      (isStronglyPEmbedded_of_twelveCtx' h hns d hd) h.not_H_le_M hdvdHM
  have hNleY : N ≤ (H ⊓ M).subgroupOf H := by
    rw [inf_comm H M]
    exact Subgroup.normalCore_le _
  exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.map_quotient hsub hNleY
    (not_dvd_card_normalCore_of_twelveCtx h hns hd)

private theorem gammaIn_quotKerImg_le (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    gammaIn 1 d (quotKerImg M H D)
        (oPPrimeHull p (⊤ : Subgroup (QuotKer M H)) ⊔ quotKerImg M H D) ≤
      quotKerImg M H M := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hdvdD : d ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := hD.isPGroup.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hD1 (Subgroup.card_eq_one.mp hn)
    rw [hn]
    exact dvd_pow_self d hn0
  have hdvdHM : d ∣ Nat.card (H ⊓ M : Subgroup G) := hdvdD.trans (Subgroup.card_dvd_of_le hD.le)
  have hstrong := isStronglyPEmbedded_quotKerImg h hns hd hD hD1
  have hDbarp : IsPGroup d (quotKerImg M H D) :=
    (hD.isPGroup.comap_subtype (K := H)).map _
  have hDbar_le : quotKerImg M H D ≤ quotKerImg M H M := by
    dsimp only [quotKerImg]
    exact Subgroup.map_mono
      (Subgroup.subgroupOf_mono H (hD.le.trans inf_le_right))
  refine (CFSG.LocalAnalysis.AGL81I.Section3.gammaIn_le_gammaOver (Fact.out : d.Prime).one_lt
    (quotKerImg M H D) (oPPrimeHull p ⊤ ⊔ quotKerImg M H D)).trans ?_
  rw [CFSG.LocalAnalysis.AGL81TheoremCD.Section12.gammaOver]
  refine iSup₂_le fun F hF => iSup_le fun hrank => ?_
  have hFne : F ≠ ⊥ := by
    rintro rfl
    rw [CFSG.AGLEmbedding.pRank_bot_eq_zero
      (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1)] at hrank
    omega
  exact inf_le_left.trans (hstrong.normalizer_le hFne (hDbarp.to_le hF)
    (hF.trans hDbar_le))

theorem exists_threeTenHyp_quotKer (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M) (hle : pLayerIn p H ≤ M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    ∃ P : Subgroup (QuotKer M H),
      CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenHyp
        (oPPrimeHull p (⊤ : Subgroup (QuotKer M H))) (quotKerImg M H D) P
        (quotKerImg M H M ⊓
          (oPPrimeHull p (⊤ : Subgroup (QuotKer M H)) ⊔ quotKerImg M H D)) p d := by
  have hd' := mem_sigma_prime_odd_ne_p h hd
  obtain ⟨hDsyl, hDbar_ne⟩ := quotKerImg_sylow_d h hns hd hD hD1
  obtain ⟨P, hPsyl, hPnorm⟩ := exists_sylowP_quotKer hI h
  let I : Subgroup (QuotKer M H) := oPPrimeHull p (⊤ : Subgroup (QuotKer M H))
  let Mbar : Subgroup (QuotKer M H) := quotKerImg M H M
  let Dbar : Subgroup (QuotKer M H) := quotKerImg M H D
  let Y : Subgroup (QuotKer M H) := Mbar ⊓ (I ⊔ Dbar)
  have hYne : Y ≠ I ⊔ Dbar := quotKerImg_inf_sup_ne hI h hle
  have hY : Y < (I ⊔ Dbar : Subgroup (QuotKer M H)) :=
    lt_of_le_of_ne inf_le_right hYne
  have hγ : gammaIn 1 d Dbar (I ⊔ Dbar) ≤ Y :=
    le_inf (gammaIn_quotKerImg_le h hns hd hD hD1)
      (CFSG.LocalAnalysis.AGL81I.Section3.gammaIn_le 1 d Dbar (I ⊔ Dbar))
  have hNfield : Subgroup.normalizer (P : Set (QuotKer M H)) ⊓ I ≤ Y :=
    le_inf (inf_le_left.trans hPnorm) (inf_le_right.trans le_sup_left)
  exact ⟨P, h.p_prime, h.p_odd, hd'.1, hd'.2.1, hd'.2.2, rfl, hDsyl, hDbar_ne, hPsyl,
    hY, hγ, hNfield⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
