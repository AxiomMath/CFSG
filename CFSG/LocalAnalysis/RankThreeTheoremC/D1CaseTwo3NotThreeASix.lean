module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockCenterFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3LeviUnique
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InvTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InvAxis
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ConjAxis
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterMain
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Normalizes
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3HexRest
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NFAxis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Curtis.Coordinator CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.ComponentInitial LinearFlag


theorem conj_mem_perfectJoin_of_mem_normalizer {Y : Type*} [Group Y] {J : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (J : Set Y)) {x : Y} (hx : x ∈ perfectJoin J) :
    g * x * g⁻¹ ∈ perfectJoin J := by
  have hU : (perfectJoin J).map (MulAut.conj g).toMonoidHom ≤ J := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (perfectJoin_le J hy)
  have hUp : ⁅(perfectJoin J).map (MulAut.conj g).toMonoidHom,
      (perfectJoin J).map (MulAut.conj g).toMonoidHom⁆ =
      (perfectJoin J).map (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.map_commutator, perfectJoin_perfect]
  exact le_perfectJoin hU hUp ⟨x, hx, rfl⟩

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem D1CaseTwoData3.false_of_center_not_threeASix
    (hOut : KFactOutCyclic) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK : CitedBlockToralThree)
    (hZ : KFactFixCensusCenter) (h47 : SL3InvertCentre)
    {P : Sylow 3 G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoData3 3 P M H R Rbar) {z : H} (hz : D1CaseTwoCand 3 M H R z)
    (hnSP : ¬ D1CzSP 3 (z : G)) (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    (hno6 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζA : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hz' := hz
  have hz'' := hz
  obtain ⟨h, hzM, hzP, hz3, hCz, hrk, hcyc, hin⟩ := D1CaseTwoData3.nf_inputs hOut hS hKL hInv hSch
    hSyl h84 h85 h86 h93 hD2 hK hd hz hnSP hout hB0 hNH
  obtain ⟨w, hwR, hwo, hwz, hwcR, hwcP, hΩP, hΩR, -⟩ :=
    D1CaseTwoData3.exists_axis_inv hOut hS hKL hInv hSch hSyl hd hz' hnSP hout hB0
  obtain ⟨Kb, hKb, hKX, hzR, hzo, hRz, hzKb⟩ := hz''
  set S := pCoreOf 2 H with hSdef
  have hnine : NineThreeConclusion M S L := h.nineThree h93 hL
  have hX : ¬ InClassXBlock L := (h.nineThree_not_one h85 hD2 hL).1
  have hSy : ¬ IsSylowTwoOf (S ⊓ L) L := h.not_isSylowTwoOf_inf h85 hD2 hL
  have hKeq := h.toD1Escape.inf_eq_inf_normalizer_twoCore
  have hLc : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  have hNL : Subgroup.normalizer (S : Set G) ⊓ L ≤ H ⊓ M := by
    intro x hx
    rw [hKeq]
    exact ⟨hLc.le hx.2, hx.1⟩
  have hJHM : blockPL M S L ≤ barM M (H ⊓ M) := barM_mono hNL
  have hcycJ : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q :=
    fun V hV hVp Q hQ hQ3 => hcyc V (hV.trans hJHM) hVp Q hQ hQ3
  have h3A6 : ¬ (Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))) :=
    fun hh => hno6 L hL hh.1 hh.2
  set zb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ with hzb
  have hzpg : IsPGroup 3 (Subgroup.zpowers (z : G)) :=
    CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨(z : G), hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hzb, ← map_pow, h1, map_one]
  have hu := hin L hL
  have huC := h.not_mem_centralizer_block hp (by norm_num) hzM hzpg hCz hL
  have hfix : ∀ l ∈ barM M L, zb * l * zb⁻¹ = l → l ∈ blockPL M S L :=
    fun l hl hl' => h.fixed_le_barM_normalizer_inf hp (by norm_num) hzM hzpg hCz l hl hl'
  obtain ⟨e, ψ, d, he, he2, hCP, hpc, cfg⟩ := toral_setup hZ h.asc81bHyp hL hnine hX hSy hcycJ
    h3A6 hζA hζC hζ3 hζ1 hu hzb3 huC hfix
  have hZ3 : ∀ x ∈ barM M L, x ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      x ∈ Subgroup.zpowers ζ := toral_a ψ ζ hζA hζC hζ3 hζ1
  set K := GaloisField 2 e with hK
  have : NeZero e := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := blockPL M S L with hJdef
  have hJL : J ≤ barM M L := blockPL_le_barM
  set V := perfectJoin J with hVdef
  have hVJ : V ≤ J := perfectJoin_le J
  have hVp : ⁅V, V⁆ = V := perfectJoin_perfect J
  have hVmax : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ J → ⁅W, W⁆ = W → W ≤ V :=
    fun W hW hWp => le_perfectJoin hW hWp
  obtain ⟨W, hWJ, hWp, hW3⟩ := exists_perfect_three_dvd_of_compParab hCP he2 (projEquiv ψ)
  have hV3 : 3 ∣ Nat.card V := hW3.trans (Subgroup.card_dvd_of_le (hVmax W hWJ hWp))
  have hVC : V ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxV, hxC⟩ := hx
    have hVL : V ≤ barM M L := hVJ.trans hJL
    have hxL : x ∈ barM M L := hVL hxV
    have hxs : ψ ⟨x, hxL⟩ ∈ scalars 3 K :=
      (ψ_mem_scalars_iff ψ ⟨x, hxL⟩).mpr ((mem_center_iff_mem_centralizer _).mpr hxC)
    set V' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
      (V.subgroupOf (barM M L)).map ψ.toMonoidHom with hV'
    have hV'le : V' ≤ stabilizer (flagSpace 3 K d) := by
      rintro _ ⟨v, hv, rfl⟩
      exact (cfg.hJ v).mp (hVJ (Subgroup.mem_subgroupOf.mp hv))
    have hV'p : ⁅V', V'⁆ = V' := by
      have h1 : ⁅V.subgroupOf (barM M L), V.subgroupOf (barM M L)⁆ = V.subgroupOf (barM M L) := by
        apply Subgroup.map_injective (barM M L).subtype_injective
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVL, hVp]
      rw [hV', ← Subgroup.map_commutator, h1]
    have h1 := eq_one_of_mem_scalars_of_perfect cfg.hd hV'le hV'p (g := ψ ⟨x, hxL⟩)
      ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hxV, rfl⟩ hxs
    have h2 : (⟨x, hxL⟩ : ↥(barM M L)) = 1 := ψ.injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  obtain ⟨t, htN, ht2, htK, htinv⟩ :=
    D1CaseTwoData3.exists_inverting_two_element hOut hS hKL hd hKb hKX
  have htH : (t : G) ∈ H := t.2
  have hRP : R ≤ (P : Subgroup G) := hd.cfg.ext.le_P
  have hr3 : 3 ≤ Open.pRank 3 R := hd.cfg.ext.three_le_pRank
  have htM : (t : G) ∈ M := hd.cfg.ext.weakCore_le
    (normalizer_le_weakCore 3 hRP (by omega) (hr3.trans (pRank_mono 3 hp le_sup_left)) htN)
  have hLt : (t : G) ∈ Subgroup.normalizer (L : Set G) :=
    hd.mem_normalizer_of_levi hOut hS hKL hSch hKb hKX hL hVJ hVp hV3 hVC htH htM
  have hSt : (t : G) ∈ Subgroup.normalizer (S : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H htH
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkdef
  set tb := mk ⟨(t : G), htM⟩ with htb
  have htL' : tb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM htM hLt
  have htS' : tb ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM htM hSt
  have htJ : tb ∈ Subgroup.normalizer (J : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.mem_normalizer_fintype (blockPL_conj_mem h.asc81bHyp htL' htS')
  have hPM : (P : Subgroup G) ≤ M := hd.cfg.ext.sylow_le
  have hwP : w ∈ (P : Subgroup G) := hRP hwR
  have hwM : w ∈ M := hPM hwP
  have hrank3 : evenRank G = 3 := hd.cfg.glob.rank
  have h3σ : 3 ∈ rankThreeSigmaA G := hd.cfg.loc.sigma
  have hM2 : IsTwoLocal M := hd.cfg.loc.isCoreMaxLocal.1.1
  have hPN : ∀ (g : G) (hg : g ∈ (P : Subgroup G)),
      mk ⟨g, hPM hg⟩ ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun g hg => mem_normalizer_barM (hPM hg)
      (le_normalizer_of_isPGroup_three3 hrank3 h3σ hM2 hLc P.isPGroup' hPM hg)
  have hζw := zeta_mem_zpowers_mk_axis hPM hPN hζA hζC hζ3 hζ1 hZ3 hwP hwo hwcP hΩP
  have hŵo : orderOf (mk ⟨w, hwM⟩) = 3 := by
    have hP3 : IsPGroup 3 ((P : Subgroup G).subgroupOf M) := P.isPGroup'.comap_subtype
    have hw3 : w ^ 3 = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hwo] at this
    have h1 : (mk ⟨w, hwM⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨w, hwM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
      rw [this, map_one]
    have hne : mk ⟨w, hwM⟩ ≠ 1 := by
      intro h1'
      have := eq_of_mk_pCore_two_eq_of_isPGroup_three hP3 (a := ⟨w, hwM⟩) (b := 1) hwP
        (one_mem _) (by rw [h1', map_one])
      have h2 : w = 1 := by simpa using congrArg Subtype.val this
      rw [h2, orderOf_one] at hwo
      omega
    exact orderOf_eq_prime h1 hne
  have hmk1 : tb * ζ * tb⁻¹ ∈ Subgroup.zpowers ζ := by
    apply hZ3
    · exact (Subgroup.mem_normalizer_iff.mp htL' ζ).mp hζA
    · refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      have hl' : tb⁻¹ * l * tb ∈ barM M L := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem htL') l).mp hl
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hζC _ hl'
      calc l * (tb * ζ * tb⁻¹) = tb * ((tb⁻¹ * l * tb) * ζ) * tb⁻¹ := by group
        _ = tb * (ζ * (tb⁻¹ * l * tb)) * tb⁻¹ := by rw [h1]
        _ = (tb * ζ * tb⁻¹) * l := by group
  have hmkw : tb * mk ⟨w, hwM⟩ * tb⁻¹ ∈ Subgroup.zpowers (mk ⟨w, hwM⟩) :=
    conj_mem_zpowers_of_zpowers_zeta hŵo hζ1 hζw hmk1
  have hwt : (t : G) * w * (t : G)⁻¹ ∈ Subgroup.zpowers w :=
    conj_axis_mem_zpowers_of_mk hPM hRP hwR hwo hwz hzR hwcR hΩR htN htM hmkw
  have hinv : (t : G) * w * (t : G)⁻¹ = w⁻¹ :=
    D1CaseTwoData3.conj_axis_eq_inv hd hKb hzR hzKb hwR hwo hwz hwcR hΩR htK htinv hwt
  have hmkinv : tb * mk ⟨w, hwM⟩ * tb⁻¹ = (mk ⟨w, hwM⟩)⁻¹ := by
    have h1 : (⟨(t : G), htM⟩ : ↥M) * ⟨w, hwM⟩ * (⟨(t : G), htM⟩ : ↥M)⁻¹ = (⟨w, hwM⟩ : ↥M)⁻¹ :=
      Subtype.ext (by simpa using hinv)
    rw [htb, ← map_inv, ← map_mul, ← map_mul, h1, map_inv]
  have hζinv : tb * ζ * tb⁻¹ = ζ⁻¹ := conj_eq_inv_of_zpowers hζw hmkinv
  set O := GLBPrimeCore 3 H with hOdef
  have hVHM : V ≤ barM M (H ⊓ M) := hVJ.trans hJHM
  obtain ⟨V', hV'le, hV'p, hV'bar⟩ :=
    exists_perfect_le_of_le_barM (inf_le_right : H ⊓ M ≤ M) hVHM hVp
  have hV'pc : V' ≤ d1PlusCore 3 H Kb :=
    hd.perfect_le_plusCore hOut hS hKL hSch hKb hKX hV'le hV'p
  refine h47 (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) J V K ψ d cfg.hd hJL cfg.hJ hVJ hVp hVmax hV3 ζ
    hζA hζC hζ3 hζ1 tb htL' htJ hζinv ⟨V ⊓ barM M O, inf_le_left, ?_, ?_, ?_⟩
  ·
    rintro v hv n ⟨hnV, hnO⟩
    refine ⟨V.mul_mem (V.mul_mem hv hnV) (V.inv_mem hv), ?_⟩
    obtain ⟨hm, hhm, rfl⟩ := hVHM hv
    obtain ⟨om, hom, rfl⟩ := hnO
    have hhmH : (hm : G) ∈ H := (Subgroup.mem_subgroupOf.mp hhm).1
    have homO : (om : G) ∈ O := Subgroup.mem_subgroupOf.mp hom
    set h₁ : H := ⟨(hm : G), hhmH⟩ with hh₁
    set o₁ : H := ⟨(om : G), glbPrimeCore_le 3 H homO⟩ with ho₁
    have hπo : QuotientGroup.mk' (primeComplementCore (G := H) 3) o₁ = 1 :=
      (mk'_primeComplementCore_eq_one_iff 3 o₁).mpr homO
    have hπ : QuotientGroup.mk' (primeComplementCore (G := H) 3) (h₁ * o₁ * h₁⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hπo, mul_one, mul_inv_cancel]
    have hO' : ((h₁ * o₁ * h₁⁻¹ : H) : G) ∈ O := (mk'_primeComplementCore_eq_one_iff 3 _).mp hπ
    refine ⟨hm * om * hm⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    simpa [hh₁, ho₁] using hO'
  ·
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h3 => ?_
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨om, hom, hxeq⟩ := x.2.2
    have h1 : orderOf (x : ↥M ⧸ CFSG.pCore 2 ↥M) ∣ orderOf om := by
      rw [← hxeq]; exact orderOf_map_dvd _ _
    have h2 : orderOf (om : G) ∣ Nat.card O :=
      Subgroup.orderOf_dvd_natCard O (Subgroup.mem_subgroupOf.mp hom)
    rw [Subgroup.orderOf_coe] at h2
    have hxo : orderOf (x : ↥M ⧸ CFSG.pCore 2 ↥M) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    rw [hxo] at h1
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime 3 H)) (h1.trans h2)
  ·
    intro v hv
    have hv' := hv
    rw [← hV'bar] at hv'
    obtain ⟨vm, hvm, rfl⟩ := hv'
    have hvpc := hV'pc (Subgroup.mem_subgroupOf.mp hvm)
    obtain ⟨hh, hhc, hhv⟩ := hvpc
    have hcomm : QuotientGroup.mk' (primeComplementCore (G := H) 3) t *
        QuotientGroup.mk' (primeComplementCore (G := H) 3) hh =
        QuotientGroup.mk' (primeComplementCore (G := H) 3) hh *
        QuotientGroup.mk' (primeComplementCore (G := H) 3) t :=
      Subgroup.mem_centralizer_iff.mp hhc _ htK
    have hπ : QuotientGroup.mk' (primeComplementCore (G := H) 3) (hh * t * hh⁻¹ * t⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    have hO' : ((hh * t * hh⁻¹ * t⁻¹ : H) : G) ∈ O := (mk'_primeComplementCore_eq_one_iff 3 _).mp hπ
    have hvvm : (vm : G) = hh := hhv.symm
    refine ⟨?_, ?_⟩
    · have h1 : tb * (mk vm)⁻¹ * tb⁻¹ ∈ V :=
        conj_mem_perfectJoin_of_mem_normalizer htJ (V.inv_mem hv)
      have h2 : mk vm * tb * (mk vm)⁻¹ * tb⁻¹ = mk vm * (tb * (mk vm)⁻¹ * tb⁻¹) := by group
      rw [h2]
      exact V.mul_mem hv h1
    · refine ⟨vm * ⟨(t : G), htM⟩ * vm⁻¹ * ⟨(t : G), htM⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · simpa [hvvm] using hO'
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv]

end CFSG.LocalAnalysis.RankThreeTheoremC
