module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenTwelve

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem S14Choice.pPrimeCore_inf_kSub_le {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet) :
    (CFSG.pPrimeCore 3 ↥M).map M.subtype ⊓ kSub 3 M H ≤
      (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, i, j, hij, hI⟩ := h.exists_twoSet h2 hK hU hL hKF
  let K : Subgroup G := kSub 3 M H
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥M).map M.subtype
  let φ : ↥K →* alternatingGroup (Fin 11) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))
  let N' : Subgroup (alternatingGroup (Fin 11)) := ((D ⊓ K).subgroupOf K).map φ
  have hI' : (((K ⊓ M).subgroupOf K).map φ) = a11TwoSetStab i j := by
    change (((K ⊓ M).subgroupOf K).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)))) = _
    rw [← Subgroup.map_map]
    simpa [K] using hI
  have hDleM : D ≤ M := Subgroup.map_subtype_le _
  have hmap : ((D ⊓ K).subgroupOf K).map φ ≤ ((K ⊓ M).subgroupOf K).map φ :=
    Subgroup.map_mono fun x hx => by
      obtain ⟨hxD, hxK⟩ := Subgroup.mem_subgroupOf.mp hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hxK, hDleM hxD⟩
  have hN'le : N' ≤ a11TwoSetStab i j := by
    refine hmap.trans ?_
    rw [hI']
  have hMD : M ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D] using CFSG.ABGLocalTools.le_normalizer_map_subtype M
      (CFSG.pPrimeCore 3 ↥M)
  have hKMinfN : (K ⊓ M).subgroupOf K ≤
      Subgroup.normalizer ((D ⊓ K).subgroupOf K : Set ↥K) := by
    intro y hy
    have hyKM : (y : G) ∈ K ⊓ M := Subgroup.mem_subgroupOf.mp hy
    rw [← Subgroup.subgroupOf_normalizer_eq (H := D ⊓ K) inf_le_right,
      Subgroup.mem_subgroupOf]
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := D) (K := K)
      ⟨hMD hyKM.2, Subgroup.le_normalizer hyKM.1⟩
  have hSN : a11TwoSetStab i j ≤
      Subgroup.normalizer (N' : Set (alternatingGroup (Fin 11))) := by
    rw [← hI']
    exact (Subgroup.map_mono hKMinfN).trans (Subgroup.le_normalizer_map φ)
  have hN'N : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (N' : Set (alternatingGroup (Fin 11))) := by
    refine (show ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤ a11TwoSetStab i j from
      ?_).trans hSN
    simpa using Subgroup.commutator_le_sup (a11TwoSetStab i j) (a11TwoSetStab i j)
  have hN'card : Nat.card N' ∣ Nat.card ↥(D ⊓ K) := by
    have h := Subgroup.card_map_dvd ((D ⊓ K).subgroupOf K) φ
    have hcard : Nat.card ↥((D ⊓ K).subgroupOf K) = Nat.card ↥(D ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ K ≤ K)).toEquiv
    rw [hcard] at h
    simpa [N'] using h
  have hD3 : ¬ 3 ∣ Nat.card D := by
    have hDcard : Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥M) := by
      simpa [D] using Subgroup.card_map_of_injective (K := CFSG.pPrimeCore 3 ↥M)
        M.subtype_injective
    rw [hDcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M))
  have hN'3 : ¬ 3 ∣ Nat.card N' := by
    intro h3
    exact hD3 (h3.trans (hN'card.trans (Subgroup.card_dvd_of_le (inf_le_left : D ⊓ K ≤ D))))
  have hN'bot : N' = ⊥ := a11TwoSetStab_threePrime_eq_bot hij hN'3 hN'le hN'N
  intro x hx
  have hxK : x ∈ K := hx.2
  have hxN : φ ⟨x, hxK⟩ ∈ N' :=
    Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
  rw [hN'bot] at hxN
  have hx1 : φ ⟨x, hxK⟩ = 1 := Subgroup.mem_bot.mp hxN
  have hmk : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨x, hxK⟩ = 1 := by
    apply e.injective
    simpa [φ] using hx1
  have hxP : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pPrimeCore 3 ↥K :=
    (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥K) _).mp hmk
  simpa [K] using Subgroup.mem_map_of_mem K.subtype hxP

theorem IsMaxInvariantTwoIn.isSylowOf_two_sup {J R H D : Subgroup G}
    (hR : IsMaxInvariantTwoIn J R H) (hNRH : Subgroup.normalizer (R : Set G) ≤ H)
    (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hcomm : ∀ d ∈ D, d ∈ H → ∀ j ∈ J, ⁅j, d⁆ ∈ R) :
    CFSG.ABGLocalTools.IsSylowOf 2 R (R ⊔ D) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V : Subgroup G := R ⊔ D
  by_contra hnot
  have hRsub : IsPGroup 2 (R.subgroupOf V) := hR.2.1.comap_subtype
  obtain ⟨S, hRS⟩ := hRsub.exists_le_sylow
  have hne : R.subgroupOf V ≠ (S : Subgroup V) := by
    intro heq
    apply hnot
    refine ⟨S, ?_⟩
    rw [← heq, Subgroup.map_subgroupOf_eq_of_le (le_sup_left : R ≤ V)]
  have hlt : R.subgroupOf V < (S : Subgroup V) := lt_of_le_of_ne hRS hne
  obtain ⟨x, hxS, hxR, hxN⟩ :=
    CFSG.RankThree.PartTwo.Late.exists_mem_normalizer_not_mem_of_lt (p := 2)
      (P := R.subgroupOf V) (Q := (S : Subgroup V)) S.isPGroup' hlt
  have hxNV : (x : G) ∈ Subgroup.normalizer (R : Set G) := by
    have hx' : x ∈ (Subgroup.normalizer (R : Set G)).subgroupOf V := by
      rw [Subgroup.subgroupOf_normalizer_eq (H := R) (le_sup_left : R ≤ V)]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hx'
  have hxmul : (x : G) ∈ (R : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R D hRD]
    exact x.2
  obtain ⟨r, hr, d, hd, hxd⟩ := hxmul
  have hd_eq : d = r⁻¹ * (x : G) := by
    rw [← hxd]
    group
  have hdV : d ∈ V := by
    rw [hd_eq]
    exact V.mul_mem (V.inv_mem ((le_sup_left : R ≤ V) hr)) x.2
  have hdS : (⟨d, hdV⟩ : V) ∈ (S : Subgroup V) := by
    have h1 : (⟨r, (le_sup_left : R ≤ V) hr⟩ : V)⁻¹ * x ∈ (S : Subgroup V) :=
      (S : Subgroup V).mul_mem ((S : Subgroup V).inv_mem
        (hRS (Subgroup.mem_subgroupOf.mpr hr))) hxS
    have h2 : (⟨r, (le_sup_left : R ≤ V) hr⟩ : V)⁻¹ * x = (⟨d, hdV⟩ : V) := by
      apply Subtype.ext
      change r⁻¹ * (x : G) = d
      rw [hd_eq]
    rwa [h2] at h1
  have hdN : d ∈ Subgroup.normalizer (R : Set G) := by
    rw [hd_eq]
    exact (Subgroup.normalizer (R : Set G)).mul_mem
      ((Subgroup.normalizer (R : Set G)).inv_mem (Subgroup.le_normalizer hr)) hxNV
  have hdH : d ∈ H := hNRH hdN
  have hdR : d ∉ R := by
    intro hdR
    refine hxR (Subgroup.mem_subgroupOf.mpr ?_)
    exact hxd ▸ R.mul_mem hr hdR
  let V₂ : Subgroup G := R ⊔ Subgroup.zpowers d
  have hRV₂ : R ≤ V₂ := le_sup_left
  have hdV₂ : d ∈ V₂ := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hRV₂S : R ≤ (S : Subgroup V).map V.subtype := fun r hr =>
    Subgroup.mem_map.mpr ⟨⟨r, (le_sup_left : R ≤ V) hr⟩,
      hRS (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hdV₂S : d ∈ (S : Subgroup V).map V.subtype :=
    Subgroup.mem_map.mpr ⟨⟨d, hdV⟩, hdS, rfl⟩
  have hV₂leS : V₂ ≤ (S : Subgroup V).map V.subtype :=
    sup_le hRV₂S (Subgroup.zpowers_le.mpr hdV₂S)
  have hV₂2 : IsPGroup 2 V₂ := (S.isPGroup'.map V.subtype).to_le hV₂leS
  have hV₂H : V₂ ≤ H := sup_le hR.1 (Subgroup.zpowers_le.mpr hdH)
  have hJV₂ : J ≤ Subgroup.normalizer (V₂ : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      have hjR : j ∈ Subgroup.normalizer (R : Set G) := hR.2.2.1 hj
      have hRmap : R.map (MulAut.conj j) = R :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hjR
      have hjd : j * d * j⁻¹ ∈ V₂ := by
        have hcommjd : ⁅j, d⁆ ∈ R := hcomm d hd hdH j hj
        have heq : j * d * j⁻¹ = ⁅j, d⁆ * d := by
          rw [commutatorElement_def]
          group
        rw [heq]
        exact V₂.mul_mem (Subgroup.mem_sup_left hcommjd)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
      rw [hRmap]
      exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hjd)
    · rw [Subgroup.card_map_of_injective (MulAut.conj j).injective]
  have hV₂eq : V₂ = R := hR.2.2.2 V₂ hV₂H hV₂2 hJV₂ le_sup_left
  have hdR' : d ∈ R := by
    rw [← hV₂eq]
    exact hdV₂
  exact hdR hdR'

theorem S14Choice.isSylowOf_two_sup_pPrimeCore {M H E Q R : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h525 : FiveTwentyFiveS11Use)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H) :
    CFSG.ABGLocalTools.IsSylowOf 2 R (R ⊔ (CFSG.pPrimeCore 3 ↥M).map M.subtype) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let J : Subgroup G := K ⊓ M
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥M).map M.subtype
  obtain ⟨hNRH, hRMmax⟩ :=
    h.normalizer_R_le hA h2 hpre hK hU hL hKF h525 hX hR
  have hRM : R ≤ M := hRMmax.1
  have hMD : M ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D] using CFSG.ABGLocalTools.le_normalizer_map_subtype M
      (CFSG.pPrimeCore 3 ↥M)
  have hRD : R ≤ Subgroup.normalizer (D : Set G) := hRM.trans hMD
  have hOeq : pCoreOf 2 K = (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
    simpa [K] using h.pCoreOf_two_kSub_eq_caseTwo h2
  have hOleR : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ R := by
    rw [← hOeq]
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 H := by
      simpa [K] using h.pCoreOf_two_kSub_le hK
    exact h1.trans (h.pCoreOf_two_le_of_isMaxInvariantTwoIn hR)
  have hcomm : ∀ d ∈ D, d ∈ H → ∀ j ∈ J, ⁅j, d⁆ ∈ R := by
    intro d hd hdH j hj
    have hcommD : ⁅j, d⁆ ∈ D := by
      have hconjD : j * d * j⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hMD hj.2) d).mp hd
      rw [commutatorElement_def]
      exact D.mul_mem hconjD (D.inv_mem hd)
    have hcommK : ⁅j, d⁆ ∈ K := by
      have hdNK : d ∈ Subgroup.normalizer (K : Set G) := by
        simpa [K] using hK 3 E H h.hypCGen hdH
      have hconjK : d * j⁻¹ * d⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp hdNK j⁻¹).mp (K.inv_mem hj.1)
      rw [commutatorElement_def]
      have heq : j * d * j⁻¹ * d⁻¹ = j * (d * j⁻¹ * d⁻¹) := by group
      rw [heq]
      exact K.mul_mem hj.1 hconjK
    have hDKO : D ⊓ K ≤ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
      simpa [D, K] using h.pPrimeCore_inf_kSub_le h2 hK hU hL hKF
    exact hOleR (hDKO ⟨hcommD, hcommK⟩)
  exact IsMaxInvariantTwoIn.isSylowOf_two_sup hR hNRH hRD hcomm

theorem comap_normalizer_map_le_sup_of_isSylowOf {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (O : Subgroup X) [O.Normal] {Q : Subgroup X}
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q (Q ⊔ O)) :
    (Subgroup.normalizer ((Q.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) :
        Set (X ⧸ O))).comap (QuotientGroup.mk' O) ≤
      O ⊔ Subgroup.normalizer (Q : Set X) := by
  let K := (Q.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O)
  have hK : K = Q ⊔ O := by
    dsimp [K]
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hQK : Q ≤ K := by
    rw [hK]
    exact le_sup_left
  have hQsub : IsPGroup p (Q.subgroupOf K) := hQ.isPGroup.comap_subtype
  have hQcardK : Nat.card Q = p ^ (Nat.card K).factorization p := by
    rw [hK]
    exact hQ.card_eq
  have hQsubcard : Nat.card (Q.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv]
    exact hQcardK
  intro x hx
  rw [Subgroup.mem_comap] at hx
  have hQ'K : Q.map (MulAut.conj x).toMonoidHom ≤ K := by
    rintro _ ⟨q, hq, rfl⟩
    change QuotientGroup.mk' O (x * q * x⁻¹) ∈ Q.map (QuotientGroup.mk' O)
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp (Subgroup.mem_map_of_mem _ hq)
  obtain ⟨S, hS⟩ := hQsub.exists_le_sylow
  obtain ⟨S', hS'⟩ :=
    ((hQ.isPGroup.map (MulAut.conj x).toMonoidHom).comap_subtype (K := K)).exists_le_sylow
  have hSeq : (S : Subgroup K) = Q.subgroupOf K := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hS ?_
    rw [Sylow.card_eq_multiplicity S, hQsubcard]
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S' S
  have hconj : ∀ q ∈ Q, (k : X) * (x * q * x⁻¹) * (k : X)⁻¹ ∈ Q := by
    intro q hq
    have hmem : (⟨x * q * x⁻¹, hQ'K ⟨q, hq, rfl⟩⟩ : K) ∈ (S' : Subgroup K) :=
      hS' ⟨q, hq, rfl⟩
    have hmem' : k * ⟨x * q * x⁻¹, hQ'K ⟨q, hq, rfl⟩⟩ * k⁻¹ ∈
        ((k • S' : Sylow p K) : Subgroup K) := by
      rw [CFSG.RankThreeCoreUniqueness.Helpers.sylow_conjugate_eq_map]
      exact Subgroup.mem_map_of_mem _ hmem
    rw [hk, hSeq] at hmem'
    exact hmem'
  obtain ⟨q₀, hq₀, hq₀k⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp k.property)
  have hnN : q₀⁻¹ * (k : X) * x ∈ Subgroup.normalizer (Q : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      change q₀⁻¹ * (k : X) * x * q * (q₀⁻¹ * (k : X) * x)⁻¹ ∈ Q
      have heq : q₀⁻¹ * (k : X) * x * q * (q₀⁻¹ * (k : X) * x)⁻¹ =
          q₀⁻¹ * ((k : X) * (x * q * x⁻¹) * (k : X)⁻¹) * q₀ := by group
      rw [heq]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq₀) (hconj q hq)) hq₀
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  have hxn : x * (q₀⁻¹ * (k : X) * x)⁻¹ ∈ (QuotientGroup.mk' O).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hq₀k]
    group
  rw [QuotientGroup.ker_mk'] at hxn
  have hmem := Subgroup.mul_mem_sup hxn hnN
  rwa [inv_mul_cancel_right] at hmem

theorem S14Choice.normalizer_map_R_le {M H E Q R : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h525 : FiveTwentyFiveS11Use)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H) :
    Subgroup.normalizer (((R.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) :
        Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) : Set (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) ≤
      ((H ⊓ M).subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  obtain ⟨hNRH, hRMmax⟩ :=
    h.normalizer_R_le hA h2 hpre hK hU hL hKF h525 hX hR
  have hRM : R ≤ M := hRMmax.1
  have hQ : CFSG.ABGLocalTools.IsSylowOf 2 (R.subgroupOf M) ((R.subgroupOf M) ⊔ O) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M]
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hRM]
    exact h.isSylowOf_two_sup_pPrimeCore hA h2 hpre hK hU hL hKF h525 hX hR
  have hmain := comap_normalizer_map_le_sup_of_isSylowOf (X := ↥M) (p := 2) O
    (Q := R.subgroupOf M) hQ
  refine (CFSG.AGLEmbedding.le_map_of_comap_le (QuotientGroup.mk'_surjective O) hmain).trans ?_
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hNle : Subgroup.normalizer (R.subgroupOf M) ≤ (H ⊓ M).subgroupOf M := by
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    have hn' : (n : G) ∈ Subgroup.normalizer (R : Set G) := by
      have : n ∈ (Subgroup.normalizer (R : Set G)).subgroupOf M := by
        rwa [Subgroup.subgroupOf_normalizer_eq (H := R) hRM]
      exact Subgroup.mem_subgroupOf.mp this
    exact ⟨hNRH hn', n.2⟩
  exact Subgroup.map_mono hNle

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
