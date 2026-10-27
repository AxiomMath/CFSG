module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData

import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMComponent
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMTools
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMStepZero
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.CGT.Timmesfeld75.Sec4TwoBender
import CFSG.GH74.QTGen4.U42.VertexGen4B
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import TauCeti.RepresentationTheory.CharacterTable.Solvable
import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

namespace TwelveSixIData

theorem normalizer_le₁ (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    normalizer (D.W₁ : Set G) ≤ M :=
  normalizer_le_of_inverted D.cfg.card₁ (D.centralizer_le₁ hc) (D.t₁_mem hc.data).2
    D.cfg.inv₁

theorem normalizer_le₂ (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    normalizer (D.W₂ : Set G) ≤ M :=
  normalizer_le_of_inverted D.cfg.card₂ (D.centralizer_le₂ hc) (D.t₂_mem hc.data).2
    D.cfg.inv₂

theorem normalizer_le₃ (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    normalizer (D.W₃ : Set G) ≤ M :=
  normalizer_le_of_inverted D.cfg.card₃ (D.centralizer_le₃ hc) (D.t₃_mem hc.data).2
    D.cfg.inv₃

end TwelveSixIData

private theorem isSubnormal_sup_of_normal {H J O : Subgroup G}
    (hJ : CFSG.Open.IsSubnormal J H) (hOH : O ≤ H) (hON : (O.subgroupOf H).Normal) :
    CFSG.Open.IsSubnormal (J ⊔ O) H := by
  have hle : J ⊔ O ≤ H := sup_le hJ.le hOH
  rw [CFSG.Open.IsSubnormal.iff_subgroupOf hle, Subgroup.subgroupOf_sup hJ.le hOH]
  exact CFSG.GroupTheory.isSubnormal_sup hJ.subgroupOf hON.isSubnormal

private theorem starImg_sup_relPPrimeCore (hp : p.Prime) {H A : Subgroup G} (hAH : A ≤ H) :
    starImg p H (A ⊔ relPPrimeCore p H) = starImg p H A := by
  set P : Subgroup ↥H := primeComplementCore (G := ↥H) p with hP
  set π : ↥H →* StarGroup p H := QuotientGroup.mk' P with hπ
  have hOH : relPPrimeCore p H ≤ H := relPPrimeCore_le H
  have hOsub : (relPPrimeCore p H).subgroupOf H = P := by
    rw [nineTenGen_relPPrimeCore_eq_map hp H]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective P
  have hsub : (A ⊔ relPPrimeCore p H).subgroupOf H = A.subgroupOf H ⊔ P := by
    rw [Subgroup.subgroupOf_sup hAH hOH, hOsub]
  have hOmap : P.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  calc starImg p H (A ⊔ relPPrimeCore p H)
      = (A.subgroupOf H ⊔ P).map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
          rw [starImg, hsub]
    _ = (A.subgroupOf H ⊔ P).map π := rfl
    _ = (A.subgroupOf H).map π ⊔ P.map π := Subgroup.map_sup ..
    _ = starImg p H A := by rw [hOmap, sup_bot_eq]; rfl

private theorem pRank_sup_relPPrimeCore_le_one (hp : p.Prime)
    (hO3 : ¬ 3 ∣ Nat.card (relPPrimeCore p H)) {I : Subgroup G} (hIH : I ≤ H)
    (hIrank : CFSG.Open.pRank 3 I ≤ 1) :
    CFSG.Open.pRank 3 (I ⊔ relPPrimeCore p H) ≤ 1 := by
  set P : Subgroup ↥H := primeComplementCore (G := ↥H) p with hP
  set π : ↥H →* StarGroup p H := QuotientGroup.mk' P with hπ
  have hOH : relPPrimeCore p H ≤ H := relPPrimeCore_le H
  have hOsub : (relPPrimeCore p H).subgroupOf H = P := by
    rw [nineTenGen_relPPrimeCore_eq_map hp H]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective P
  have hcardO : Nat.card ↥((relPPrimeCore p H).subgroupOf H) = Nat.card (relPPrimeCore p H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv
  have hker : ∀ (A : Subgroup G) (hAH : A ≤ H),
      ¬ 3 ∣ Nat.card ↥((A.subgroupOf H) ⊓ π.ker) := by
    intro A hAH
    have hkerEq : π.ker = (relPPrimeCore p H).subgroupOf H := by
      rw [hπ, QuotientGroup.ker_mk', ← hOsub]
    rw [hkerEq]
    refine fun hd => hO3 ?_
    have hd' : 3 ∣ Nat.card ↥((relPPrimeCore p H).subgroupOf H) :=
      hd.trans (Subgroup.card_dvd_of_le (inf_le_right : (A.subgroupOf H) ⊓
        (relPPrimeCore p H).subgroupOf H ≤ (relPPrimeCore p H).subgroupOf H))
    rwa [hcardO] at hd' 
  have hstar : starImg p H (I ⊔ relPPrimeCore p H) = starImg p H I :=
    starImg_sup_relPPrimeCore hp hIH
  have hmapIO : ((I ⊔ relPPrimeCore p H).subgroupOf H).map π =
      starImg p H (I ⊔ relPPrimeCore p H) := rfl
  have hmapI : (I.subgroupOf H).map π = starImg p H I := rfl
  have hIOle : I ⊔ relPPrimeCore p H ≤ H := sup_le hIH hOH
  calc CFSG.Open.pRank 3 (I ⊔ relPPrimeCore p H)
      = CFSG.Open.pRank 3 ((I ⊔ relPPrimeCore p H).subgroupOf H) :=
        (CFSG.Quasithin.H13.Ch4.L436.pRank_subgroupOf_eq_pRank hIOle Nat.prime_three).symm
    _ = CFSG.Open.pRank 3 (((I ⊔ relPPrimeCore p H).subgroupOf H).map π) :=
        (nineTenGen_pRank_map_eq_of_coprime_ker (p := 3) Nat.prime_three π
          ((I ⊔ relPPrimeCore p H).subgroupOf H) (hker _ hIOle)).symm
    _ = CFSG.Open.pRank 3 (starImg p H (I ⊔ relPPrimeCore p H)) := by rw [hmapIO]
    _ = CFSG.Open.pRank 3 (starImg p H I) := by rw [hstar]
    _ = CFSG.Open.pRank 3 ((I.subgroupOf H).map π) := by rw [hmapI]
    _ = CFSG.Open.pRank 3 (I.subgroupOf H) :=
        nineTenGen_pRank_map_eq_of_coprime_ker (p := 3) Nat.prime_three π
          (I.subgroupOf H) (hker I hIH)
    _ = CFSG.Open.pRank 3 I :=
        CFSG.Quasithin.H13.Ch4.L436.pRank_subgroupOf_eq_pRank hIH Nat.prime_three
    _ ≤ 1 := hIrank

private theorem isSubnormal_inf_sup_relPPrimeCore {H I J : Subgroup G} (hp : p.Prime)
    (hIH : I ≤ H) (hJH : J ≤ H) (hJ : IsPComponentIn p J H) :
    CFSG.Open.IsSubnormal ((J ⊔ relPPrimeCore p H) ⊓ I) I := by
  have hOH : relPPrimeCore p H ≤ H := relPPrimeCore_le H
  have hON : ((relPPrimeCore p H).subgroupOf H).Normal := by
    have hHnorm : H ≤ Subgroup.normalizer (relPPrimeCore p H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp (relPPrimeCore_normal hp H)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mpr hHnorm
  obtain ⟨K, hK, hJsub, -, -⟩ := hJ.2
  have hJopen : CFSG.Open.IsSubnormal J H :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hJH).mpr hJsub
  have hJOsub : CFSG.Open.IsSubnormal (J ⊔ relPPrimeCore p H) H :=
    isSubnormal_sup_of_normal hJopen hOH hON
  exact hJOsub.inf_of_le hIH

private theorem le_sup_inf_sup_relPPrimeCore {H I J : Subgroup G} (hp : p.Prime)
    (hIH : I ≤ H) (hJH : J ≤ H) (hJI : starImg p H J ≤ starImg p H I) :
    J ≤ ((J ⊔ relPPrimeCore p H) ⊓ I) ⊔ relPPrimeCore p H := by
  have hOH : relPPrimeCore p H ≤ H := relPPrimeCore_le H
  have hO_normH : H ≤ Subgroup.normalizer (relPPrimeCore p H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp (relPPrimeCore_normal hp H)
  have hJleIO : J ≤ I ⊔ relPPrimeCore p H :=
    le_sup_relPPrimeCore_of_starImg_le hp hJH hJI
  have hded : ((J ⊔ relPPrimeCore p H) ⊓ I) ⊔ relPPrimeCore p H =
      (J ⊔ relPPrimeCore p H) ⊓ (I ⊔ relPPrimeCore p H) := by
    exact Subgroup.inf_sup_assoc_of_le (H := I) (K := J ⊔ relPPrimeCore p H)
      (N := relPPrimeCore p H) (hIH.trans hO_normH) le_sup_right
  have h1 : J ≤ (J ⊔ relPPrimeCore p H) ⊓ (I ⊔ relPPrimeCore p H) :=
    le_inf le_sup_left hJleIO
  rwa [← hded] at h1

private theorem false_of_n_eq_one_of_starImg_le {H I J : Subgroup G} {n : ℕ}
    (hIH : I ≤ H) (hJ : IsPComponentIn p J H)
    (hIt : IsPSLType 2 (GaloisField 2 n) (modTwoCore I)) (hn : n = 1)
    (hJI : starImg p H J ≤ starImg p H I) : False := by
  classical
  rw [hn] at hIt
  have hIcard : Nat.card I =
      2 ^ ((Nat.card (CFSG.pCore 2 ↥I)).factorization 2 + 1) * 3 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e⟩ := hIt
    have hQcard : Nat.card (modTwoCore I) = 6 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.GH74.QTGen4.U42.VertexGen4B.card_psl_galois (n := 1) le_rfl]
      norm_num
    obtain ⟨k0, hk0card⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
    have hfacpow : (2 ^ k0).factorization 2 = k0 := by
      rw [Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I)
    rw [h, hQcard, hk0card, hfacpow, pow_succ]
    ring
  have hJdvd : Nat.card ↥(starImg p H J) ∣
      2 ^ ((Nat.card (CFSG.pCore 2 ↥I)).factorization 2 + 1) * 3 := by
    have hIstar : Nat.card ↥(starImg p H I) ∣ Nat.card I := by
      have h := Subgroup.card_map_dvd (H := I.subgroupOf H)
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIH).toEquiv] at h
      exact h
    rw [hIcard] at hIstar
    exact (Subgroup.card_dvd_of_le hJI).trans hIstar
  have hsolv : Group.IsSolvable ↥(starImg p H J) :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (p := 2) (q := 3)
      (a := (Nat.card (CFSG.pCore 2 ↥I)).factorization 2 + 1) (b := 1)
      Nat.prime_two Nat.prime_three (by simpa using hJdvd)
  have hcomp : CFSG.IsComponent (starImg p H J) := isComponent_starImg hJ
  haveI : Nontrivial ↥(starImg p H J) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
  haveI : Group.IsPerfect ↥(starImg p H J) := hcomp.1.1
  exact Group.IsPerfect.not_isSolvable ↥(starImg p H J) hsolv

private theorem le_pCoreOf_two_of_map_eq_bot {I S : Subgroup G}
    {π : ↥I →* modTwoCore I} (hπ : π = QuotientGroup.mk' (CFSG.pCore 2 ↥I))
    (hSI : S ≤ I) (hbot : (S.subgroupOf I).map π = ⊥) : S ≤ pCoreOf 2 I := by
  intro x hx
  have hxI : x ∈ I := hSI hx
  have hxbot : (⟨x, hxI⟩ : ↥I) ∈ π.ker :=
    (Subgroup.map_eq_bot_iff (S.subgroupOf I) (f := π)).mp hbot
      (Subgroup.mem_subgroupOf.mpr hx)
  rw [hπ, QuotientGroup.ker_mk'] at hxbot
  exact Subgroup.mem_map_of_mem I.subtype hxbot

private theorem false_of_le_pCoreOf_two_of_starImg_le {H I J : Subgroup G} (hp : p.Prime)
    (hIH : I ≤ H) (hJ : IsPComponentIn p J H) (hJI : starImg p H J ≤ starImg p H I)
    (hSle : (J ⊔ relPPrimeCore p H) ⊓ I ≤ pCoreOf 2 I) : False := by
  classical
  have hJle : J ≤ ((J ⊔ relPPrimeCore p H) ⊓ I) ⊔ relPPrimeCore p H :=
    le_sup_inf_sup_relPPrimeCore hp hIH hJ.1 hJI
  have hJleO₂ : J ≤ pCoreOf 2 I ⊔ relPPrimeCore p H :=
    hJle.trans (sup_le_sup_right hSle _)
  have hJstar_le : starImg p H J ≤ starImg p H (pCoreOf 2 I) := by
    refine (Subgroup.map_mono (Subgroup.comap_mono hJleO₂)).trans ?_
    change starImg p H (pCoreOf 2 I ⊔ relPPrimeCore p H) ≤ starImg p H (pCoreOf 2 I)
    rw [starImg_sup_relPPrimeCore hp
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 I).trans hIH)]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2I : IsPGroup 2 (pCoreOf 2 I) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).map I.subtype
  have hp2IH : IsPGroup 2 ((pCoreOf 2 I).subgroupOf H) :=
    hp2I.of_equiv (Subgroup.subgroupOfEquivOfLe
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 I).trans hIH)).symm
  have h2star : IsPGroup 2 (starImg p H (pCoreOf 2 I)) :=
    hp2IH.map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
  have hJstar2 : IsPGroup 2 (starImg p H J) := h2star.to_le hJstar_le
  have hcomp : CFSG.IsComponent (starImg p H J) := isComponent_starImg hJ
  haveI : Nontrivial ↥(starImg p H J) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
  haveI : Group.IsNilpotent ↥(starImg p H J) := hJstar2.isNilpotent
  haveI : Group.IsPerfect ↥(starImg p H J) := hcomp.1.1
  exact Group.IsPerfect.not_isNilpotent ↥(starImg p H J) hJstar2.isNilpotent

private theorem three_dvd_card_of_map_eq_top {I S P : Subgroup G} {π : ↥I →* modTwoCore I}
    (h3Q : 3 ∣ Nat.card (modTwoCore I)) (hSI : S ≤ I) (hSP : S ≤ P)
    (htop : (S.subgroupOf I).map π = ⊤) : 3 ∣ Nat.card P := by
  have h3S : 3 ∣ Nat.card S := by
    have hdvd : Nat.card (⊤ : Subgroup (modTwoCore I)) ∣ Nat.card (S.subgroupOf I) := by
      rw [← htop]
      exact Subgroup.card_map_dvd (H := S.subgroupOf I) π
    have hcardS : Nat.card (S.subgroupOf I) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSI).toEquiv
    rw [Subgroup.card_top, hcardS] at hdvd
    exact h3Q.trans hdvd
  exact h3S.trans (Subgroup.card_dvd_of_le hSP)

private theorem three_dvd_card_sup_of_starImg_le_of_three_le {H I J : Subgroup G} {n : ℕ}
    (hp : p.Prime) (hIH : I ≤ H) (hJH : J ≤ H) (hJ : IsPComponentIn p J H)
    (hIt : IsPSLType 2 (GaloisField 2 n) (modTwoCore I)) (hn : 3 ≤ n)
    (hJI : starImg p H J ≤ starImg p H I) :
    3 ∣ Nat.card (J ⊔ relPPrimeCore p H : Subgroup G) := by
  classical
  set S : Subgroup G := (J ⊔ relPPrimeCore p H) ⊓ I with hS
  have hSI : S ≤ I := by rw [hS]; exact inf_le_right
  have hSJO : S ≤ J ⊔ relPPrimeCore p H := by rw [hS]; exact inf_le_left
  have hSsub : CFSG.Open.IsSubnormal S I :=
    isSubnormal_inf_sup_relPPrimeCore hp hIH hJH hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hIt
  have hQsimple : IsSimpleGroup (modTwoCore I) :=
    CFSG.CGT.Timmesfeld75.isSimpleGroup_of_psl2 (by omega : 2 ≤ n) e
  have h3Q : 3 ∣ Nat.card (modTwoCore I) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SignalizerFunctorTheorem.CatalogBridge.three_dvd_card_psl2_two_pow
      (by omega : n ≠ 0)
  set π : ↥I →* modTwoCore I := QuotientGroup.mk' (CFSG.pCore 2 ↥I) with hπ
  have hSmap : ((S.subgroupOf I).map π).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hSsub.subgroupOf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hQsimple hSmap with hbot | htop
  · have hSle : S ≤ pCoreOf 2 I := le_pCoreOf_two_of_map_eq_bot hπ hSI hbot
    exact False.elim (false_of_le_pCoreOf_two_of_starImg_le hp hIH hJ hJI hSle)
  · exact three_dvd_card_of_map_eq_top h3Q hSI hSJO htop

private theorem three_dvd_card_sup_of_starImg_le (hp : p.Prime) {H I J : Subgroup G} {n : ℕ}
    (hIH : I ≤ H) (hJH : J ≤ H) (hJ : IsPComponentIn p J H)
    (hIt : IsPSLType 2 (GaloisField 2 n) (modTwoCore I)) (hn : Odd n)
    (hJI : starImg p H J ≤ starImg p H I) :
    3 ∣ Nat.card (J ⊔ relPPrimeCore p H : Subgroup G) := by
  rcases hn with ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hn1 : n = 1 := by omega
    exact False.elim (false_of_n_eq_one_of_starImg_le hIH hJ hIt hn1 hJI)
  · have hn3 : 3 ≤ n := by omega
    exact three_dvd_card_sup_of_starImg_le_of_three_le hp hIH hJH hJ hIt hn3 hJI

private theorem exists_sylow_three_with_unique_order_three {I P : Subgroup G}
    (h3 : 3 ∣ Nat.card P) (hPIO : P ≤ I ⊔ relPPrimeCore p H)
    (hIOrank : CFSG.Open.pRank 3 (I ⊔ relPPrimeCore p H) ≤ 1) :
    ∃ (T W₀ : Subgroup G), CFSG.ABGLocalTools.IsSylowOf 3 T P ∧ W₀ ≤ T ∧
      Nat.card W₀ = 3 ∧ normalizer (T : Set G) ≤ normalizer (W₀ : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hTsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 P
  have hfac : 0 < (Nat.card P).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
  have hTcard : Nat.card T = 3 ^ (Nat.card P).factorization 3 := hTsyl.card_eq
  have h3T : 3 ∣ Nat.card T := by
    rw [hTcard]
    exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp hfac)
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 3 h3T
  let xG : G := (x : T)
  have hxGord : orderOf xG = 3 := by
    rw [show xG = ((x : ↥T) : G) from rfl, Subgroup.orderOf_coe, hxord]
  let W₀ : Subgroup G := Subgroup.zpowers xG
  have hW₀card : Nat.card W₀ = 3 := by
    rw [Nat.card_zpowers, hxGord]
  have hW₀T : W₀ ≤ T := Subgroup.zpowers_le.mpr x.2
  have hTrank : CFSG.Open.pRank 3 T ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (hTsyl.le.trans hPIO)).trans hIOrank
  have huniq : ∀ X : Subgroup G, X ≤ T → Nat.card X = 3 → X = W₀ := fun X hXT hXcard =>
    (CFSG.LocalAnalysis.RankThreeUC.eq_of_card_eq_prime_of_pRank_le_one
      (p := 3) (Q := T) (A := W₀) (B := X) hTsyl.isPGroup hTrank hW₀T hXT hW₀card hXcard).symm
  have hTnormW₀ : T ≤ normalizer (W₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine huniq _ ?_ ?_
    · rintro y ⟨z, hz, rfl⟩
      exact T.mul_mem (T.mul_mem ht (hW₀T hz)) (T.inv_mem ht)
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hW₀card]
  have hNT_le_NW₀ : normalizer (T : Set G) ≤ normalizer (W₀ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    refine huniq _ ?_ ?_
    · calc W₀.map (MulAut.conj g).toMonoidHom
          ≤ T.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hW₀T
        _ = T := hg
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hW₀card]
  exact ⟨T, W₀, hTsyl, hW₀T, hW₀card, hNT_le_NW₀⟩

private theorem normalizer_le_of_order_three_conjugate {I T W W₀ : Subgroup G}
    (hIOrank : CFSG.Open.pRank 3 (I ⊔ relPPrimeCore p H) ≤ 1)
    (hWI : W ≤ I) (hW : Nat.card W = 3) (hNW : normalizer (W : Set G) ≤ M)
    (hIOM : I ⊔ relPPrimeCore p H ≤ M)
    (hW₀IO : W₀ ≤ I ⊔ relPPrimeCore p H) (hW₀card : Nat.card W₀ = 3)
    (hNT_le : normalizer (T : Set G) ≤ normalizer (W₀ : Set G)) :
    normalizer (T : Set G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyIO, hyW'⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime (p := 3)
      hIOrank (hWI.trans le_sup_left) hW₀IO hW hW₀card
  have hyW : W₀ = W.map (MulAut.conj y).toMonoidHom := hyW'.symm
  have hyM : y ∈ M := hIOM hyIO
  have hMy : M.map (MulAut.conj y).toMonoidHom = M := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact M.mul_mem (M.mul_mem hyM hw) (M.inv_mem hyM)
    · intro hz
      refine ⟨y⁻¹ * z * y, M.mul_mem (M.mul_mem (M.inv_mem hyM) hz) hyM, ?_⟩
      change (MulAut.conj y) (y⁻¹ * z * y) = z
      rw [MulAut.conj_apply]
      group
  have hNW₀ : normalizer (W₀ : Set G) ≤ M := by
    rw [hyW, ← Subgroup.map_equiv_normalizer_eq W (MulAut.conj y)]
    calc (normalizer (W : Set G)).map (MulAut.conj y).toMonoidHom
        ≤ M.map (MulAut.conj y).toMonoidHom := Subgroup.map_mono hNW
      _ = M := hMy
  exact hNT_le.trans hNW₀

private theorem inf_normalizer_le_of_three_dvd {H I P W : Subgroup G}
    (hPH : P ≤ H) (hPM : P ≤ M)
    (hPIO : P ≤ I ⊔ relPPrimeCore p H)
    (hIOrank : CFSG.Open.pRank 3 (I ⊔ relPPrimeCore p H) ≤ 1)
    (h3 : 3 ∣ Nat.card P)
    (hWI : W ≤ I) (hW : Nat.card W = 3)
    (hNW : normalizer (W : Set G) ≤ M)
    (hIOM : I ⊔ relPPrimeCore p H ≤ M) :
    H ⊓ normalizer (P : Set G) ≤ M := by
  obtain ⟨T, W₀, hTsyl, hW₀T, hW₀card, hNT_le⟩ :=
    exists_sylow_three_with_unique_order_three h3 hPIO hIOrank
  have hW₀IO : W₀ ≤ I ⊔ relPPrimeCore p H := hW₀T.trans (hTsyl.le.trans hPIO)
  have hNT : normalizer (T : Set G) ≤ M :=
    normalizer_le_of_order_three_conjugate hIOrank hWI hW hNW hIOM hW₀IO hW₀card hNT_le
  have hPH' : P ≤ H ⊓ normalizer (P : Set G) := le_inf hPH Subgroup.le_normalizer
  have hH'norm : H ⊓ normalizer (P : Set G) ≤ normalizer (P : Set G) := inf_le_right
  have hfr := nineTenGen_frattini_le_sup_normalizer (q := 3)
    (H := H ⊓ normalizer (P : Set G)) (K := P) (S := T) hPH' hH'norm hTsyl
  exact hfr.trans (sup_le hPM (inf_le_right.trans hNT))

private theorem inf_normalizer_le_inf_normalizer_sup {H J : Subgroup G} (hp : p.Prime) :
    H ⊓ normalizer (J : Set G) ≤
      H ⊓ normalizer (((J ⊔ relPPrimeCore p H) : Subgroup G) : Set G) := by
  have hOH : relPPrimeCore p H ≤ H := relPPrimeCore_le H
  have hO_normH : H ≤ Subgroup.normalizer (relPPrimeCore p H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp (relPPrimeCore_normal hp H)
  intro g hg
  obtain ⟨hgH, hgJ⟩ := Subgroup.mem_inf.mp hg
  refine Subgroup.mem_inf.mpr ⟨hgH, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe] at hgJ ⊢
  have hOg : (relPPrimeCore p H).map (MulAut.conj g).toMonoidHom =
      relPPrimeCore p H := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hO_normH hgH))
  calc (J ⊔ relPPrimeCore p H).map (MulAut.conj g).toMonoidHom
      = (J.map (MulAut.conj g).toMonoidHom) ⊔
          ((relPPrimeCore p H).map (MulAut.conj g).toMonoidHom) := by
          rw [Subgroup.map_sup]
    _ = J ⊔ relPPrimeCore p H := by rw [hgJ, hOg]

theorem TwelveSixKCtx.inf_normalizer_le_of_starImg_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hO3 : ¬ 3 ∣ Nat.card (relPPrimeCore p H)) (hA : pLayerIn p H ≤ M)
    {L I W : Subgroup G} {n : ℕ} (hL : L ∈ weakBlockSet M H) (hIL : I ≤ H ⊓ L)
    (hn : Odd n) (hIt : IsPSLType 2 (GaloisField 2 n) (modTwoCore I))
    (hWI : W ≤ I) (hW : Nat.card W = 3) (hNW : normalizer (W : Set G) ≤ M)
    {J : Subgroup G} (hJ : IsPComponentIn p J H)
    (hJI : starImg p H J ≤ starImg p H I) :
    H ⊓ normalizer (J : Set G) ≤ M := by
  classical
  have hp : p.Prime := hc.ctx.p_prime
  have hIH : I ≤ H := hIL.trans inf_le_left
  have hIL' : I ≤ L := hIL.trans inf_le_right
  have hLrank : CFSG.Open.pRank 3 L = 1 := by
    rw [← pRank_barM_eq Nat.prime_three (by norm_num) M L hL.le, hc.hm3 L hL]
  have hIrank : CFSG.Open.pRank 3 I ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hIL').trans_eq hLrank
  have hIOrank : CFSG.Open.pRank 3 (I ⊔ relPPrimeCore p H) ≤ 1 :=
    pRank_sup_relPPrimeCore_le_one hp hO3 hIH hIrank
  have h3JO : 3 ∣ Nat.card (J ⊔ relPPrimeCore p H : Subgroup G) :=
    three_dvd_card_sup_of_starImg_le hp hIH hJ.1 hJ hIt hn hJI
  have hIM : I ≤ M := hIL'.trans hL.le
  have hOM : relPPrimeCore p H ≤ M := relPPrimeCore_le_M_of_twelveCtx hc.ctx
  have hIOM : I ⊔ relPPrimeCore p H ≤ M := sup_le hIM hOM
  have hPM : J ⊔ relPPrimeCore p H ≤ M := sup_le ((le_pLayerIn hJ).trans hA) hOM
  have hPH : J ⊔ relPPrimeCore p H ≤ H := sup_le hJ.1 (relPPrimeCore_le H)
  have hPIO : J ⊔ relPPrimeCore p H ≤ I ⊔ relPPrimeCore p H :=
    sup_le (le_sup_relPPrimeCore_of_starImg_le hp hJ.1 hJI) le_sup_right
  have hNP : H ⊓ normalizer (((J ⊔ relPPrimeCore p H) : Subgroup G) : Set G) ≤ M :=
    inf_normalizer_le_of_three_dvd hPH hPM hPIO hIOrank h3JO hWI hW hNW hIOM
  exact (inf_normalizer_le_inf_normalizer_sup hp).trans hNP

theorem TwelveSixKCtx.starImg_I_le_cStarL
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hA : pLayerIn p H ≤ M) :
    starImg p H D.I₁ ≤ cStarL p H ∧ starImg p H D.I₂ ≤ cStarL p H ∧
      starImg p H D.I₃ ≤ cStarL p H := by
  have hO3 : ¬ 3 ∣ Nat.card (relPPrimeCore p H) :=
    hc.not_three_dvd_card_relPPrimeCore D
  refine ⟨?_, ?_, ?_⟩
  · rcases starImg_le_cStarL_or_exists_isPComponentIn hc.ctx.p_prime hA
      (D.isSubnormal₁ hc.data) with h | ⟨J, hJ, hJI⟩
    · exact h
    · exact absurd (hc.le_of_inf_normalizer_le hA hJ
        (hc.inf_normalizer_le_of_starImg_le hO3 hA hc.data.mem₁ D.le_inf₁ hc.data.odd₁
          D.type₁ D.le₁ D.cfg.card₁ (D.normalizer_le₁ hc) hJ hJI)) hc.ctx.not_H_le_M
  · rcases starImg_le_cStarL_or_exists_isPComponentIn hc.ctx.p_prime hA
      (D.isSubnormal₂ hc.data) with h | ⟨J, hJ, hJI⟩
    · exact h
    · exact absurd (hc.le_of_inf_normalizer_le hA hJ
        (hc.inf_normalizer_le_of_starImg_le hO3 hA hc.data.mem₂ D.le_inf₂ hc.data.odd₂
          D.type₂ D.le₂ D.cfg.card₂ (D.normalizer_le₂ hc) hJ hJI)) hc.ctx.not_H_le_M
  · rcases starImg_le_cStarL_or_exists_isPComponentIn hc.ctx.p_prime hA
      (D.isSubnormal₃ hc.data) with h | ⟨J, hJ, hJI⟩
    · exact h
    · exact absurd (hc.le_of_inf_normalizer_le hA hJ
        (hc.inf_normalizer_le_of_starImg_le hO3 hA hc.data.mem₃ D.le_inf₃ hc.data.odd₃
          D.type₃ D.le₃ D.cfg.card₃ (D.normalizer_le₃ hc) hJ hJI)) hc.ctx.not_H_le_M

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
