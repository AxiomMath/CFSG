module

public import CFSG.Open.PGLModelDefs
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.Models.PGLOrders
import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl2
import CFSG.Quasithin.H13.A5S136r
import CFSG.Quasithin.Background.A3Structure318Star
import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.Quasithin CFSG.LocalCores

theorem map_pPrimeCore_three_le_center {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hne : CFSG.pPrimeCore 3 K ≠ ⊤) :
    (CFSG.pPrimeCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Type := K ⧸ CFSG.pCore 2 K
  let q : K →* Y := QuotientGroup.mk' (CFSG.pCore 2 K)
  let N : Subgroup Y := (CFSG.pPrimeCore 3 K).map q
  have hker : ¬ 3 ∣ Nat.card q.ker := by
    have hkerq : q.ker = CFSG.pCore 2 K := QuotientGroup.ker_mk' _
    rw [hkerq]
    intro hdvd
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hn] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hcoreY : CFSG.pPrimeCore 3 Y = N := by
    have hmap := (CFSG.prime_complement_kernel_core_preimage (p := 3) q
      (QuotientGroup.mk'_surjective _) hker).2
    exact hmap.symm
  have hcomapY : (CFSG.pPrimeCore 3 Y).comap q = CFSG.pPrimeCore 3 K :=
    (CFSG.prime_complement_kernel_core_preimage (p := 3) q
      (QuotientGroup.mk'_surjective _) hker).1
  have hNproper : N ≠ ⊤ := by
    intro htop
    apply hne
    have : (CFSG.pPrimeCore 3 Y).comap q = ⊤ := by
      rw [hcoreY, htop]
      simp
    rwa [hcomapY] at this
  rcases quasisimple_normal_subgroups hq (N := CFSG.pPrimeCore 3 Y)
    CFSG.pPrimeCore_normal with htop | hcenter
  · exact absurd (hcoreY.symm.trans htop) hNproper
  · rwa [hcoreY] at hcenter

theorem center_noTwo_of_pCore_two_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.pCore 2 Y = ⊥) :
    ∀ z ∈ Subgroup.center Y, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
  intro z hz k hzk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Subgroup.zpowers z ≤ CFSG.pCore 2 Y := by
    refine le_sSup ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz), ?_⟩
    have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hzk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  rw [hY] at hsub
  exact Subgroup.mem_bot.mp (hsub (Subgroup.mem_zpowers z))

theorem pCore_two_eq_pPrimeCore_three
    {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hL : Nonempty ((K ⧸ CFSG.pPrimeCore 3 K) ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2))) :
    CFSG.pCore 2 K = CFSG.pPrimeCore 3 K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Type := K ⧸ CFSG.pCore 2 K
  let q : K →* Y := QuotientGroup.mk' (CFSG.pCore 2 K)
  let N : Subgroup Y := (CFSG.pPrimeCore 3 K).map q
  have hO2le : CFSG.pCore 2 K ≤ CFSG.pPrimeCore 3 K :=
    CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num)
  have hker : ¬ 3 ∣ Nat.card q.ker := by
    have hkerq : q.ker = CFSG.pCore 2 K := QuotientGroup.ker_mk' _
    rw [hkerq]
    intro hdvd
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hn] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hcoreY : CFSG.pPrimeCore 3 Y = N := by
    have hmap := (CFSG.prime_complement_kernel_core_preimage (p := 3) q
      (QuotientGroup.mk'_surjective _) hker).2
    exact hmap.symm
  have hO3ne : CFSG.pPrimeCore 3 K ≠ ⊤ := by
    intro htop
    obtain ⟨e⟩ := hL
    have hcard : Nat.card (K ⧸ CFSG.pPrimeCore 3 K) = 1 := by
      rw [htop]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
    have h20160 : Nat.card (K ⧸ CFSG.pPrimeCore 3 K) = 20160 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.PGLModel.card_projSL_three_four
    omega
  have hNle : N ≤ Subgroup.center Y := map_pPrimeCore_three_le_center hq hO3ne
  have hadm : StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hbase : CFSG.Quasithin.IsPSL 3 2 2
      (CFSG.PGLModel.projSL 3 (GaloisField 2 2)) :=
    CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm (MulEquiv.refl _)
  obtain ⟨e⟩ := hL
  have hmod : CFSG.Quasithin.IsPSL 3 2 2 (K ⧸ CFSG.pPrimeCore 3 K) :=
    CFSG.Quasithin.IsPSL.of_mulEquiv e.symm hbase
  have eYN : Y ⧸ N ≃* K ⧸ CFSG.pPrimeCore 3 K :=
    QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 K)
      (CFSG.pPrimeCore 3 K) hO2le
  have hYN : CFSG.Quasithin.IsPSL 3 2 2 (Y ⧸ N) :=
    CFSG.Quasithin.IsPSL.of_mulEquiv eYN.symm hmod
  have hYperf : Group.IsPerfect Y := hq.1
  have hNcenter : N = Subgroup.center Y := by
    have hNker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' _
    have hker_le : (QuotientGroup.mk' N).ker ≤ Subgroup.center Y := by
      rw [hNker]
      exact hNle
    have hcomap := comap_center_eq_of_perfect hYperf (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) hker_le
    have hquot : Subgroup.center (Y ⧸ N) = ⊥ :=
      CFSG.Quasithin.H13.A5.center_eq_bot_of_isPSL34 hYN
    rw [hquot, MonoidHom.comap_bot] at hcomap
    rw [hNker] at hcomap
    exact hcomap
  have hYcenterPSL : CFSG.Quasithin.IsPSL 3 2 2 (Y ⧸ Subgroup.center Y) := by
    have eYCenter : Y ⧸ Subgroup.center Y ≃* K ⧸ CFSG.pPrimeCore 3 K :=
      (QuotientGroup.quotientMulEquivOfEq hNcenter).symm.trans eYN
    exact CFSG.Quasithin.IsPSL.of_mulEquiv eYCenter.symm hmod
  have hNcop : Nat.Coprime 3 (Nat.card N) := by
    rw [← hcoreY]
    exact CFSG.pPrimeCore_coprime_card
  have hNcard : Nat.card N ∣ 3 := by
    rw [hNcenter]
    exact CFSG.Quasithin.H13.S126P31.card_center_dvd_three_of_quotient
      hYperf.commutator_eq_top
      (center_noTwo_of_pCore_two_eq_bot
        (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 2) (H := K))) hYcenterPSL
  have hNbot : N = ⊥ := by
    have hcard1 : Nat.card N = 1 :=
      (hNcop.symm.eq_one_of_dvd hNcard)
    exact Subgroup.card_eq_one.mp hcard1
  have hO3le : CFSG.pPrimeCore 3 K ≤ CFSG.pCore 2 K := by
    have hmapbot : (CFSG.pPrimeCore 3 K).map q = ⊥ := by
      change N = ⊥
      exact hNbot
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmapbot
  exact le_antisymm hO2le hO3le

theorem nonempty_mulEquiv_quotient_pCore_two
    {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hL : Nonempty ((K ⧸ CFSG.pPrimeCore 3 K) ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2))) :
    Nonempty ((K ⧸ CFSG.pCore 2 K) ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2)) := by
  obtain ⟨e⟩ := hL
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (pCore_two_eq_pPrimeCore_three hq ⟨e⟩)).trans e⟩

theorem pCore_two_eq_pPrimeCore_three_of_a11 {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hA : Nonempty ((K ⧸ CFSG.pPrimeCore 3 K) ≃* alternatingGroup (Fin 11))) :
    CFSG.pCore 2 K = CFSG.pPrimeCore 3 K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Type := K ⧸ CFSG.pCore 2 K
  let q : K →* Y := QuotientGroup.mk' (CFSG.pCore 2 K)
  let N : Subgroup Y := (CFSG.pPrimeCore 3 K).map q
  have hne : CFSG.pPrimeCore 3 K ≠ ⊤ := by
    intro htop
    obtain ⟨e⟩ := hA
    have hcard : Nat.card (K ⧸ CFSG.pPrimeCore 3 K) = 1 := by
      rw [htop]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
    have hcardA : Nat.card (K ⧸ CFSG.pPrimeCore 3 K) = 19958400 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num
    omega
  have hNle : N ≤ Subgroup.center Y := map_pPrimeCore_three_le_center hq hne
  have hYperf : Group.IsPerfect Y := hq.1
  have hO2Y : CFSG.pCore 2 Y = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 2) (H := K)
  have hNodd : Odd (Nat.card N) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have h2dvd : 2 ∣ Nat.card N := even_iff_two_dvd.mp heven
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2dvd
    have hz2N : z ^ 2 = 1 := by
      simpa [hzord] using pow_orderOf_eq_one z
    have hz2 : (z : Y) ^ 2 = 1 := by
      have h := congrArg (fun w : ↥N => (w : Y)) hz2N
      simpa using h
    have hz1 : (z : Y) = 1 :=
      center_noTwo_of_pCore_two_eq_bot hO2Y (z : Y) (hNle z.2) 1 (by simpa using hz2)
    have hz1' : z = 1 := Subtype.ext hz1
    rw [hz1', orderOf_one] at hzord
    omega
  obtain ⟨e⟩ := hA
  have eYN : Y ⧸ N ≃* K ⧸ CFSG.pPrimeCore 3 K :=
    QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 K)
      (CFSG.pPrimeCore 3 K)
      (CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num))
  let η : Y →* alternatingGroup (Fin 11) :=
    (eYN.trans e).toMonoidHom.comp (QuotientGroup.mk' N)
  have hη : Function.Surjective η :=
    (eYN.trans e).surjective.comp (QuotientGroup.mk'_surjective N)
  have hηker : η.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (eYN.trans e) ((QuotientGroup.mk' N) x) = 1 := hx
      exact (QuotientGroup.eq_one_iff x).mp ((eYN.trans e).injective (by simpa using h1))
    · intro hx
      have h1 : (QuotientGroup.mk' N) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show (eYN.trans e) ((QuotientGroup.mk' N) x) = 1
      rw [h1, map_one]
  have hηcenter : η.ker ≤ Subgroup.center Y := hηker ▸ hNle
  have hηodd : Odd (Nat.card η.ker) := hηker ▸ hNodd
  have hNcard1 : Nat.card N = 1 := by
    have h := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 9)
      (by norm_num) η hη hηcenter hηodd
    rwa [hηker] at h
  have hO3le : CFSG.pPrimeCore 3 K ≤ CFSG.pCore 2 K := by
    have hmapbot : (CFSG.pPrimeCore 3 K).map q = ⊥ := by
      change N = ⊥
      exact Subgroup.card_eq_one.mp hNcard1
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmapbot
  exact le_antisymm (CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3)
    (by norm_num)) hO3le

theorem nonempty_mulEquiv_quotient_pCore_two_of_a11 {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hA : Nonempty ((K ⧸ CFSG.pPrimeCore 3 K) ≃* alternatingGroup (Fin 11))) :
    Nonempty ((K ⧸ CFSG.pCore 2 K) ≃* alternatingGroup (Fin 11)) := by
  obtain ⟨e⟩ := hA
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (pCore_two_eq_pPrimeCore_three_of_a11 hq ⟨e⟩)).trans e⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
