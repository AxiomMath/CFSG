module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.PComponentCover
import CFSG.GroupTheory.CyclicAutOmega
import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.Walter.Transitivity.OddCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement Pointwise

private theorem mem_pPrimeCore_map_subtype_iff {X : Type} [Group X] {p : ℕ}
    {K : Subgroup X} {z : X} (hz : z ∈ K) :
    z ∈ (CFSG.pPrimeCore p ↥K).map K.subtype ↔
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)) ⟨z, hz⟩ = 1 := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyz⟩
    have hzy : (⟨z, hz⟩ : ↥K) = y := Subtype.ext hyz.symm
    rw [hzy]
    exact (QuotientGroup.eq_one_iff _).mpr hy
  · intro h
    exact ⟨⟨z, hz⟩, (QuotientGroup.eq_one_iff _).mp h, rfl⟩

private theorem quotient_pPrimeCore_perfect {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {K : Subgroup X} (hK : CFSG.IsPComponent p K) :
    Group.IsPerfect (↥K ⧸ CFSG.pPrimeCore p ↥K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple
    p K hK).1

private theorem pRank_quotient_pPrimeCore_eq_one {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {K : Subgroup X} (hr : CFSG.Open.pRank 3 K = 1)
    (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K)) :
    CFSG.pRank 3 (↥K ⧸ CFSG.pPrimeCore p ↥K) = 1 := by
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three
    (CFSG.pPrimeCore p ↥K) hcop, CFSG.SectionRank.pRank_coe_eq_openPRank 3 K]
  exact hr

private theorem isCyclic_sylow_three_of_pRank_eq_one {Y : Type} [Group Y] [Finite Y]
    (hrank : CFSG.pRank 3 Y = 1) (Q : Sylow 3 Y) :
    IsCyclic ↥(Q : Subgroup Y) := by
  refine CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
    Nat.prime_three (by norm_num) Q.isPGroup' ?_
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank 3 (Q : Subgroup Y)]
  have h1 : CFSG.Open.pRank 3 (Q : Subgroup Y) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
    CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 Y] at h1
  exact h1.trans (le_of_eq hrank)

theorem inf_pPrimeCore_map_eq_bot {X : Type} [Group X] {p : ℕ} {K A : Subgroup X}
    (hA3 : Nat.card A = 3) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K)) :
    A ⊓ (CFSG.pPrimeCore p ↥K).map K.subtype = ⊥ := by
  have hcardN : Nat.card ((CFSG.pPrimeCore p ↥K).map K.subtype) =
      Nat.card (CFSG.pPrimeCore p ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  refine (Subgroup.disjoint_of_coprime_natCard (H := A) (K := _) ?_).eq_bot
  rw [hA3, hcardN]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcop

private theorem card_map_subgroupOf_quotient_eq_three {X : Type} [Group X] [Finite X] {p : ℕ}
    {K A : Subgroup X} (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K)) :
    Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥K))) = 3 := by
  haveI : Nontrivial A := (Finite.one_lt_card_iff_nontrivial).1 (by rw [hA3]; norm_num)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have hinf : A ⊓ (CFSG.pPrimeCore p ↥K).map K.subtype = ⊥ :=
    inf_pPrimeCore_map_eq_bot hA3 hcop
  set aX : X := (a : X) with haX
  have haK : aX ∈ K := hAK a.2
  set abar : ↥K ⧸ CFSG.pPrimeCore p ↥K :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)) ⟨aX, haK⟩ with habar
  have habar1 : abar ≠ 1 := by
    intro h
    have hmem : (⟨aX, haK⟩ : ↥K) ∈ CFSG.pPrimeCore p ↥K := (QuotientGroup.eq_one_iff _).mp h
    have hAN : aX ∈ A ⊓ (CFSG.pPrimeCore p ↥K).map K.subtype :=
      ⟨a.2, Subgroup.mem_map.mpr ⟨⟨aX, haK⟩, hmem, rfl⟩⟩
    rw [hinf, Subgroup.mem_bot] at hAN
    exact ha (Subtype.ext hAN)
  have hcube : abar ^ 3 = 1 := by
    have hord : orderOf aX ∣ 3 := by
      rw [← hA3]
      exact Subgroup.orderOf_dvd_natCard A a.2
    have hpow : aX ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hord
    have hpowK : (⟨aX, haK⟩ : ↥K) ^ 3 = 1 := Subtype.ext hpow
    rw [habar, ← map_pow, hpowK, map_one]
  have hordbar : orderOf abar = 3 := orderOf_eq_prime (p := 3) hcube habar1
  set Abar : Subgroup (↥K ⧸ CFSG.pPrimeCore p ↥K) :=
    (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)) with hAbar
  have habarA' : abar ∈ Abar := Subgroup.mem_map.mpr ⟨⟨aX, haK⟩, a.2, rfl⟩
  have h3dvd : 3 ∣ Nat.card Abar := by
    have h := Subgroup.orderOf_dvd_natCard Abar habarA'
    rw [hordbar] at h
    exact h
  have hdvd : Nat.card Abar ∣ 3 := by
    rw [hAbar, ← hA3, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact Subgroup.card_map_dvd (A.subgroupOf K) _
  exact (Nat.dvd_antisymm h3dvd hdvd).symm

private theorem omega_map_subtype_eq_of_card_three {Y : Type} [Group Y] [Finite Y]
    {Q Z : Subgroup Y} [IsCyclic ↥Q] (hZQ : Z ≤ Q) (hZcard : Nat.card Z = 3) :
    (CFSG.omega₁ ↥Q (p := 3)).map Q.subtype = Z := by
  letI : CommGroup ↥Q := IsCyclic.commGroup
  have h3Q : 3 ∣ Nat.card ↥Q := by
    have h := Subgroup.card_dvd_of_le hZQ
    rwa [hZcard] at h
  have hle : Z ≤ (CFSG.omega₁ ↥Q (p := 3)).map Q.subtype := by
    intro z hz
    have hz3 : z ^ 3 = 1 := by
      have h := Subgroup.orderOf_dvd_natCard Z hz
      rw [hZcard] at h
      exact (orderOf_dvd_iff_pow_eq_one).mp h
    exact Subgroup.mem_map.mpr ⟨⟨z, hZQ hz⟩,
      (CFSG.mem_omega₁_iff_of_comm (fun a b => mul_comm a b)).mpr (Subtype.ext hz3), rfl⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective Q.subtype_injective, CFSG.card_omega₁_of_isCyclic,
    Nat.gcd_eq_right h3Q, hZcard]

private theorem exists_inverting_image_quotient {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {K A : Subgroup X} (hK : CFSG.IsPComponent p K)
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hAK : A ≤ K) (hA3 : Nat.card A = 3) :
    ∃ n ∈ Subgroup.normalizer
        (((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)) :
          Subgroup (↥K ⧸ CFSG.pPrimeCore p ↥K)) : Set (↥K ⧸ CFSG.pPrimeCore p ↥K)),
      ∀ (a : X) (ha : a ∈ A),
        n * (QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)) ⟨a, hAK ha⟩ * n⁻¹ =
          ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)) ⟨a, hAK ha⟩)⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set PC := CFSG.pPrimeCore p ↥K with hPC
  set Abar : Subgroup (↥K ⧸ PC) := (A.subgroupOf K).map (QuotientGroup.mk' PC) with hAbar
  have hAbarCard : Nat.card Abar = 3 :=
    card_map_subgroupOf_quotient_eq_three hAK hA3 hcop
  haveI hperf : Group.IsPerfect (↥K ⧸ PC) := quotient_pPrimeCore_perfect hp hK
  have hAbarP : IsPGroup 3 ↥Abar :=
    IsPGroup.iff_card.2 ⟨1, by rw [hAbarCard]; norm_num⟩
  obtain ⟨Q, hAbarQ⟩ := hAbarP.exists_le_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup (↥K ⧸ PC)) :=
    isCyclic_sylow_three_of_pRank_eq_one
      (pRank_quotient_pPrimeCore_eq_one hp hr hcop) Q
  have hQne : (Q : Subgroup (↥K ⧸ PC)) ≠ ⊥ := by
    intro hbot
    have hle : Abar ≤ (⊥ : Subgroup (↥K ⧸ PC)) := hbot ▸ hAbarQ
    have hdvd : Nat.card Abar ∣ 1 := by
      simpa using Subgroup.card_dvd_of_le hle
    rw [hAbarCard] at hdvd
    omega
  haveI : IsCyclic ↥(Q : Subgroup (↥K ⧸ PC)) := hQcyc
  obtain ⟨n, hnNorm, hnInv⟩ :=
    CFSG.GroupTheory.exists_mem_normalizer_conj_eq_inv_of_perfect
      (X := ↥K ⧸ PC) Q hQne
  have hΩeq : (CFSG.omega₁ ↥(Q : Subgroup (↥K ⧸ PC)) (p := 3)).map
      (Q : Subgroup (↥K ⧸ PC)).subtype = Abar :=
    omega_map_subtype_eq_of_card_three hAbarQ hAbarCard
  refine ⟨n, ?_, ?_⟩
  · rw [← hΩeq]
    exact normalizer_le_normalizer_omega₁_map_subtype (Q : Subgroup (↥K ⧸ PC)) hnNorm
  · intro a ha
    have hā : (QuotientGroup.mk' PC) ⟨a, hAK ha⟩ ∈
        (CFSG.omega₁ ↥(Q : Subgroup (↥K ⧸ PC)) (p := 3)).map
          (Q : Subgroup (↥K ⧸ PC)).subtype := by
      rw [hΩeq, hAbar]
      exact Subgroup.mem_map.mpr ⟨⟨a, hAK ha⟩, ha, rfl⟩
    exact hnInv _ hā

private theorem exists_mem_inf_centralizer_inverting_mod_core {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {K : Subgroup X} (hK : CFSG.IsPComponent p K)
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    {B₁ B₂ A : Subgroup X} (hB₁ : IsPGroup 3 ↥B₁) (hB₂ : IsPGroup 3 ↥B₂)
    (hc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hB₂K : B₂ ≤ Subgroup.normalizer (K : Set X))
    (hcomm₁ : ⁅B₁, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hcomm₂ : ⁅B₂, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAK : A ≤ K) (hA3 : Nat.card A = 3) :
    ∃ c ∈ K ⊓ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup X) : Set X),
      ∀ (a : X) (ha : a ∈ A),
        (c * a * c⁻¹) * a ∈ (CFSG.pPrimeCore p ↥K).map K.subtype := by
  classical
  set PC := CFSG.pPrimeCore p ↥K with hPC
  set N : Subgroup X := PC.map K.subtype with hN
  have hNK : N ≤ K := Subgroup.map_subtype_le _
  have hKN : K ≤ Subgroup.normalizer (N : Set X) :=
    CFSG.Walter.Transitivity.le_normalizer_map_pPrimeCore K
  have hcopN : ¬ 3 ∣ Nat.card N := by
    rw [hN, Subgroup.card_map_of_injective K.subtype_injective]
    exact hcop
  obtain ⟨n, hnNorm, hnInv⟩ :=
    exists_inverting_image_quotient hp hK hr hcop hAK hA3
  obtain ⟨b, hbn⟩ := QuotientGroup.mk'_surjective PC n
  have hbK : ((b : ↥K) : X) ∈ K := b.2
  obtain ⟨c, hcC, hcN⟩ := CFSG.GroupTheory.exists_mem_inf_centralizer_sup
    Nat.prime_three Nat.prime_three hNK hKN hB₁ hB₂ hc hB₁K hB₂K hcomm₁ hcomm₂ hcopN hcopN hbK
  refine ⟨c, hcC, ?_⟩
  have hcK : c ∈ K := hcC.1
  have hcNin : c⁻¹ * (b : X) ∈ N := hcN
  have hmul : (QuotientGroup.mk' PC) ⟨c⁻¹ * (b : X),
      K.mul_mem (K.inv_mem hcK) hbK⟩ = 1 :=
    (mem_pPrimeCore_map_subtype_iff (K := K) (K.mul_mem (K.inv_mem hcK) hbK)).mp hcNin
  have hrw : (QuotientGroup.mk' PC) ⟨c⁻¹ * (b : X), K.mul_mem (K.inv_mem hcK) hbK⟩ =
      ((QuotientGroup.mk' PC) ⟨c, hcK⟩)⁻¹ * n := by
    rw [show (⟨c⁻¹ * (b : X), K.mul_mem (K.inv_mem hcK) hbK⟩ : ↥K) =
      (⟨c, hcK⟩ : ↥K)⁻¹ * b from Subtype.ext rfl]
    rw [map_mul, map_inv, hbn]
  rw [hrw] at hmul
  have hcn : (QuotientGroup.mk' PC) ⟨c, hcK⟩ = n := by
    have h2 : (QuotientGroup.mk' PC) ⟨c, hcK⟩ *
        (((QuotientGroup.mk' PC) ⟨c, hcK⟩)⁻¹ * n) = n := by group
    rwa [hmul, mul_one] at h2
  intro a ha
  have hca : (QuotientGroup.mk' PC) ⟨c * a * c⁻¹, K.mul_mem (K.mul_mem hcK (hAK ha))
      (K.inv_mem hcK)⟩ =
      ((QuotientGroup.mk' PC) ⟨a, hAK ha⟩)⁻¹ := by
    rw [show (⟨c * a * c⁻¹, K.mul_mem (K.mul_mem hcK (hAK ha)) (K.inv_mem hcK)⟩ : ↥K) =
      (⟨c, hcK⟩ : ↥K) * ⟨a, hAK ha⟩ * (⟨c, hcK⟩ : ↥K)⁻¹ from Subtype.ext rfl]
    rw [map_mul, map_mul, map_inv, hcn]
    exact hnInv a ha
  have hK1 : c * a * c⁻¹ ∈ K := K.mul_mem (K.mul_mem hcK (hAK ha)) (K.inv_mem hcK)
  have hK2 : (c * a * c⁻¹) * a ∈ K := K.mul_mem hK1 (hAK ha)
  have hprod : (QuotientGroup.mk' PC) ⟨(c * a * c⁻¹) * a, hK2⟩ = 1 := by
    rw [show (⟨(c * a * c⁻¹) * a, hK2⟩ : ↥K) = ⟨c * a * c⁻¹, hK1⟩ * ⟨a, hAK ha⟩
      from Subtype.ext rfl]
    rw [map_mul, hca, inv_mul_cancel]
  exact (mem_pPrimeCore_map_subtype_iff hK2).mpr hprod

private theorem isSylowOf_three_of_card_eq_mul {X : Type} [Group X] [Finite X]
    {P K D : Subgroup X} (hPK : P ≤ K) (hPcard : Nat.card P = 3)
    (hP3 : IsPGroup 3 ↥P) (hcard : Nat.card K = Nat.card P * Nat.card D)
    (hDcop : ¬ 3 ∣ Nat.card D) :
    CFSG.ABGLocalTools.IsSylowOf 3 P K := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hPK, hP3, ?_⟩
  have h1 : P.relIndex K * Nat.card P = Nat.card P * Nat.card D := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := K)
    rw [inf_eq_left.mpr hPK, hcard] at h
    exact h
  have hidx : P.relIndex K = Nat.card D := by
    rw [hPcard] at h1
    exact Nat.mul_right_cancel (by norm_num : 0 < 3) (by simpa [mul_comm] using h1)
  rw [hidx]
  exact hDcop

private theorem map_conj_eq_self_of_mem {X : Type} [Group X] {A : Subgroup X} {a : X}
    (ha : a ∈ A) : A.map (MulAut.conj a).toMonoidHom = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)

theorem exists_mem_inf_conj_eq_of_isSylowOf {X : Type} [Group X] [Finite X]
    {A D C P : Subgroup X} (hAC : A ≤ C)
    (hDnorm : C ≤ Subgroup.normalizer (D : Set X))
    (hADcard : Nat.card (A ⊔ D : Subgroup X) = 3 * Nat.card D) (hDcop : ¬ 3 ∣ Nat.card D)
    (hA3 : Nat.card A = 3) (hPcard : Nat.card P = 3) (hP3 : IsPGroup 3 ↥P)
    (hPAD : P ≤ (A ⊔ D : Subgroup X)) :
    ∃ d ∈ D, P = A.map (MulAut.conj d).toMonoidHom := by
  have hA3g : IsPGroup 3 ↥A := IsPGroup.iff_card.2 ⟨1, by rw [hA3]; norm_num⟩
  have hADcard' : Nat.card (A ⊔ D : Subgroup X) = Nat.card A * Nat.card D := by
    rw [hADcard, hA3]
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A (A ⊔ D : Subgroup X) :=
    isSylowOf_three_of_card_eq_mul (D := D) le_sup_left hA3 hA3g hADcard' hDcop
  have hADcardP : Nat.card (A ⊔ D : Subgroup X) = Nat.card P * Nat.card D := by
    rw [hADcard', hPcard, hA3]
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P (A ⊔ D : Subgroup X) :=
    isSylowOf_three_of_card_eq_mul (D := D) hPAD hPcard hP3 hADcardP hDcop
  obtain ⟨k, hk, hkrel⟩ := hAsyl.exists_mem_conj hPsyl
  have hPk : P = A.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    exact ⟨fun hx => ⟨k⁻¹ * x * k, (hkrel x).mp hx, by
        change (MulAut.conj k) (k⁻¹ * x * k) = x
        rw [MulAut.conj_apply]
        group⟩,
      fun ⟨a, ha, hax⟩ => by
        rw [← hax]
        refine (hkrel _).mpr ?_
        have hka : (MulAut.conj k).toMonoidHom a = k * a * k⁻¹ := by
          change (MulAut.conj k) a = k * a * k⁻¹
          rw [MulAut.conj_apply]
        rw [hka]
        have hx' : k⁻¹ * (k * a * k⁻¹) * k = a := by group
        simpa [hx'] using ha⟩
  have hkAD : k ∈ D ⊔ A := by
    rw [sup_comm]
    exact hk
  have hmul : (↑(D ⊔ A) : Set X) = (D : Set X) * (A : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left D A (hAC.trans hDnorm)
  have hkDA : k ∈ (D : Set X) * (A : Set X) := hmul ▸ hkAD
  obtain ⟨d, hdD, a, haA, hda⟩ := hkDA
  refine ⟨d, hdD, ?_⟩
  rw [hPk, ← hda]
  have haMap : A.map (MulAut.conj a).toMonoidHom = A := map_conj_eq_self_of_mem haA
  have hcomp : (MulAut.conj d * MulAut.conj a).toMonoidHom =
      (MulAut.conj d).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
    ext x
    rw [MonoidHom.comp_apply]
    change (MulAut.conj d * MulAut.conj a) x = (MulAut.conj d) ((MulAut.conj a) x)
    rw [MulAut.mul_apply]
  rw [map_mul, hcomp, ← Subgroup.map_map, haMap]

theorem exists_inverting_of_conj_eq {X : Type} [Group X]
    {N K C A : Subgroup X} {c d : X}
    (hKN : K ≤ Subgroup.normalizer (N : Set X))
    (hAK : A ≤ K) (hcC : c ∈ C) (hdN : d ∈ N) (hdC : d ∈ C)
    (hAN : A ⊓ N = ⊥)
    (hmod : ∀ (a : X) (ha : a ∈ A), (c * a * c⁻¹) * a ∈ N)
    (hconj : A.map (MulAut.conj c).toMonoidHom = A.map (MulAut.conj d).toMonoidHom) :
    ∃ t ∈ C, ∀ (a : X) (ha : a ∈ A), t * a * t⁻¹ = a⁻¹ := by
  have hNconj : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N :=
    fun k hk n hn => (Subgroup.mem_normalizer_iff.mp (hKN hk) n).mp hn
  refine ⟨d⁻¹ * c, C.mul_mem (C.inv_mem hdC) hcC, fun a ha => ?_⟩
  have hwN : (c * a * c⁻¹) * a ∈ N := hmod a ha
  have hmem : c * a * c⁻¹ ∈ A.map (MulAut.conj c).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, ha, by
      change (MulAut.conj c) a = c * a * c⁻¹
      rw [MulAut.conj_apply]⟩
  rw [hconj] at hmem
  obtain ⟨a', ha', ha'eq⟩ := Subgroup.mem_map.mp hmem
  have ha'conj : d * a' * d⁻¹ = c * a * c⁻¹ := by
    change (MulAut.conj d) a' = c * a * c⁻¹
    exact ha'eq
  have htaA : (d⁻¹ * c) * a * (d⁻¹ * c)⁻¹ ∈ A := by
    have h : (d⁻¹ * c) * a * (d⁻¹ * c)⁻¹ = a' := by
      rw [show a' = d⁻¹ * (c * a * c⁻¹) * d by rw [← ha'conj]; group]
      group
    rw [h]
    exact ha'
  have hnN : a * (c * a * c⁻¹) ∈ N := by
    have h := hNconj a (hAK ha) ((c * a * c⁻¹) * a) hwN
    rwa [show a * ((c * a * c⁻¹) * a) * a⁻¹ = a * (c * a * c⁻¹) by group] at h
  have hdaN : a * d⁻¹ * a⁻¹ ∈ N := by
    have h := hNconj a (hAK ha) d⁻¹ (N.inv_mem hdN)
    rwa [show a * d⁻¹ * a⁻¹ = a * d⁻¹ * a⁻¹ by rfl] at h
  have hmN : (a * d⁻¹ * a⁻¹) * (a * (c * a * c⁻¹)) * d ∈ N :=
    N.mul_mem (N.mul_mem hdaN hnN) hdN
  have heq : (d⁻¹ * c) * a * (d⁻¹ * c)⁻¹ =
      a⁻¹ * ((a * d⁻¹ * a⁻¹) * (a * (c * a * c⁻¹)) * d) := by group
  have hmA : (a * d⁻¹ * a⁻¹) * (a * (c * a * c⁻¹)) * d ∈ A := by
    have hma : a * ((d⁻¹ * c) * a * (d⁻¹ * c)⁻¹) =
        (a * d⁻¹ * a⁻¹) * (a * (c * a * c⁻¹)) * d := by group
    rw [← hma]
    exact A.mul_mem ha htaA
  have hbot : ((a * d⁻¹ * a⁻¹) * (a * (c * a * c⁻¹)) * d) ∈ (⊥ : Subgroup X) := by
    rw [← hAN]
    exact ⟨hmA, hmN⟩
  rw [Subgroup.mem_bot] at hbot
  rw [heq, hbot, mul_one]

theorem exists_inv_mem_inf_centralizer_sup {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {K : Subgroup X} (hK : CFSG.IsPComponent p K)
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    {B₁ B₂ A : Subgroup X} (hB₁ : IsPGroup 3 B₁) (hB₂ : IsPGroup 3 B₂)
    (hc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hB₂K : B₂ ≤ Subgroup.normalizer (K : Set X))
    (hcomm₁ : ⁅B₁, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hcomm₂ : ⁅B₂, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hAc : A ≤ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup X) : Set X)) :
    ∃ t ∈ K ⊓ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup X) : Set X),
      ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  classical
  set PC := CFSG.pPrimeCore p ↥K with hPC
  set N : Subgroup X := PC.map K.subtype with hN
  set C : Subgroup X := K ⊓ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup X) : Set X) with hC
  have hNK : N ≤ K := Subgroup.map_subtype_le _
  have hKN : K ≤ Subgroup.normalizer (N : Set X) :=
    CFSG.Walter.Transitivity.le_normalizer_map_pPrimeCore K
  have hcopN : ¬ 3 ∣ Nat.card N := by
    rw [hN, Subgroup.card_map_of_injective K.subtype_injective]
    exact hcop
  have hAC : A ≤ C := le_inf hAK hAc
  have hAN : A ⊓ N = ⊥ := inf_pPrimeCore_map_eq_bot hA3 hcop
  obtain ⟨c, hcC, hmod⟩ := exists_mem_inf_centralizer_inverting_mod_core hp hK hr hcop
    hB₁ hB₂ hc hB₁K hB₂K hcomm₁ hcomm₂ hAK hA3
  have hNconj : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N :=
    fun k hk n hn => (Subgroup.mem_normalizer_iff.mp (hKN hk) n).mp hn
  set D : Subgroup X := N ⊓ C with hD
  have hDcop : ¬ 3 ∣ Nat.card D := fun h =>
    hcopN (h.trans (Subgroup.card_dvd_of_le (inf_le_left : D ≤ N)))
  have hDnorm : C ≤ Subgroup.normalizer (D : Set X) :=
    (le_inf (inf_le_left.trans hKN) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hADdisj : Disjoint D A := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    calc D ⊓ A ≤ N ⊓ A := inf_le_inf inf_le_left le_rfl
      _ = ⊥ := by rw [inf_comm]; exact hAN
  have hADcard : Nat.card (A ⊔ D : Subgroup X) = 3 * Nat.card D := by
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      D A (hAC.trans hDnorm) hADdisj
    rw [sup_comm, hcard, hA3, Nat.mul_comm]
  have hA3g : IsPGroup 3 ↥A := IsPGroup.iff_card.2 ⟨1, by rw [hA3]; norm_num⟩
  set P : Subgroup X := A.map (MulAut.conj c).toMonoidHom with hP
  have hPcard : Nat.card P = 3 := by
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj c).injective, hA3]
  have hP3 : IsPGroup 3 ↥P := hA3g.map (MulAut.conj c).toMonoidHom
  have hPAD : P ≤ (A ⊔ D : Subgroup X) := by
    rintro z ⟨a, ha, haz⟩
    have hcaC : c * a * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hcC (hAC ha)) (C.inv_mem hcC)
    have hz : z = c * a * c⁻¹ := by
      rw [← haz]
      change (MulAut.conj c) a = c * a * c⁻¹
      rw [MulAut.conj_apply]
    rw [hz]
    have hnN : a * (c * a * c⁻¹) ∈ N := by
      have h := hNconj a (hAK ha) ((c * a * c⁻¹) * a) (hmod a ha)
      rwa [show a * ((c * a * c⁻¹) * a) * a⁻¹ = a * (c * a * c⁻¹) by group] at h
    have hnD : a * (c * a * c⁻¹) ∈ D := ⟨hnN, C.mul_mem (hAC ha) hcaC⟩
    rw [show c * a * c⁻¹ = a⁻¹ * (a * (c * a * c⁻¹)) by group]
    exact Subgroup.mul_mem_sup (A.inv_mem ha) hnD
  obtain ⟨d, hdD, hconj⟩ := exists_mem_inf_conj_eq_of_isSylowOf hAC hDnorm
    hADcard hDcop hA3 hPcard hP3 hPAD
  exact exists_inverting_of_conj_eq hKN hAK hcC hdD.1 hdD.2 hAN hmod hconj

end CFSG.GroupTheory
