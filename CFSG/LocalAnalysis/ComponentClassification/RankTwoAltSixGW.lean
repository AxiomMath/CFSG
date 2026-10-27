module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenGW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixSylow

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.GorensteinWalter

section Img

variable {G : Type} [Group G]

theorem odd_card_pPrimeCore [Finite G] (K : Subgroup G) : Odd (Nat.card (pPrimeCore 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
    (pPrimeCore_coprime_card (p := 2) (G := K))
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)

theorem eq_one_of_mem_pPrimeCore_of_mul_self [Finite G] {K : Subgroup G} {h : K}
    (h2 : h * h = 1) (hO : h ∈ pPrimeCore 2 K) : h = 1 := by
  have hd2 : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  have hodd : Odd (orderOf h) :=
    Odd.of_dvd_nat (odd_card_pPrimeCore K) (Subgroup.orderOf_dvd_natCard _ hO)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

@[expose] noncomputable def imgCore (K V : Subgroup G) : Subgroup (K ⧸ pPrimeCore 2 K) :=
  ((QuotientGroup.mk' (pPrimeCore 2 K)).comp (V.subgroupOf K).subtype).range

theorem mem_imgCore_iff {K V : Subgroup G} {q : K ⧸ pPrimeCore 2 K} :
    q ∈ imgCore K V ↔ ∃ v : K, (v : G) ∈ V ∧ (v : K ⧸ pPrimeCore 2 K) = q := by
  constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩
    exact ⟨v, mem_subgroupOf.mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, mem_subgroupOf.mpr hv⟩, rfl⟩

theorem card_imgCore [Finite G] {K V : Subgroup G} (hVK : V ≤ K) (hsq : ∀ v ∈ V, v * v = 1) :
    Nat.card (imgCore K V) = Nat.card V := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' (pPrimeCore 2 K)).comp (V.subgroupOf K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : (v : K) ∈ pPrimeCore 2 K := (QuotientGroup.eq_one_iff _).mp hv
    have hv2 : (v : K) * v = 1 := Subtype.ext (hsq _ (mem_subgroupOf.mp v.2))
    exact Subtype.ext (eq_one_of_mem_pPrimeCore_of_mul_self hv2 h1)
  rw [imgCore, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv]

theorem isKleinFour_imgCore [Finite G] {K V : Subgroup G} (hVK : V ≤ K)
    (hsq : ∀ v ∈ V, v * v = 1) (h4 : Nat.card V = 4) : IsKleinFour (imgCore K V) := by
  refine isKleinFour_of_card ((card_imgCore hVK hsq).trans h4) fun y => ?_
  obtain ⟨v, hv, hvy⟩ := mem_imgCore_iff.mp y.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hvy, ← QuotientGroup.mk_pow, Subgroup.coe_one]
  have : v ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, sq]
    exact hsq _ hv)
  rw [this, QuotientGroup.mk_one]

theorem isPGroup_imgCore [Finite G] {K V : Subgroup G} (hVK : V ≤ K)
    (hsq : ∀ v ∈ V, v * v = 1) (h4 : Nat.card V = 4) : IsPGroup 2 (imgCore K V) :=
  IsPGroup.of_card (n := 2) (by rw [card_imgCore hVK hsq, h4]; norm_num)

end Img

namespace Six

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 6)} {ψB : B ≃* alternatingGroup (Fin 6)}

theorem y0_mul_self : y0 ψB * y0 ψB = 1 := by
  show ((ψB.symm e4523 : B) : G) * (ψB.symm e4523 : B) = 1
  rw [← Subgroup.coe_mul, ← map_mul, show e4523 * e4523 = 1 from Subtype.ext (by decide), map_one,
    Subgroup.coe_one]

theorem nonempty_quot_equiv_alt7
    [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G)) :
    Nonempty ((H ψA ⧸ pPrimeCore 2 (H ψA)) ≃* alternatingGroup (Fin 7)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc1 := c1_not_mem_core hco hN ht1A
  set cb := ((⟨c1 ψA, c1_mem_H⟩ : H ψA) : H ψA ⧸ pPrimeCore 2 (H ψA)) with hcb
  have hcb1 : cb ≠ 1 := fun h => hc1 ((QuotientGroup.eq_one_iff _).mp h)
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcb, ← QuotientGroup.mk_pow, show (⟨c1 ψA, c1_mem_H⟩ : H ψA) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact c1_pow_three), QuotientGroup.mk_one]
  rcases gw_cases (hasDihedralSylowTwo_H hco ht1A) with h2 | hA | ⟨K, _, _, hK, L, hLn, hLi, hLm⟩
  ·
    exfalso
    obtain ⟨k, hk⟩ := h2 cb
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcb3) (orderOf_dvd_of_pow_eq_one hk)
    rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at hd
    exact hcb1 hd
  · exact hA
  ·
    exfalso
    have := hLn
    have hRH : R ψB ≤ H ψA := R_le_B.trans (B_le_H hco)
    have hsqR : ∀ v ∈ R ψB, v * v = 1 := fun v hv => mul_self_of_mem_R hv
    have hVL : imgCore (H ψA) (R ψB) ≤ L :=
      le_of_isPGroup_two hLi (isPGroup_imgCore hRH hsqR card_R)
    have hy0H : y0 ψB ∈ H ψA := B_le_H hco y0_mem
    set yb := ((⟨y0 ψB, hy0H⟩ : H ψA) : H ψA ⧸ pPrimeCore 2 (H ψA)) with hyb
    have hyb2 : yb ^ 2 = 1 := by
      rw [hyb, ← QuotientGroup.mk_pow, show (⟨y0 ψB, hy0H⟩ : H ψA) ^ 2 = 1 from
        Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact y0_mul_self), QuotientGroup.mk_one]
    have hybL : yb ∈ L := mem_of_sq_eq_one hLi hyb2
    have hinv : yb * cb * yb⁻¹ = cb⁻¹ := by
      rw [hyb, hcb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv]
      congr 1
      exact Subtype.ext (y0_conj_c1 hco)
    have hcV : cb ∈ centralizer (imgCore (H ψA) (R ψB) : Set _) := by
      rw [mem_centralizer_iff]
      intro q hq
      obtain ⟨v, hv, rfl⟩ := mem_imgCore_iff.mp hq
      rw [hcb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext
        ((mem_centralizer_iff.mp (R_le_centralizer_A hco hv)) _ (c1_mem (ψA := ψA))).symm
    have hodd : Odd (orderOf cb) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hcb3)
    exact hcb1 (eq_one_of_linear hK hLm hVL (isKleinFour_imgCore hRH hsqR card_R) hybL hinv
      hcV hodd)

end Six

end CFSG.ComponentClassification.RankTwoAlt
