module

public import CFSG.LargeExtraspecial.AS35WDefs

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

variable {X : Type} [Group X] {z : X}

theorem W2Data.twoPart_dvd [Finite X] (h : W2Data X z) :
    2 ^ (Nat.card X).factorization 2 ∣ Nat.card (centralizer ({z} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.sylow_le
  rw [← Sylow.card_eq_multiplicity P]
  exact Subgroup.card_dvd_of_le hP

theorem W2Data.pow_dvd [Finite X] (h : W2Data X z) {k : ℕ} (hk : 2 ^ k ∣ Nat.card X) :
    2 ^ k ∣ Nat.card (centralizer ({z} : Set X)) := by
  have hv : k ≤ (Nat.card X).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hk
  exact (pow_dvd_pow 2 hv).trans h.twoPart_dvd

theorem W2Data.false_of_conj_mem (h : W2Data X z) {P : Subgroup X}
    (hPC : P ≤ centralizer ({z} : Set X))
    (hPn : ∀ c ∈ centralizer ({z} : Set X), ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hP2 : IsPGroup 2 P)
    {x : X} (hxP : x ∈ P) (hxz : x ≠ z) (hc : IsConj z x) : False :=
  hxz (h.weaklyClosed x (le_oTwoCent hPC hPn hP2 hxP) hc)

theorem W2Data.false_of_not_two (h : W2Data X z) {P : Subgroup X}
    (hPC : P ≤ centralizer ({z} : Set X))
    (hPn : ∀ c ∈ centralizer ({z} : Set X), ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hP2 : IsPGroup 2 P)
    {t : X} (htP : t ∈ P) (ht2 : orderOf t = 2) {c : X} (hct : c * t = t * c)
    (hord : ∀ k : ℕ, orderOf (z * (c * z * c⁻¹)) ≠ 2 ^ k) : False := by
  have hzt : z ∈ oTwoCent t := h.mem_oTwoCent t (le_oTwoCent hPC hPn hP2 htP) ht2
  have hc : c ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.2 hct
  have hczc : c * z * c⁻¹ ∈ oTwoCent t := conj_mem_oTwoCent hc hzt
  have hm : z * (c * z * c⁻¹) ∈ oTwoCent t := (oTwoCent t).mul_mem hzt hczc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (isPGroup_oTwoCent t) ⟨_, hm⟩
  rw [Subgroup.orderOf_mk] at hk
  exact hord k hk

theorem W2Data.false_of_simple [Finite X] (h : W2Data X z) (N : Subgroup X)
    (hNC : N ≤ centralizer ({z} : Set X))
    (hNn : ∀ c ∈ centralizer ({z} : Set X), ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hs : IsSimpleGroup N)
    (hna : ∃ a b : N, a * b ≠ b * a) : False := by
  set R := oTwoCent z
  have hRN : (R.subgroupOf N).Normal := by
    refine ⟨fun r hr c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    simpa using conj_mem_oTwoCent (hNC c.2) hr
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf N) with h1 | h1
  ·
    obtain ⟨a, b, hab⟩ := hna
    have key : ∀ n ∈ N, n = 1 := by
      intro n hn
      have hc : ∀ r ∈ R, n * r = r * n := by
        intro r hr
        have hN' : n * (r * n⁻¹ * r⁻¹) ∈ N :=
          N.mul_mem hn (hNn r (oTwoCent_le_centralizer z hr) n⁻¹ (N.inv_mem hn))
        have hR' : n * r * n⁻¹ * r⁻¹ ∈ R :=
          R.mul_mem (conj_mem_oTwoCent (hNC hn) hr) (R.inv_mem hr)
        have heq : n * (r * n⁻¹ * r⁻¹) = n * r * n⁻¹ * r⁻¹ := by group
        have hmem : (⟨_, hN'⟩ : N) ∈ R.subgroupOf N := by
          rw [Subgroup.mem_subgroupOf]
          change n * (r * n⁻¹ * r⁻¹) ∈ R
          rw [heq]
          exact hR'
        rw [h1, Subgroup.mem_bot] at hmem
        have h2 : n * r * n⁻¹ * r⁻¹ = 1 := by
          rw [← heq]
          exact congrArg Subtype.val hmem
        calc n * r = n * r * n⁻¹ * r⁻¹ * (r * n) := by group
          _ = r * n := by rw [h2, one_mul]
      have hnR : n ∈ R := h.selfCentralizing n (hNC hn) hc
      have : (⟨n, hn⟩ : N) ∈ R.subgroupOf N := hnR
      rw [h1] at this
      exact congrArg Subtype.val ((Subgroup.mem_bot).1 this)
    have ha : a = 1 := Subtype.ext (key _ a.2)
    have hb : b = 1 := Subtype.ext (key _ b.2)
    exact hab (by rw [ha, hb])
  ·
    have hle : N ≤ R := by
      intro n hn
      have : (⟨n, hn⟩ : N) ∈ R.subgroupOf N := by rw [h1]; exact Subgroup.mem_top _
      exact this
    have h2 : IsPGroup 2 N := (isPGroup_oTwoCent z).to_le hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, b, hab⟩ := hna
    have hnt : Nontrivial N := ⟨⟨a * b, b * a, hab⟩⟩
    have hZ := h2.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center N) with h3 | h3
    · rw [h3] at hZ
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hZ
      rw [Subgroup.mem_bot] at hx hy
      exact hxy (Subtype.ext (hx.trans hy.symm))
    · have : a ∈ center N := by rw [h3]; exact Subgroup.mem_top _
      exact hab ((Subgroup.mem_center_iff.1 this b).symm)

end AS35W

end CFSG.LargeExtraspecial
