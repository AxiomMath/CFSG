module

public import CFSG.LieType.ChevTwo.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem exists_mem_orderOf_of_isPGroup_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {H : Subgroup G} (hH : IsPGroup p H) (hne : H ≠ ⊥) :
    ∃ x ∈ H, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hH
  have h1 : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot H).2 hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hn, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hdvd : p ∣ Nat.card H := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨x.1, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem odd_orderOf_of_mem_isPGroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup G} (hH : IsPGroup p H) {α : G} (hα : α ∈ H) : Odd (orderOf α) := by
  obtain ⟨k, hk⟩ := hH ⟨α, hα⟩
  have hk' : α ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
  rw [hj]
  exact (hp.odd_of_ne_two hp2).pow

theorem mem_inner_of_odd_orderOf_of_card_outer_dvd_two {K : Type*} [Group K] [Finite K]
    [Finite (MulAut K)] (hO : Nat.card (Outer K) ∣ 2) {α : MulAut K} (hα : Odd (orderOf α)) :
    α ∈ inner K := by
  have h1 : orderOf (QuotientGroup.mk' (inner K) α) ∣ orderOf α := orderOf_map_dvd _ _
  have h2 : orderOf (QuotientGroup.mk' (inner K) α) ∣ 2 :=
    (orderOf_dvd_natCard _).trans hO
  have h3 : orderOf (QuotientGroup.mk' (inner K) α) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · exfalso
      rw [h] at h1
      obtain ⟨m, hm⟩ := hα
      obtain ⟨k, hk⟩ := h1
      omega
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem oppositeFixed_of_u33_facts {K : Type} [Group K] [Finite K] [Finite (MulAut K)]
    (hcardM : Nat.card (MulAut K) = 12096) (hK : Nat.card K = 6048)
    (hZ : ∀ z : K, (∀ h : K, h * z = z * h) → z = 1)
    (hE : ∀ x : K, x ^ 27 = 1 → x ^ 3 = 1)
    (hF1 : ∀ g s : K, g ^ 7 = 1 → g ≠ 1 → s * s = 1 → s ≠ 1 → g * s ≠ s * g)
    (hF3 : ∀ g h : K, g ^ 3 = 1 → g ≠ 1 → h ^ 3 = 1 → h ≠ 1 → g * h = h * g → h ≠ g →
      h ≠ g * g → ∃ x : K, (x = g ∨ x = h ∨ x = g * h ∨ x = g * h * h) ∧
        ∀ s : K, s * s = 1 → s ≠ 1 → x * s ≠ s * x)
    (hX5 : ∀ g s : K, g ^ 3 = 1 → g ≠ 1 → s * s = 1 → s ≠ 1 → g * s = s * g →
      ∃ c : K, g * c = c * g ∧ (s * (c * s * c⁻¹)) ^ 3 = 1 ∧ s * (c * s * c⁻¹) ≠ 1) :
    OppositeFixed K := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    apply hZ z
    intro h
    have hzh := congrArg (fun a : MulAut K => a h) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at hzh
    exact (mul_inv_eq_iff_eq_mul.1 hzh).symm
  have hinner : Nat.card (inner K) = 6048 := by
    rw [← hK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hO : Nat.card (Outer K) ∣ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner K)
    rw [hcardM, hinner] at h
    have h' : Nat.card (Outer K) * 6048 = 12096 := h.symm
    have h2 : Nat.card (Outer K) = 2 := by omega
    rw [h2]
  intro p hp hp2 R hR Q hQ0 hQ2 _hcore hnorm _hQR hCent
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRbot : R ≠ ⊥ := by
    rintro rfl
    apply hnorm
    rw [eq_top_iff]
    intro s _
    apply hCent
    show ∀ α ∈ (⊥ : Subgroup (MulAut K)), α s = s
    intro α hα
    rw [Subgroup.mem_bot] at hα
    rw [hα, MulAut.one_apply]
  obtain ⟨β, hβR, hβord⟩ := exists_mem_orderOf_of_isPGroup_ne_bot hp hR hRbot
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1
    (mem_inner_of_odd_orderOf_of_card_outer_dvd_two hO
      (odd_orderOf_of_mem_isPGroup hp hp2 hR hβR))
  have hgord : orderOf g = p := by
    rw [← orderOf_injective _ hinj g, hg, hβord]
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hgord
    exact hp.one_lt.ne hgord
  have hp37 : p = 3 ∨ p = 7 := by
    have hpd : p ∣ 2 ^ 5 * 3 ^ 3 * 7 := by
      rw [show (2 : ℕ) ^ 5 * 3 ^ 3 * 7 = 6048 by norm_num, ← hK, ← hgord]
      exact orderOf_dvd_natCard g
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))
          hp2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (hp.dvd_of_dvd_pow h'))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
  set P : Subgroup K := R.comap (MulAut.conj : K →* MulAut K) with hPdef
  have hmemP : ∀ y : K, y ∈ P ↔ MulAut.conj y ∈ R := fun y => Iff.rfl
  have hgP : g ∈ P := (hmemP g).2 (hg ▸ hβR)
  have hcommP : ∀ y ∈ P, ∀ s : K, (∀ α ∈ R, α s = s) → y * s = s * y := by
    intro y hy s hs
    have h := hs _ ((hmemP y).1 hy)
    rw [MulAut.conj_apply] at h
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [h]
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨hsC, hsQ⟩ := Subgroup.mem_inf.1 hs
  have hsC' : ∀ α ∈ R, α s = s := hsC
  rw [Subgroup.mem_bot]
  by_contra hs1
  obtain ⟨t, htZ, ht2o⟩ : ∃ t ∈ Subgroup.zpowers s, orderOf t = 2 := by
    obtain ⟨k, hk⟩ := hQ2 ⟨s, hsQ⟩
    have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hsk)
    have hZ2 : IsPGroup 2 (Subgroup.zpowers s) :=
      (IsPGroup.iff_card).2 ⟨m, by rw [Nat.card_zpowers, hm]⟩
    exact exists_mem_orderOf_of_isPGroup_ne_bot Nat.prime_two hZ2
      (Subgroup.zpowers_eq_bot.not.2 hs1)
  have htT : t ∈ Q ⊓ autCentralizer R := by
    have hsT : s ∈ Q ⊓ autCentralizer R := Subgroup.mem_inf.2 ⟨hsQ, hsC⟩
    exact Subgroup.zpowers_le.2 hsT htZ
  have htQ : t ∈ Q := (Subgroup.mem_inf.1 htT).1
  have htC : ∀ α ∈ R, α t = t := (Subgroup.mem_inf.1 htT).2
  have ht2 : t * t = 1 := by
    have h : t ^ 2 = 1 := by rw [← ht2o]; exact pow_orderOf_eq_one t
    rwa [pow_two] at h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2o
    exact absurd ht2o (by norm_num)
  have hRinner : ∀ α ∈ R, ∃ y : K, MulAut.conj y = α := fun α hα =>
    MonoidHom.mem_range.1 (mem_inner_of_odd_orderOf_of_card_outer_dvd_two hO
      (odd_orderOf_of_mem_isPGroup hp hp2 hR hα))
  rcases hp37 with rfl | rfl
  ·
    have hPexp : ∀ y ∈ P, y ^ 3 = 1 := by
      intro y hy
      obtain ⟨k, hk⟩ := hR ⟨MulAut.conj y, (hmemP y).1 hy⟩
      have hk' : (MulAut.conj y) ^ 3 ^ k = 1 := congrArg Subtype.val hk
      have hyk : y ^ 3 ^ k = 1 := by
        apply hinj
        rw [map_pow, hk', map_one]
      obtain ⟨j, -, hjord⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
        (orderOf_dvd_of_pow_eq_one hyk)
      have hd6048 : orderOf y ∣ 6048 := by rw [← hK]; exact orderOf_dvd_natCard y
      have hd27 : orderOf y ∣ 27 := by
        rw [hjord] at hd6048 ⊢
        have hcop : Nat.Coprime (3 ^ j) 224 := Nat.Coprime.pow_left j (by norm_num)
        have h6 : 3 ^ j ∣ 27 * 224 := hd6048
        exact hcop.dvd_of_dvd_mul_right h6
      exact hE y (orderOf_dvd_iff_pow_eq_one.1 hd27)
    have hPgrp : IsPGroup 3 P := hR.comap_of_injective MulAut.conj hinj
    have hPne : P ≠ ⊥ := fun h => hg1 (Subgroup.mem_bot.1 (h ▸ hgP))
    haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
    have hcne : Subgroup.center ↥P ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).1 (IsPGroup.center_nontrivial hPgrp)
    obtain ⟨z, hzP, hz3, hz1, hzcomm⟩ :
        ∃ z ∈ P, z ^ 3 = 1 ∧ z ≠ 1 ∧ ∀ y ∈ P, y * z = z * y := by
      obtain ⟨z0, hz0c, hz0o⟩ := exists_mem_orderOf_of_isPGroup_ne_bot (G := ↥P) Nat.prime_three
        (IsPGroup.to_subgroup hPgrp (Subgroup.center ↥P)) hcne
      refine ⟨z0, z0.2, ?_, ?_, fun y hy => ?_⟩
      · have h := pow_orderOf_eq_one z0
        rw [hz0o] at h
        simpa using congrArg Subtype.val h
      · intro h
        have h' : z0 = 1 := Subtype.ext h
        rw [h', orderOf_one] at hz0o
        exact absurd hz0o (by norm_num)
      · have h := Subgroup.mem_center_iff.1 hz0c ⟨y, hy⟩
        simpa using congrArg Subtype.val h
    have hPz : ∀ y ∈ P, y ∈ Subgroup.zpowers z := by
      intro y hy
      by_contra hyz
      have hy1 : y ≠ 1 := fun h => hyz (h ▸ Subgroup.one_mem _)
      have hyz' : y ≠ z := fun h => hyz (h ▸ Subgroup.mem_zpowers z)
      have hyz2 : y ≠ z * z := fun h => hyz (h ▸ Subgroup.mul_mem _
        (Subgroup.mem_zpowers z) (Subgroup.mem_zpowers z))
      obtain ⟨x, hx, hxs⟩ := hF3 z y hz3 hz1 (hPexp y hy) hy1 (hzcomm y hy).symm hyz' hyz2
      have hxP : x ∈ P := by
        rcases hx with rfl | rfl | rfl | rfl
        · exact hzP
        · exact hy
        · exact P.mul_mem hzP hy
        · exact P.mul_mem (P.mul_mem hzP hy) hy
      exact hxs t ht2 ht1 (hcommP x hxP t htC)
    have hCRz : ∀ c : K, z * c = c * z → ∀ α ∈ R, α c = c := by
      intro c hc α hα
      obtain ⟨y, rfl⟩ := hRinner α hα
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hPz y ((hmemP y).2 hα))
      rw [MulAut.conj_apply]
      have hcm : Commute (z ^ k) c := Commute.zpow_left (show Commute z c from hc) k
      rw [hcm.eq, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨c, hzc, hx3, hx1⟩ := hX5 z t hz3 hz1 ht2 ht1 (hcommP z hzP t htC)
    have hcC : c ∈ autCentralizer R := fun α hα => hCRz c hzc α hα
    have hconj : c * t * c⁻¹ ∈ Q := ((Subgroup.mem_normalizer_iff.1 (hCent hcC)) t).1 htQ
    have hxQ : t * (c * t * c⁻¹) ∈ Q := Q.mul_mem htQ hconj
    obtain ⟨k, hk⟩ := hQ2 ⟨_, hxQ⟩
    have hk' : (t * (c * t * c⁻¹)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))
    have h1 := (pow_gcd_eq_one (a := t * (c * t * c⁻¹))).2 ⟨hx3, hk'⟩
    rw [hcop, pow_one] at h1
    exact hx1 h1
  ·
    exact hF1 g t (by rw [← hgord]; exact pow_orderOf_eq_one g) hg1 ht2 ht1
      (hcommP g hgP t htC)

end CFSG.LieType.ChevTwo.OppCl
