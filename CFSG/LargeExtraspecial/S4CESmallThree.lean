module

public import CFSG.LargeExtraspecial.S4CESmallTool

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup
open scoped commutatorElement

theorem finite_map_of_finite {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (S : Subgroup G) : Finite (S.map f) :=
  Finite.of_surjective (fun x : S => (⟨f x, x, x.2, rfl⟩ : S.map f))
    (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)

theorem exists_generators {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H) {p : ℕ}
    [hp : Fact p.Prime] {S : Subgroup G} (hS : Nat.card (S.map f) ∣ p ^ 2)
    (hcyc : ¬ IsCyclic (S.map f)) :
    ∃ x ∈ S, ∃ y ∈ S, f x ^ p = 1 ∧ f y ^ p = 1 ∧
      (∀ s ∈ S, ∀ t ∈ S, f s * f t = f t * f s) ∧
      ∀ s ∈ S, ∃ i j : ℤ, f s = f x ^ i * f y ^ j := by
  set T := S.map f with hT
  have := finite_map_of_finite f S
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp.out).mp hS
  have hk' : k = 2 := by
    interval_cases k
    · exfalso
      apply hcyc
      rw [pow_zero] at hk
      have : Subsingleton T := (Nat.card_eq_one_iff_unique.mp hk).1
      infer_instance
    · exact absurd (isCyclic_of_prime_card (by rw [hk, pow_one])) hcyc
    · rfl
  subst hk'
  have hexp : ∀ t : T, t ^ p = 1 := by
    intro t
    obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (hk ▸ orderOf_dvd_natCard t)
    have hj1 : j ≤ 1 := by
      by_contra hj1
      exact hcyc (isCyclic_of_orderOf_eq_card t (by rw [hj, hk, show j = 2 by omega]))
    exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow p hj1 |>.trans (by rw [pow_one]))
  have : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial, hk]
    exact Nat.one_lt_pow two_ne_zero hp.out.one_lt
  obtain ⟨xb, hxb⟩ := exists_ne (1 : T)
  obtain ⟨yb, hyb⟩ : ∃ t : T, t ∉ zpowers xb := by
    by_contra hall
    push Not at hall
    exact hcyc ⟨xb, fun t => hall t⟩
  have hcomm : ∀ s t : T, s * t = t * s :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk).is_comm.comm
  obtain ⟨x, hxS, hx⟩ := xb.2
  obtain ⟨y, hyS, hy⟩ := yb.2
  refine ⟨x, hxS, y, hyS, ?_, ?_, fun s hs t ht => ?_, fun s hs => ?_⟩
  · rw [hx]
    exact congrArg Subtype.val (hexp xb)
  · rw [hy]
    exact congrArg Subtype.val (hexp yb)
  · exact congrArg Subtype.val (hcomm ⟨f s, s, hs, rfl⟩ ⟨f t, t, ht, rfl⟩)
  set R : Subgroup T := zpowers xb
  set R' : Subgroup T := zpowers yb
  have hR'R : R' ≤ normalizer (R : Set T) := by
    rw [zpowers_le]
    refine mem_normalizer_iff.mpr fun g => ?_
    rw [hcomm yb g, mul_inv_cancel_right]
  have hRcard : Nat.card R = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hexp xb) hxb
  have hlt : R < R ⊔ R' :=
    lt_of_le_of_ne le_sup_left fun he => hyb (he ▸ mem_sup_right (mem_zpowers yb))
  have hsup : R ⊔ R' = ⊤ := by
    have h1 := card_dvd_of_le (le_top : R ⊔ R' ≤ ⊤)
    rw [card_top, hk] at h1
    obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow hp.out).mp h1
    have h2 : p < Nat.card ↥(R ⊔ R') := hRcard ▸ card_lt_of_lt hlt
    have hj' : j = 2 := by
      interval_cases j
      · rw [hj, pow_zero] at h2
        exact absurd h2 (by have := hp.out.one_lt; omega)
      · rw [hj, pow_one] at h2
        exact absurd h2 (lt_irrefl p)
      · rfl
    exact eq_top_of_card_eq _ (by rw [hj, hj', hk])
  have hsT : (⟨f s, s, hs, rfl⟩ : T) ∈ ((R ⊔ R' : Subgroup T) : Set T) := by
    rw [hsup]
    exact mem_top _
  rw [coe_mul_of_right_le_normalizer_left R R' hR'R] at hsT
  obtain ⟨r, hr, r', hr', he⟩ := hsT
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hr
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hr'
  refine ⟨i, j, ?_⟩
  have := congrArg Subtype.val he
  simp only [Subgroup.coe_mul, Subgroup.coe_zpow] at this
  rw [← this, ← hx, ← hy]

namespace CEHyp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {K : Type*} [Group K]
  {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
  (h : CEHyp π E a X E₀)
include h

theorem exists_commutator_le_zpowers [Finite K] {p : ℕ} [Fact p.Prime] {S : Subgroup K}
    (hS : Nat.card (S.map π) ∣ p ^ 2) :
    ∃ c : K, c ^ p = 1 ∧ ⁅S, S⁆ ≤ zpowers c := by
  by_cases hcyc : IsCyclic (S.map π)
  · refine ⟨1, one_pow p, ?_⟩
    rw [commutator_eq_bot_of_isMulCommutative (h.isMulCommutative_of_isCyclic hcyc)]
    exact bot_le
  obtain ⟨x, hxS, y, hyS, -, hyp, hab, hgen⟩ := exists_generators π hS hcyc
  have hcen : ∀ u ∈ S, ∀ v ∈ S, ⁅u, v⁆ ∈ center K := fun u hu v hv =>
    h.mem_center_of_mem_ker (by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hab u hu v hv)
  let R (u : K) (hu : u ∈ S) : S →* K := MonoidHom.mk' (fun v => ⁅u, (v : K)⁆) fun v v' => by
    rw [Subgroup.coe_mul]
    exact commutatorElement_mul_right_of_mem_center (hcen u hu v' v'.2)
  let L (v : K) (hv : v ∈ S) : S →* K := MonoidHom.mk' (fun u => ⁅(u : K), v⁆) fun u u' => by
    rw [Subgroup.coe_mul]
    exact commutatorElement_mul_left_of_mem_center (hcen u' u'.2 v hv)
  have hR : ∀ u hu (v : S), R u hu v = ⁅u, (v : K)⁆ := fun _ _ _ => rfl
  have hL : ∀ v hv (u : S), L v hv u = ⁅(u : K), v⁆ := fun _ _ _ => rfl
  have hdec : ∀ s : S, ∃ i j : ℤ, ∃ z : S, (z : K) ∈ π.ker ∧
      s = (⟨x, hxS⟩ : S) ^ i * (⟨y, hyS⟩ : S) ^ j * z := by
    intro s
    obtain ⟨i, j, hs⟩ := hgen s s.2
    refine ⟨i, j, ((⟨x, hxS⟩ : S) ^ i * (⟨y, hyS⟩ : S) ^ j)⁻¹ * s, ?_, by group⟩
    rw [MonoidHom.mem_ker]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, map_mul, map_inv, map_zpow,
      hs]
    group
  have hval : ∀ φ : S →* K, (∀ z : S, (z : K) ∈ π.ker → φ z = 1) → ∀ s : S,
      ∃ i j : ℤ, φ s = φ ⟨x, hxS⟩ ^ i * φ ⟨y, hyS⟩ ^ j := by
    intro φ hφ s
    obtain ⟨i, j, z, hz, rfl⟩ := hdec s
    exact ⟨i, j, by rw [map_mul, map_mul, map_zpow, map_zpow, hφ z hz, mul_one]⟩
  have hRz : ∀ u hu (z : S), (z : K) ∈ π.ker → R u hu z = 1 := fun u hu z hz => by
    rw [hR u hu, commutatorElement_eq_one_iff_mul_comm]
    exact mem_center_iff.mp (h.mem_center_of_mem_ker hz) u
  have hLz : ∀ v hv (z : S), (z : K) ∈ π.ker → L v hv z = 1 := fun v hv z hz => by
    rw [hL v hv, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp (h.mem_center_of_mem_ker hz) v).symm
  set c := ⁅x, y⁆ with hc
  have hcm : c ∈ zpowers c := mem_zpowers c
  have hcm' : ⁅y, x⁆ ∈ zpowers c := by
    rw [← commutatorElement_inv]
    exact inv_mem hcm
  have h1 : (1 : K) ∈ zpowers c := one_mem _
  have hA : ∀ u ∈ S, ⁅u, x⁆ ∈ zpowers c ∧ ⁅u, y⁆ ∈ zpowers c := by
    intro u hu
    obtain ⟨i, j, hi⟩ := hval (L x hxS) (hLz x hxS) ⟨u, hu⟩
    obtain ⟨k, l, hk⟩ := hval (L y hyS) (hLz y hyS) ⟨u, hu⟩
    simp only [hL, commutatorElement_self] at hi hk
    refine ⟨?_, ?_⟩
    · rw [hi]
      exact mul_mem (zpow_mem h1 i) (zpow_mem hcm' j)
    · rw [hk]
      exact mul_mem (zpow_mem hcm k) (zpow_mem h1 l)
  refine ⟨c, ?_, ?_⟩
  ·
    have hyk : y ^ p ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hyp]
    have := hRz x hxS ((⟨y, hyS⟩ : S) ^ p) (by simpa using hyk)
    rw [map_pow, hR x hxS] at this
    exact this
  · rw [commutator_le]
    intro u hu v hv
    obtain ⟨k, l, hk⟩ := hval (R u hu) (hRz u hu) ⟨v, hv⟩
    simp only [hR] at hk
    rw [hk]
    exact mul_mem (zpow_mem (hA u hu).1 k) (zpow_mem (hA u hu).2 l)

theorem card_ker_eq_one_or_three [Finite K] (hperf : E₀ ≤ ⁅E₀, stabIn X a⁆) {U : Subgroup K}
    (hU : U ⊓ π.ker = ⊥) {m : ℕ} (hm : Odd m) (hX : Nat.card X = Nat.card U * m)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ Nat.card X)
    (h27 : ¬ 3 ^ 3 ∣ Nat.card X) : Nat.card π.ker = 1 ∨ Nat.card π.ker = 3 := by
  have hodd := h.odd_card_ker hperf hU hm hX
  have hK := h.commutator_eq_top hperf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : ∀ {p : ℕ}, p.Prime → p ∣ Nat.card π.ker → p = 3 := by
    intro p hp hpd
    have : Fact p.Prime := ⟨hp⟩
    by_contra hp3
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hw1 : (w : K) = 1 := h.eq_one_of_mem_ker_of_pow_eq_one hK (hsq p hp hp2 hp3) w.2 (by
      rw [← Subgroup.coe_pow, ← hw, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [show w = 1 from Subtype.ext hw1, orderOf_one] at hw
    exact hp.one_lt.ne hw
  have hZ3 : IsPGroup 3 π.ker := by
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprime⟩
  let S : Sylow 3 K := default
  have hZS : π.ker ≤ S := hZ3.le_sylow_of_normal S
  have hS9 : Nat.card ((S : Subgroup K).map π) ∣ 3 ^ 2 := by
    have := finite_map_of_finite π (S : Subgroup K)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (S.isPGroup'.map π)
    have hd := card_dvd_of_le (h.range_eq ▸ map_le_range π _ : (S : Subgroup K).map π ≤ X)
    rw [hk] at hd ⊢
    refine pow_dvd_pow 3 ?_
    by_contra hk3
    exact h27 ((pow_dvd_pow 3 (by omega)).trans hd)
  obtain ⟨c, hc3, hcS⟩ := h.exists_commutator_le_zpowers hS9
  have hZc : π.ker ≤ ⁅(S : Subgroup K), (S : Subgroup K)⁆ := by
    intro z hz
    obtain ⟨n, hn⟩ := hZ3 ⟨z, hz⟩
    exact mem_commutator_of_perfect hK S.not_dvd_index (h.mem_center_of_mem_ker hz) (hZS hz)
      (n := n) (by simpa using congrArg Subtype.val hn)
  have hdvd : Nat.card π.ker ∣ 3 := by
    have h1 := card_dvd_of_le (hZc.trans hcS)
    rw [Nat.card_zpowers] at h1
    exact h1.trans (orderOf_dvd_of_pow_eq_one hc3)
  exact (Nat.dvd_prime Nat.prime_three).mp hdvd

end CEHyp

end CFSG.LargeExtraspecial.S4
