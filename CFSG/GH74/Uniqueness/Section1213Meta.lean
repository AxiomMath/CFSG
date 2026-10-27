module

public import CFSG.GH74.Uniqueness.Bender.Core
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem A5.pow_dvd_sub_one_of_pow_dvd {p e r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 1 ≤ r)
    (h : p ^ e ∣ r ^ p - 1) : p ^ (e - 1) ∣ r - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have hp1 : p ∣ r ^ p - 1 := (dvd_pow_self p he.ne').trans h
  have hferm : (r : ZMod p) ^ p = r := ZMod.pow_card (r : ZMod p)
  have hrp : 1 ≤ r ^ p := Nat.one_le_pow _ _ hr
  have hpr : p ∣ r - 1 := by
    rw [← ZMod.natCast_eq_zero_iff] at hp1 ⊢
    rw [Nat.cast_sub hrp, Nat.cast_pow, hferm, Nat.cast_one] at hp1
    rw [Nat.cast_sub hr, Nat.cast_one]
    exact hp1
  rcases Nat.lt_or_ge 1 r with hr1 | hr1
  · have hndvd : ¬ p ∣ r := by
      intro hd
      have h2 : p ∣ r - (r - 1) := Nat.dvd_sub hd hpr
      rw [Nat.sub_sub_self hr] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hlte := padicValNat.pow_sub_pow (x := r) (y := 1) (p := p) hodd hr1
      (by simpa using hpr) hndvd (n := p) hp.ne_zero
    rw [one_pow, padicValNat_self] at hlte
    have hne : r ^ p - 1 ≠ 0 := by
      have : 1 < r ^ p := Nat.one_lt_pow hp.ne_zero hr1
      omega
    have hle := (padicValNat_dvd_iff_le hne).mp h
    have hne' : r - 1 ≠ 0 := by omega
    exact (padicValNat_dvd_iff_le hne').mpr (by omega)
  · have : r = 1 := le_antisymm hr1 hr
    subst this
    simp

theorem A5.commute_of_le_normalizer_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {x : G} (hx : orderOf x = p) {P : Subgroup G} (hP : IsPGroup p P)
    (hPN : P ≤ normalizer ((zpowers x : Subgroup G) : Set G)) : ∀ y ∈ P, y * x = x * y := by
  intro y hy
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x ^ k = y * x * y⁻¹ :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr
      ((mem_normalizer_iff.mp (hPN hy) x).mp (mem_zpowers x)))
  have hym : ∀ m : ℕ, y ^ m * x * (y ^ m)⁻¹ = x ^ (k ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y ^ (m + 1) * x * (y ^ (m + 1))⁻¹ = y ^ m * (y * x * y⁻¹) * (y ^ m)⁻¹ := by
            rw [pow_succ]; group
        _ = (y ^ m * x * (y ^ m)⁻¹) ^ k := by rw [← hk, conj_pow]
        _ = x ^ (k ^ (m + 1)) := by rw [ih, ← pow_mul, pow_succ]
  obtain ⟨a, ha⟩ := hP ⟨y, hy⟩
  have hya : y ^ (p ^ a) = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have h1 : x ^ (k ^ (p ^ a)) = x := by
    have := hym (p ^ a)
    rw [hya, one_mul, inv_one, mul_one] at this
    exact this.symm
  have hk1 : x ^ k = x := by
    have h3 : ((k ^ (p ^ a) : ℕ) : ZMod p) = (k : ZMod p) := by
      rw [Nat.cast_pow, ZMod.pow_card_pow]
    have h4 : x ^ (k ^ (p ^ a)) = x ^ k := by
      rw [← pow_mod_orderOf, hx, ← ZMod.val_natCast, h3, ZMod.val_natCast, ← hx, pow_mod_orderOf]
    rw [← h4, h1]
  calc y * x = y * x * y⁻¹ * y := by group
    _ = x * y := by rw [← hk, hk1]

theorem A5.commutator_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {C : Subgroup G} (hC : IsCyclic C) (hCp : IsPGroup p C) {y : G}
    (hy : y ^ p = 1) (hyC : y ∈ normalizer (C : Set G)) {c : G} (hc : c ∈ C) :
    c * y * c⁻¹ * y⁻¹ ∈ C ∧ (c * y * c⁻¹ * y⁻¹) ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hC.exists_generator
  set g₀ : G := (g : G) with hg₀
  have hpow : ∀ a ∈ C, ∃ m : ℕ, g₀ ^ m = a := by
    intro a ha
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (hg ⟨a, ha⟩))
    exact ⟨m, by rw [hg₀, ← Subgroup.coe_pow, hm]⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hCp
  have hord : orderOf g₀ = p ^ e := by
    rw [hg₀, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, he]
  obtain ⟨r₀, hr₀⟩ := hpow _ ((mem_normalizer_iff.mp hyC g₀).mp g.2)
  set r : ℕ := r₀ + orderOf g₀ with hr
  have hr1 : 1 ≤ r := by
    have := orderOf_pos g₀
    omega
  have hyg : y * g₀ * y⁻¹ = g₀ ^ r := by
    rw [hr, pow_add, pow_orderOf_eq_one, mul_one, hr₀]
  have hym : ∀ m : ℕ, y ^ m * g₀ * (y ^ m)⁻¹ = g₀ ^ (r ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y ^ (m + 1) * g₀ * (y ^ (m + 1))⁻¹ = y ^ m * (y * g₀ * y⁻¹) * (y ^ m)⁻¹ := by
            rw [pow_succ]; group
        _ = (y ^ m * g₀ * (y ^ m)⁻¹) ^ r := by rw [hyg, conj_pow]
        _ = g₀ ^ (r ^ (m + 1)) := by rw [ih, ← pow_mul, pow_succ]
  have hrp : 1 ≤ r ^ p := Nat.one_le_pow _ _ hr1
  have hdiv : p ^ e ∣ r ^ p - 1 := by
    rw [← hord]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    have h1 := hym p
    rw [hy, one_mul, inv_one, mul_one] at h1
    have h2 : g₀ ^ (r ^ p - 1) * g₀ = g₀ := by
      rw [← pow_succ, Nat.sub_add_cancel hrp, ← h1]
    exact mul_eq_right.mp h2
  have hdiv' := A5.pow_dvd_sub_one_of_pow_dvd hp hp2 hr1 hdiv
  obtain ⟨m, rfl⟩ := hpow c hc
  have hyc : y * g₀ ^ m * y⁻¹ = g₀ ^ (r * m) := by
    rw [← conj_pow, hyg, ← pow_mul]
  have hinv : (g₀ ^ m * y * (g₀ ^ m)⁻¹ * y⁻¹)⁻¹ = g₀ ^ ((r - 1) * m) := by
    have e1 : (g₀ ^ m * y * (g₀ ^ m)⁻¹ * y⁻¹)⁻¹ = (y * g₀ ^ m * y⁻¹) * (g₀ ^ m)⁻¹ := by group
    rw [e1, hyc]
    have e2 : r * m = (r - 1) * m + m := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left m (by omega))]
    rw [e2, pow_add, mul_inv_cancel_right]
  refine ⟨?_, ?_⟩
  · have h1 : (g₀ ^ m * y * (g₀ ^ m)⁻¹ * y⁻¹)⁻¹ ∈ C := by
      rw [hinv]
      exact C.pow_mem g.2 _
    simpa using C.inv_mem h1
  · have h1 : ((g₀ ^ m * y * (g₀ ^ m)⁻¹ * y⁻¹)⁻¹) ^ p = 1 := by
      rw [hinv, ← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hord]
      obtain ⟨k, hk⟩ := hdiv'
      rcases Nat.eq_zero_or_pos e with rfl | he
      · simp
      · refine ⟨k * m, ?_⟩
        rw [hk]
        have : p ^ e = p ^ (e - 1) * p := by
          rw [← pow_succ, Nat.sub_add_cancel he]
        rw [this]
        ring
    rwa [inv_pow, inv_eq_one] at h1

theorem A5.orderOf_conj {G : Type*} [Group G] (g y : G) : orderOf (g * y * g⁻¹) = orderOf y := by
  simpa using orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y

theorem A5.metacyclic_plane {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {C : Subgroup G} (hC : IsCyclic C) (hCp : IsPGroup p C) {x y w : G} (hxC : x ∈ C)
    (hx : orderOf x = p) (hy : orderOf y = p) (hyC : y ∈ normalizer (C : Set G))
    (hxy : x * y = y * x) (hyx : y ∉ zpowers x) (hwC : w ∈ C) (hwy : w * y ≠ y * w) :
    Nat.card ↥(zpowers x ⊔ zpowers y) = p ^ 2 ∧
    (∀ u ∈ zpowers x ⊔ zpowers y, u ^ p = 1) ∧
    ∀ u ∈ zpowers x ⊔ zpowers y, u ≠ 1 →
      zpowers u = zpowers x ∨ ∃ g : G, zpowers u = zpowers (g * y * g⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  have hyp : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  obtain ⟨hdC, hdp⟩ := A5.commutator_pow_eq_one hp hp2 hC hCp hyp hyC hwC
  obtain ⟨d, hd⟩ : ∃ d : G, d = w * y * w⁻¹ * y⁻¹ := ⟨_, rfl⟩
  rw [← hd] at hdC hdp
  have hd1 : d ≠ 1 := by
    intro h
    apply hwy
    calc w * y = (w * y * w⁻¹ * y⁻¹) * (y * w) := by group
      _ = y * w := by rw [← hd, h, one_mul]
  have hdo : orderOf d = p := orderOf_eq_prime hdp hd1
  have hzp : ∀ a ∈ C, orderOf a = p → zpowers a = zpowers x := fun a ha hao =>
    Bender.eq_of_card_eq_of_cyclic hC (zpowers_le.mpr ha) (zpowers_le.mpr hxC)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hao, hx])
  have hdx : zpowers d = zpowers x := hzp d hdC hdo
  have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    have := hC
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥C)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxpow : ∀ v ∈ zpowers x, v * y = y * v := by
    intro v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (show Commute x y from hxy) k).eq
  have hwd : w * d = d * w := hCcomm w hwC d hdC
  have hwyw : w * y * w⁻¹ = d * y := by rw [hd]; group
  have hwj : ∀ j : ℕ, w ^ j * y * (w ^ j)⁻¹ = d ^ j * y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : w * d ^ j = d ^ j * w := (Commute.pow_right (show Commute w d from hwd) j).eq
      calc w ^ (j + 1) * y * (w ^ (j + 1))⁻¹ = w * (w ^ j * y * (w ^ j)⁻¹) * w⁻¹ := by
            rw [pow_succ']; group
        _ = (w * d ^ j) * y * w⁻¹ := by rw [ih]; group
        _ = d ^ j * (w * y * w⁻¹) := by rw [hc]; group
        _ = d ^ (j + 1) * y := by rw [hwyw, pow_succ]; group
  have hcommU : ∀ a ∈ zpowers x, ∀ b ∈ zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a y from hxpow a ha) k).eq
  have hinf : zpowers x ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [mem_bot]
    by_contra hv1
    obtain ⟨hvx, hvy⟩ := mem_inf.mp hv
    have hvo : orderOf v = p := by
      have h1 : orderOf v ∣ p := hy ▸ orderOf_dvd_of_mem_zpowers hvy
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hv1
      · exact h
    have h2 : zpowers v = zpowers y := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hvy)
      rw [Nat.card_zpowers, Nat.card_zpowers, hvo, hy]
    apply hyx
    have : y ∈ zpowers v := h2 ▸ mem_zpowers y
    exact zpowers_le.mpr hvx this
  have hcard : Nat.card ↥(zpowers x ⊔ zpowers y) = p ^ 2 := by
    rw [Bender.card_sup_eq_mul_of_commute hcommU hinf, Nat.card_zpowers, Nat.card_zpowers, hx,
      hy, sq]
  have hexp1 : ∀ v ∈ zpowers x, v ^ p = 1 := fun v hv =>
    orderOf_dvd_iff_pow_eq_one.mp (hx ▸ orderOf_dvd_of_mem_zpowers hv)
  have hexp2 : ∀ v ∈ zpowers y, v ^ p = 1 := fun v hv =>
    orderOf_dvd_iff_pow_eq_one.mp (hy ▸ orderOf_dvd_of_mem_zpowers hv)
  have hexp : ∀ u ∈ zpowers x ⊔ zpowers y, u ^ p = 1 := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Bender.exists_mul_of_mem_sup_of_commute hcommU hu
    rw [(show Commute a b from hcommU a ha b hb).mul_pow, hexp1 a ha, hexp2 b hb, one_mul]
  refine ⟨hcard, hexp, fun u hu hu1 => ?_⟩
  have huo : orderOf u = p := orderOf_eq_prime (hexp u hu) hu1
  obtain ⟨a, ha, b, hb, rfl⟩ := Bender.exists_mul_of_mem_sup_of_commute hcommU hu
  obtain ⟨α, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr ha)
  obtain ⟨β, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hb)
  by_cases hβ : p ∣ β
  · left
    have hyb : y ^ β = 1 := orderOf_dvd_iff_pow_eq_one.mp (hy ▸ hβ)
    rw [hyb, mul_one] at huo ⊢
    exact hzp _ (C.pow_mem hxC α) huo
  · right
    have hcop : Nat.Coprime β p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hβ))
    obtain ⟨β', -, hβ'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hu' : (x ^ α * y ^ β) ^ β' = x ^ (α * β') * y := by
      rw [(show Commute (x ^ α) (y ^ β) from hcommU _ ha _ hb).mul_pow, ← pow_mul, ← pow_mul,
        ← pow_mod_orderOf y, hy, hβ', pow_one]
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr
      (show x ^ (α * β') ∈ zpowers d from hdx ▸ pow_mem (mem_zpowers x) _))
    refine ⟨w ^ j, ?_⟩
    have hconj : (x ^ α * y ^ β) ^ β' = w ^ j * y * (w ^ j)⁻¹ := by
      rw [hu', hwj, hj]
    have hle : zpowers ((x ^ α * y ^ β) ^ β') ≤ zpowers (x ^ α * y ^ β) :=
      zpowers_le.mpr (pow_mem (mem_zpowers _) _)
    rw [← hconj]
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hconj, A5.orderOf_conj, hy, huo]

end CFSG.GH74.Uniqueness
