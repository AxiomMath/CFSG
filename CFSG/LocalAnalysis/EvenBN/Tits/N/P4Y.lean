module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Elem2
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup
open scoped Pointwise

variable {Γ : Type*} [Group Γ]

namespace IsF20

variable {U : Subgroup Γ} {x v : Γ}

theorem x_ne_one (h : IsF20 U x v) : x ≠ 1 := by
  intro hx1
  have hbot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have := h.fpf u hu (by rw [hx1]; group)
    rw [this]
    exact one_mem _
  have := h.card
  rw [hbot, Subgroup.card_bot] at this
  omega

theorem orderOf_x (h : IsF20 U x v) : orderOf x = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h.x5 h.x_ne_one

theorem sq_ne_one (h : IsF20 U x v) : v ^ 2 ≠ 1 := by
  intro hv
  have h1 := h.sq_conj
  rw [hv] at h1
  have hx5 := h.x5
  have hx2 : x * x = 1 := by
    have : x = x⁻¹ := by simpa using h1
    calc x * x = x * x⁻¹ := by rw [← this]
      _ = 1 := by group
  apply h.x_ne_one
  have h5 : x * x * x * x * x = 1 := by simpa [pow_succ] using hx5
  calc x = x * x * x * x * x * (x * x)⁻¹ * (x * x)⁻¹ := by group
    _ = 1 := by rw [h5, hx2]; group

theorem card_zpowers_x (h : IsF20 U x v) : Nat.card (zpowers x) = 5 := by
  rw [Nat.card_zpowers, h.orderOf_x]

theorem zpowers_x_le (h : IsF20 U x v) : zpowers x ≤ normalizer (U : Set Γ) := by
  rw [Subgroup.zpowers_le]
  exact h.x_norm

theorem zpowers_v_le (h : IsF20 U x v) : zpowers v ≤ normalizer (U : Set Γ) := by
  rw [Subgroup.zpowers_le]
  exact h.v_norm

theorem isPGroup_U (h : IsF20 U x v) : IsPGroup 2 U := IsPGroup.of_card (n := 4) (by rw [h.card]; norm_num)

theorem exists_frob (h : IsF20 U x v) : ∃ w, IsFrob x w ∧ zpowers w = zpowers v := by
  rcases h.vx with hv | hv
  · refine ⟨v⁻¹, ⟨h.x5, h.x_ne_one, ?_, ?_⟩, Subgroup.zpowers_inv⟩
    · rw [inv_pow, h.v4, inv_one]
    · have ha2 : (v⁻¹ * x * v) ^ 2 = x := by
        have := conj_pow (i := (2 : ℕ)) (a := v⁻¹) (b := x)
        simp only [inv_inv] at this
        rw [this, ← hv]
        group
      have ha5 : (v⁻¹ * x * v) ^ 5 = 1 := by
        have := conj_pow (i := (5 : ℕ)) (a := v⁻¹) (b := x)
        simp only [inv_inv] at this
        rw [this, h.x5]
        group
      have ha6 : (v⁻¹ * x * v) = (v⁻¹ * x * v) ^ 6 := by
        rw [show (6 : ℕ) = 5 + 1 from rfl, pow_add, ha5, one_mul, pow_one]
      simp only [inv_inv]
      calc v⁻¹ * x * v = (v⁻¹ * x * v) ^ 6 := ha6
        _ = ((v⁻¹ * x * v) ^ 2) ^ 3 := by rw [← pow_mul]
        _ = x ^ 3 := by rw [ha2]
  · exact ⟨v, ⟨h.x5, h.x_ne_one, h.v4, hv⟩, rfl⟩

theorem U_inf_F (h : IsF20 U x v) : U ⊓ (zpowers x ⊔ zpowers v : Subgroup Γ) = ⊥ := by
  obtain ⟨w, hw, hwv⟩ := h.exists_frob
  rw [← hwv]
  exact hw.inf_eq_bot_of_isPGroup h.isPGroup_U h.x_norm

theorem F_le_normalizer (h : IsF20 U x v) :
    (zpowers x ⊔ zpowers v : Subgroup Γ) ≤ normalizer (U : Set Γ) :=
  sup_le h.zpowers_x_le h.zpowers_v_le

theorem card_P (h : IsF20 U x v) : Nat.card ↥(U ⊔ zpowers x ⊔ zpowers v : Subgroup Γ) = 320 := by
  obtain ⟨w, hw, hwv⟩ := h.exists_frob
  have hwN : w ∈ normalizer (U : Set Γ) := h.zpowers_v_le (hwv ▸ mem_zpowers w)
  rw [← hwv, hw.card_sup_of_isPGroup h.isPGroup_U h.x_norm hwN, h.card]

theorem exists_mul (h : IsF20 U x v) {p : Γ} (hp : p ∈ (U ⊔ (zpowers x ⊔ zpowers v) : Subgroup Γ)) :
    ∃ u ∈ U, ∃ f ∈ (zpowers x ⊔ zpowers v : Subgroup Γ), p = u * f := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left U (zpowers x ⊔ zpowers v) h.F_le_normalizer
  have hp' : p ∈ ((U : Set Γ) * ((zpowers x ⊔ zpowers v : Subgroup Γ) : Set Γ)) := by
    rw [← hset]
    exact hp
  obtain ⟨u, hu, f, hf, rfl⟩ := hp'
  exact ⟨u, hu, f, hf, rfl⟩

theorem mul_eq_mul (h : IsF20 U x v) {u u' f f' : Γ} (hu : u ∈ U) (hu' : u' ∈ U)
    (hf : f ∈ (zpowers x ⊔ zpowers v : Subgroup Γ)) (hf' : f' ∈ (zpowers x ⊔ zpowers v : Subgroup Γ))
    (e : u * f = u' * f') : u = u' ∧ f = f' := by
  have h1 : u'⁻¹ * u = f' * f⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * f) * f⁻¹ := by group
      _ = u'⁻¹ * (u' * f') * f⁻¹ := by rw [e]
      _ = f' * f⁻¹ := by group
  have hmem : u'⁻¹ * u ∈ U ⊓ (zpowers x ⊔ zpowers v : Subgroup Γ) := by
    refine Subgroup.mem_inf.2 ⟨U.mul_mem (U.inv_mem hu') hu, ?_⟩
    rw [h1]
    exact (zpowers x ⊔ zpowers v : Subgroup Γ).mul_mem hf'
      ((zpowers x ⊔ zpowers v : Subgroup Γ).inv_mem hf)
  rw [h.U_inf_F, Subgroup.mem_bot] at hmem
  have hu1 : u = u' := by
    have := mul_left_cancel (a := u'⁻¹) (b := u) (c := u') (by rw [hmem]; group)
    exact this
  refine ⟨hu1, ?_⟩
  rw [hu1] at e
  exact mul_left_cancel e

theorem zpow_x_eq_one_of_sq (h : IsF20 U x v) {r : ℤ} (h2 : (x ^ r) ^ 2 = 1) : x ^ r = 1 := by
  have h5 : (x ^ r) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : x ^ ((5 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact h.x5
    rw [this, one_zpow]
  have hd2 : orderOf (x ^ r) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hd5 : orderOf (x ^ r) ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have hd1 : orderOf (x ^ r) ∣ Nat.gcd 2 5 := Nat.dvd_gcd hd2 hd5
  have : Nat.gcd 2 5 = 1 := by norm_num
  rw [this] at hd1
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd1)

theorem sq_ne_zpow (h : IsF20 U x v) (r : ℤ) : v ^ 2 ≠ x ^ r := by
  intro hr
  have h1 : (x ^ r) ^ 2 = 1 := by rw [← hr, ← pow_mul]; exact h.v4
  have := h.zpow_x_eq_one_of_sq h1
  rw [← hr] at this
  exact h.sq_ne_one this

theorem involution_form (h : IsF20 U x v) {f : Γ}
    (hf : f ∈ (zpowers x ⊔ zpowers v : Subgroup Γ)) (hf2 : f * f = 1) :
    f = 1 ∨ ∃ m : ℤ, f = x ^ m * v ^ 2 := by
  obtain ⟨w, hw, hwv⟩ := h.exists_frob
  have hKN : zpowers v ≤ normalizer (zpowers x : Set Γ) := by
    rw [← hwv]
    exact hw.zpowers_y_le_normalizer
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (zpowers x) (zpowers v) hKN
  have hf' : f ∈ ((zpowers x : Set Γ) * (zpowers v : Set Γ)) := by
    rw [← hset]
    exact hf
  obtain ⟨a, ha, b, hb, rfl⟩ := hf'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  beta_reduce at hf2 ⊢
  have hv4 : v ^ (4 : ℤ) = 1 := by exact_mod_cast h.v4
  have hn : v ^ n = v ^ (n % 4) := zpow_eq_zpow_emod n hv4
  rw [hn] at hf2 ⊢
  obtain ⟨k, hk, hkx⟩ := h.exists_vk
  have hv2x : ∀ i : ℤ, v ^ 2 * x ^ i * (v ^ 2)⁻¹ = x ^ (-i) := h.sq_conj_zpow
  have hn4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hn4 with h0 | h1 | h2 | h3
  · rw [h0, zpow_zero, mul_one] at hf2 ⊢
    left
    apply h.zpow_x_eq_one_of_sq
    rw [pow_two]
    exact hf2
  · rw [h1, zpow_one] at hf2
    exfalso
    have e : x ^ m * v * (x ^ m * v) = x ^ (m + k * m) * (v * v) := by
      calc x ^ m * v * (x ^ m * v) = x ^ m * (v * x ^ m * v⁻¹) * (v * v) := by group
        _ = x ^ m * x ^ (k * m) * (v * v) := by rw [hkx m]
        _ = x ^ (m + k * m) * (v * v) := by rw [zpow_add]
    rw [e, ← pow_two] at hf2
    apply h.sq_ne_zpow (-(m + k * m))
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_right hf2)
  · right
    refine ⟨m, ?_⟩
    rw [h2]
    simp
  · rw [h3] at hf2
    exfalso
    have e : x ^ m * v ^ (3 : ℤ) * (x ^ m * v ^ (3 : ℤ)) = x ^ (m - k * m) * v ^ 2 := by
      have e1 : v ^ (3 : ℤ) * x ^ m * (v ^ (3 : ℤ))⁻¹ = x ^ (-(k * m)) := by
        calc v ^ (3 : ℤ) * x ^ m * (v ^ (3 : ℤ))⁻¹
            = v * (v ^ 2 * x ^ m * (v ^ 2)⁻¹) * v⁻¹ := by group
          _ = x ^ (-(k * m)) := by rw [hv2x m, hkx (-m)]; congr 1; ring
      calc x ^ m * v ^ (3 : ℤ) * (x ^ m * v ^ (3 : ℤ))
          = x ^ m * (v ^ (3 : ℤ) * x ^ m * (v ^ (3 : ℤ))⁻¹) * (v ^ 6) := by group
        _ = x ^ m * x ^ (-(k * m)) * v ^ 2 := by
            rw [e1]
            have : v ^ 6 = v ^ 2 := by
              calc v ^ 6 = v ^ 4 * v ^ 2 := by rw [← pow_add]
                _ = v ^ 2 := by rw [h.v4, one_mul]
            rw [this]
        _ = x ^ (m - k * m) * v ^ 2 := by rw [← zpow_add]; congr 2
    rw [e] at hf2
    apply h.sq_ne_zpow (-(m - k * m))
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_right hf2)

theorem involution_comm_eq (h : IsF20 U x v) {m m' : ℤ}
    (hc : (x ^ m * v ^ 2) * (x ^ m' * v ^ 2) = (x ^ m' * v ^ 2) * (x ^ m * v ^ 2)) :
    x ^ m * v ^ 2 = x ^ m' * v ^ 2 := by
  have hww : v ^ 2 * v ^ 2 = 1 := h.sq_mul_self
  have e1 : (x ^ m * v ^ 2) * (x ^ m' * v ^ 2) = x ^ (m - m') := by
    have := h.sq_conj_zpow m'
    calc (x ^ m * v ^ 2) * (x ^ m' * v ^ 2)
        = x ^ m * (v ^ 2 * x ^ m' * (v ^ 2)⁻¹) * (v ^ 2 * v ^ 2) := by group
      _ = x ^ (m - m') := by rw [this, hww, mul_one, ← zpow_add]; congr 1
  have e2 : (x ^ m' * v ^ 2) * (x ^ m * v ^ 2) = x ^ (m' - m) := by
    have := h.sq_conj_zpow m
    calc (x ^ m' * v ^ 2) * (x ^ m * v ^ 2)
        = x ^ m' * (v ^ 2 * x ^ m * (v ^ 2)⁻¹) * (v ^ 2 * v ^ 2) := by group
      _ = x ^ (m' - m) := by rw [this, hww, mul_one, ← zpow_add]; congr 1
  rw [e1, e2] at hc
  have h2 : (x ^ (m - m')) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hc]
    rw [← zpow_add]
    have : m - m' + (m' - m) = 0 := by ring
    rw [this, zpow_zero]
  have h1 := h.zpow_x_eq_one_of_sq h2
  have : x ^ m = x ^ m' := by
    have : x ^ m * (x ^ m')⁻¹ = 1 := by rw [← zpow_neg, ← zpow_add]; rw [← sub_eq_add_neg]; exact h1
    exact mul_inv_eq_one.1 this
  rw [this]

theorem gInv_three_mul (h : IsF20 U x v) (m : ℤ) : gInv x v (3 * m) = x ^ m * v ^ 2 := by
  have h1 := h.sq_conj_zpow (-(3 * m))
  have hx5 : x ^ (5 : ℤ) = 1 := by exact_mod_cast h.x5
  have h5m : x ^ (5 * m) = 1 := by rw [zpow_mul, hx5, one_zpow]
  unfold gInv
  calc x ^ (3 * m) * v ^ 2 * (x ^ (3 * m))⁻¹
      = x ^ (3 * m) * (v ^ 2 * x ^ (-(3 * m)) * (v ^ 2)⁻¹) * v ^ 2 := by
        rw [zpow_neg]; group
    _ = x ^ (3 * m) * x ^ (3 * m) * v ^ 2 := by rw [h1, neg_neg]
    _ = x ^ (3 * m + 3 * m) * v ^ 2 := by rw [zpow_add]
    _ = x ^ m * v ^ 2 := by
        have : 3 * m + 3 * m = 5 * m + m := by ring
        rw [this, zpow_add, h5m, one_mul]

theorem card_centralizer_involution (h : IsF20 U x v) (m : ℤ) :
    Nat.card ↥(U ⊓ centralizer ({x ^ m * v ^ 2} : Set Γ)) = 4 := by
  rw [← h.gInv_three_mul m]
  exact h.card_centralizer_gInv _

theorem sq_of_mul_sq (h : IsF20 U x v) {u f : Γ} (hu : u ∈ U)
    (hf : f ∈ (zpowers x ⊔ zpowers v : Subgroup Γ)) (hg : (u * f) * (u * f) = 1) : f * f = 1 := by
  have hfn : f * u * f⁻¹ ∈ U := (mem_normalizer_iff.1 (h.F_le_normalizer hf) u).1 hu
  have e : (u * f) * (u * f) = (u * (f * u * f⁻¹)) * (f * f) := by group
  have := h.mul_eq_mul (u := u * (f * u * f⁻¹)) (u' := 1) (f := f * f) (f' := 1)
    (mul_mem hu hfn) (one_mem U)
    (mul_mem hf hf) (one_mem _) (by rw [← e, hg, one_mul])
  exact this.2

theorem card_elemAb_le [Finite Γ] (h : IsF20 U x v) {D : Subgroup Γ}
    (hD : D ≤ (U ⊔ (zpowers x ⊔ zpowers v) : Subgroup Γ))
    (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hs : ∀ a ∈ D, a * a = 1) :
    Nat.card D ≤ 16 ∧ (Nat.card D = 16 → D = U) := by
  by_cases hDU : D ≤ U
  · have hle : Nat.card D ≤ 16 := h.card ▸ Subgroup.card_le_of_le hDU
    exact ⟨hle, fun hcard => Subgroup.eq_of_le_of_card_ge hDU (by rw [h.card, hcard])⟩
  · obtain ⟨g, hgD, hgU⟩ : ∃ g ∈ D, g ∉ U := by
      by_contra hno
      push Not at hno
      exact hDU hno
    obtain ⟨u₀, hu₀, f₀, hf₀, rfl⟩ := h.exists_mul (hD hgD)
    have hf₀1 : f₀ ≠ 1 := by
      intro e
      apply hgU
      rw [e, mul_one]
      exact hu₀
    have hf₀2 : f₀ * f₀ = 1 := h.sq_of_mul_sq hu₀ hf₀ (hs _ hgD)
    obtain ⟨m, hm⟩ : ∃ m : ℤ, f₀ = x ^ m * v ^ 2 := by
      rcases h.involution_form hf₀ hf₀2 with e | e
      · exact absurd e hf₀1
      · exact e
    have hdich : ∀ d ∈ D, d ∈ U ∨ (u₀ * f₀)⁻¹ * d ∈ U := by
      intro d hd
      obtain ⟨u₁, hu₁, f₁, hf₁, rfl⟩ := h.exists_mul (hD hd)
      have hf₁2 : f₁ * f₁ = 1 := h.sq_of_mul_sq hu₁ hf₁ (hs _ hd)
      rcases h.involution_form hf₁ hf₁2 with e | ⟨m₁, hm₁⟩
      · left
        rw [e, mul_one]
        exact hu₁
      · right
        have hcomm := hc _ hgD _ hd
        have hf₀n : f₀ * u₁ * f₀⁻¹ ∈ U := (mem_normalizer_iff.1 (h.F_le_normalizer hf₀) u₁).1 hu₁
        have hf₁n : f₁ * u₀ * f₁⁻¹ ∈ U := (mem_normalizer_iff.1 (h.F_le_normalizer hf₁) u₀).1 hu₀
        have e1 : (u₀ * f₀) * (u₁ * f₁) = (u₀ * (f₀ * u₁ * f₀⁻¹)) * (f₀ * f₁) := by group
        have e2 : (u₁ * f₁) * (u₀ * f₀) = (u₁ * (f₁ * u₀ * f₁⁻¹)) * (f₁ * f₀) := by group
        have hff := (h.mul_eq_mul (mul_mem hu₀ hf₀n) (mul_mem hu₁ hf₁n) (mul_mem hf₀ hf₁)
          (mul_mem hf₁ hf₀) (by rw [← e1, ← e2]; exact hcomm)).2
        have hf01 : f₀ = f₁ := by
          rw [hm, hm₁] at hff ⊢
          exact h.involution_comm_eq hff
        rw [← hf01]
        have hfn : f₀⁻¹ * (u₀⁻¹ * u₁) * f₀ ∈ U := by
          have := (mem_normalizer_iff.1 (h.F_le_normalizer (inv_mem hf₀)) (u₀⁻¹ * u₁)).1
            (mul_mem (inv_mem hu₀) hu₁)
          simpa using this
        have e3 : (u₀ * f₀)⁻¹ * (u₁ * f₀) = f₀⁻¹ * (u₀⁻¹ * u₁) * f₀ := by group
        rw [e3]
        exact hfn
    set D₀ : Subgroup Γ := D ⊓ U with hD₀
    have hgnorm : zpowers (u₀ * f₀) ≤ normalizer (D₀ : Set Γ) := by
      rw [Subgroup.zpowers_le]
      apply Subgroup.centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro y hy
      exact hc y (Subgroup.mem_inf.1 hy).1 _ hgD
    have hDsub : D ≤ zpowers (u₀ * f₀) ⊔ D₀ := by
      intro d hd
      rcases hdich d hd with hdU | hdU
      · exact mem_sup_right (Subgroup.mem_inf.2 ⟨hd, hdU⟩)
      · have hmem : (u₀ * f₀)⁻¹ * d ∈ D₀ := Subgroup.mem_inf.2 ⟨D.mul_mem (D.inv_mem hgD) hd, hdU⟩
        have : d = (u₀ * f₀) * ((u₀ * f₀)⁻¹ * d) := by group
        rw [this]
        exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right hmem)
    have hprod := card_sup_mul_card_inf' hgnorm
    have hg1 : u₀ * f₀ ≠ 1 := by
      intro e
      apply hgU
      rw [e]
      exact one_mem U
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (u₀ * f₀) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hs _ hgD) hg1
    have hzg : Nat.card (zpowers (u₀ * f₀)) = 2 := by rw [Nat.card_zpowers, hord]
    have hinf : 0 < Nat.card ↥(zpowers (u₀ * f₀) ⊓ D₀) := Nat.card_pos
    have hsup : Nat.card ↥(zpowers (u₀ * f₀) ⊔ D₀) ≤ 2 * Nat.card D₀ := by
      rw [hzg] at hprod
      nlinarith
    have hD₀le : Nat.card D₀ ≤ 4 := by
      have hsub : D₀ ≤ U ⊓ centralizer ({x ^ m * v ^ 2} : Set Γ) := by
        intro y hy
        refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← hm]
        have hyg := hc y (Subgroup.mem_inf.1 hy).1 _ hgD
        have : u₀ * (y * f₀) = u₀ * (f₀ * y) := by
          calc u₀ * (y * f₀) = y * u₀ * f₀ := by rw [h.comm y (Subgroup.mem_inf.1 hy).2 u₀ hu₀]; group
            _ = (y * (u₀ * f₀)) := by group
            _ = ((u₀ * f₀) * y) := hyg
            _ = u₀ * (f₀ * y) := by group
        exact mul_left_cancel this
      exact (Subgroup.card_le_of_le hsub).trans (h.card_centralizer_involution m).le
    have hDle : Nat.card D ≤ 8 := by
      have := Subgroup.card_le_of_le hDsub
      omega
    exact ⟨by omega, fun hcard => by omega⟩

theorem zpow_x_eq_one_of_centralizes (h : IsF20 U x v) {r : ℤ}
    (hr : ∀ a ∈ U, x ^ r * a * (x ^ r)⁻¹ = a) : x ^ r = 1 := by
  have hr0 : r % 5 = 0 := by
    by_contra hne
    have hall : ∀ a ∈ U, a = 1 := fun a ha => h.fpf_zpow r hne a ha (hr a ha)
    have hbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [hall a ha]
      exact one_mem _
    have := h.card
    rw [hbot, Subgroup.card_bot] at this
    omega
  rw [h.zpow_emod_five r, hr0, zpow_zero]

@[expose] def Pgrp (U : Subgroup Γ) (x v : Γ) : Subgroup Γ := U ⊔ (zpowers x ⊔ zpowers v)

theorem Pgrp_eq (U : Subgroup Γ) (x v : Γ) : Pgrp U x v = U ⊔ zpowers x ⊔ zpowers v := by
  unfold Pgrp
  rw [sup_assoc]

theorem card_Pgrp (h : IsF20 U x v) : Nat.card ↥(Pgrp U x v) = 320 := by
  rw [Pgrp_eq]
  exact h.card_P

theorem U_le_Pgrp (U : Subgroup Γ) (x v : Γ) : U ≤ Pgrp U x v := le_sup_left

theorem Pgrp_le_normalizer (h : IsF20 U x v) : Pgrp U x v ≤ normalizer (U : Set Γ) :=
  sup_le Subgroup.le_normalizer h.F_le_normalizer

theorem centralizer_Pgrp (h : IsF20 U x v) {p : Γ} (hp : p ∈ Pgrp U x v)
    (hc : ∀ u ∈ U, p * u = u * p) : p ∈ U := by
  obtain ⟨u, hu, f, hf, rfl⟩ := h.exists_mul hp
  have hfc : ∀ a ∈ U, f * a = a * f := by
    intro a ha
    have h1 := hc a ha
    have h2 : u * (f * a) = u * (a * f) := by
      calc u * (f * a) = (u * f) * a := by group
        _ = a * (u * f) := h1
        _ = (a * u) * f := by group
        _ = (u * a) * f := by rw [h.comm a ha u hu]
        _ = u * (a * f) := by group
    exact mul_left_cancel h2
  have hf1 : f = 1 := by
    obtain ⟨w, hw, hwv⟩ := h.exists_frob
    have hfF : f ∈ (zpowers x ⊔ zpowers w : Subgroup Γ) := by rw [hwv]; exact hf
    have hxn : f * x⁻¹ * f⁻¹ ∈ zpowers x :=
      (mem_normalizer_iff.1 (hw.sup_le_normalizer hfF) x⁻¹).1 (inv_mem (mem_zpowers x))
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.1 ((zpowers x).mul_mem (mem_zpowers x) hxn)
    have hcomm_r : ∀ a ∈ U, x ^ r * a * (x ^ r)⁻¹ = a := by
      intro a ha
      rw [hr]
      have hxa : x⁻¹ * a * x ∈ U := (mem_normalizer_iff''.1 h.x_norm a).1 ha
      have := hfc _ hxa
      have hfn : f⁻¹ * a * f = a := by
        have h3 := hfc a ha
        calc f⁻¹ * a * f = f⁻¹ * (a * f) := by group
          _ = f⁻¹ * (f * a) := by rw [h3]
          _ = a := by group
      calc x * (f * x⁻¹ * f⁻¹) * a * (x * (f * x⁻¹ * f⁻¹))⁻¹
          = x * f * x⁻¹ * (f⁻¹ * a * f) * x * f⁻¹ * x⁻¹ := by group
        _ = x * f * x⁻¹ * a * x * f⁻¹ * x⁻¹ := by rw [hfn]
        _ = x * (f * (x⁻¹ * a * x)) * f⁻¹ * x⁻¹ := by group
        _ = x * ((x⁻¹ * a * x) * f) * f⁻¹ * x⁻¹ := by rw [this]
        _ = a := by group
    have hxr : x ^ r = 1 := h.zpow_x_eq_one_of_centralizes hcomm_r
    have e : x * (f * x⁻¹ * f⁻¹) = 1 := by rw [← hr, hxr]
    have e1 : f * x⁻¹ * f⁻¹ = x⁻¹ := eq_inv_of_mul_eq_one_right e
    have hfx : f * x = x * f := by
      have e2 : f * x * f⁻¹ = x := by
        have : f * x * f⁻¹ = (f * x⁻¹ * f⁻¹)⁻¹ := by group
        rw [this, e1, inv_inv]
      calc f * x = (f * x * f⁻¹) * f := by group
        _ = x * f := by rw [e2]
    have hmem : f ∈ (zpowers x ⊔ zpowers w : Subgroup Γ) ⊓ centralizer ({x} : Set Γ) :=
      Subgroup.mem_inf.2 ⟨hfF, Subgroup.mem_centralizer_singleton_iff.2 hfx⟩
    rw [hw.centralizer_inf_eq] at hmem
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hs1 : x ^ s = 1 := by
      apply h.zpow_x_eq_one_of_centralizes
      intro a ha
      rw [hs]
      have := hfc a ha
      calc f * a * f⁻¹ = (a * f) * f⁻¹ := by rw [this]
        _ = a := by group
    rw [← hs, hs1]
  rw [hf1, mul_one]
  exact hu

theorem card_elemAb_le_sup [Finite Γ] (h : IsF20 U x v) {Z₀ : Subgroup Γ}
    (hZP : ∀ a ∈ Z₀, ∀ p ∈ Pgrp U x v, a * p = p * a) (hZinf : Z₀ ⊓ Pgrp U x v = ⊥)
    {D : Subgroup Γ} (hD : D ≤ Z₀ ⊔ Pgrp U x v)
    (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hs : ∀ a ∈ D, a * a = 1) :
    Nat.card D ≤ 16 * Nat.card Z₀ ∧ (Nat.card D = 16 * Nat.card Z₀ → D = Z₀ ⊔ U) := by
  set P := Pgrp U x v with hP
  have hZN : Z₀ ≤ normalizer (P : Set Γ) := by
    intro a ha
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro p hp
    exact (hZP a ha p hp).symm
  have hCN : Z₀ ⊔ P ≤ normalizer (P : Set Γ) := sup_le hZN Subgroup.le_normalizer
  have hDN : D ≤ normalizer (P : Set Γ) := hD.trans hCN
  have hCcard : Nat.card ↥(Z₀ ⊔ P) = Nat.card Z₀ * Nat.card P := by
    have := card_sup_mul_card_inf' hZN
    rw [hZinf, Subgroup.card_bot, mul_one] at this
    exact this
  have hrel : P.relIndex D * Nat.card ↥(P ⊓ D) = Nat.card D := Subgroup.relIndex_mul_card P D
  have hrelC : P.relIndex (Z₀ ⊔ P) * Nat.card ↥(P ⊓ (Z₀ ⊔ P)) = Nat.card ↥(Z₀ ⊔ P) :=
    Subgroup.relIndex_mul_card P (Z₀ ⊔ P)
  have hPC : P ⊓ (Z₀ ⊔ P) = P := inf_eq_left.2 le_sup_right
  rw [hPC, hCcard] at hrelC
  have hrelC' : P.relIndex (Z₀ ⊔ P) = Nat.card Z₀ := Nat.eq_of_mul_eq_mul_right Nat.card_pos hrelC
  have hle_rel : P.relIndex D ≤ Nat.card Z₀ := by
    rw [← hrelC']
    exact Subgroup.relIndex_le_of_le_right hD (by rw [hrelC']; exact Nat.card_pos.ne')
  have hD1 := h.card_elemAb_le (D := P ⊓ D) inf_le_left
    (fun a ha b hb => hc a (Subgroup.mem_inf.1 ha).2 b (Subgroup.mem_inf.1 hb).2)
    (fun a ha => hs a (Subgroup.mem_inf.1 ha).2)
  have hZpos : 0 < Nat.card Z₀ := Nat.card_pos
  have hbound : Nat.card D ≤ 16 * Nat.card Z₀ := by
    rw [← hrel]
    nlinarith [hD1.1, hle_rel]
  refine ⟨hbound, fun heq => ?_⟩
  have hD1card : Nat.card ↥(P ⊓ D) = 16 := by
    by_contra hne
    have h15 : Nat.card ↥(P ⊓ D) ≤ 15 := by have := hD1.1; omega
    nlinarith [hle_rel]
  have hUD : P ⊓ D = U := hD1.2 hD1card
  have hUleD : U ≤ D := by rw [← hUD]; exact inf_le_right
  have hrelEq : P.relIndex D = Nat.card Z₀ := by
    rw [hD1card, heq] at hrel
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 16) (by linarith)
  have hDP : D ⊔ P = Z₀ ⊔ P := by
    have hprod := card_sup_mul_card_inf' hDN
    rw [inf_comm, hD1card, heq] at hprod
    have hcard : Nat.card ↥(D ⊔ P) = Nat.card ↥(Z₀ ⊔ P) := by
      rw [hCcard]
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 16)
      rw [hprod]
      ring
    exact Subgroup.eq_of_le_of_card_ge (sup_le hD le_sup_right) (by rw [hcard])
  have hZleD : Z₀ ≤ D := by
    intro z hz
    have hzC : z ∈ D ⊔ P := by rw [hDP]; exact mem_sup_left hz
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right D P hDN
    have hz' : z ∈ ((D : Set Γ) * (P : Set Γ)) := by rw [← hset]; exact hzC
    obtain ⟨d, hd, p, hp, hdp⟩ := hz'
    have hpinv : p⁻¹ ∈ U := by
      apply h.centralizer_Pgrp (inv_mem hp)
      intro u hu
      have hdu := hc d hd u (hUleD hu)
      have hdz : d = z * p⁻¹ := by rw [← hdp]; group
      have hzu := hZP z hz u (U_le_Pgrp U x v hu)
      have hzp := hZP z hz p⁻¹ (inv_mem hp)
      rw [hdz] at hdu
      have h1 : z * (p⁻¹ * u) = z * (u * p⁻¹) := by
        calc z * (p⁻¹ * u) = (z * p⁻¹) * u := by group
          _ = u * (z * p⁻¹) := hdu
          _ = (u * z) * p⁻¹ := by group
          _ = (z * u) * p⁻¹ := by rw [hzu]
          _ = z * (u * p⁻¹) := by group
      exact mul_left_cancel h1
    have hpU : p ∈ U := by simpa using inv_mem hpinv
    have : z = d * p := hdp.symm
    rw [this]
    exact mul_mem hd (hUleD hpU)
  have hZUle : Z₀ ⊔ U ≤ D := sup_le hZleD hUleD
  have hZUcard : Nat.card ↥(Z₀ ⊔ U) = 16 * Nat.card Z₀ := by
    have hZNU : Z₀ ≤ normalizer (U : Set Γ) := by
      intro a ha
      apply Subgroup.centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro u hu
      exact (hZP a ha u (U_le_Pgrp U x v hu)).symm
    have hprod := card_sup_mul_card_inf' hZNU
    have hinf : Z₀ ⊓ U = ⊥ := by
      rw [eq_bot_iff, ← hZinf]
      exact inf_le_inf_left Z₀ (U_le_Pgrp U x v)
    rw [hinf, Subgroup.card_bot, mul_one, h.card] at hprod
    rw [hprod]
    ring
  exact (Subgroup.eq_of_le_of_card_ge hZUle (by rw [heq, hZUcard])).symm

theorem gInv_mem_F (i : ℤ) : gInv x v i ∈ (zpowers x ⊔ zpowers v : Subgroup Γ) := by
  unfold gInv
  exact mul_mem (mul_mem (mem_sup_left (zpow_mem (mem_zpowers x) i))
    (mem_sup_right (pow_mem (mem_zpowers v) 2)))
    (inv_mem (mem_sup_left (zpow_mem (mem_zpowers x) i)))

theorem exists_sq_Pgrp (h : IsF20 U x v) {u : Γ} (hu : u ∈ U) :
    ∃ p ∈ Pgrp U x v, p * p = u := by
  obtain ⟨i, a, ha, hsq⟩ := h.exists_square u hu
  exact ⟨a * gInv x v i, mul_mem (mem_sup_left ha) (mem_sup_right (gInv_mem_F (x := x) (v := v) i)), hsq⟩

end IsF20

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
