module

public import CFSG.CGT.Foote81L6.Normalizer.OrderThree

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

@[expose] def oddCentralizer {X : Type*} [Group X] (d₀ d₁ : X) : Subgroup X :=
  pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓ Subgroup.centralizer ({d₁} : Set X)

theorem mem_oddCentralizer {X : Type*} [Group X] {d₀ d₁ k : X} :
    k ∈ oddCentralizer d₀ d₁ ↔ k ∈ pPrimeCore 2 X ∧ k * d₀ = d₀ * k ∧ k * d₁ = d₁ * k := by
  simp only [oddCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

structure IsLemma8Pair {X : Type*} [Group X] (d₀ d₁ x₀ x₁ : X) : Prop where
  mem₀ : x₀ ∈ pPrimeCore 2 X
  mem₁ : x₁ ∈ pPrimeCore 2 X
  pow₀ : x₀ ^ 3 = 1
  pow₁ : x₁ ^ 3 = 1
  inv₀ : d₀ * x₀ * d₀⁻¹ = x₀⁻¹
  inv₁ : d₁ * x₁ * d₁⁻¹ = x₁⁻¹
  central₀ : ∀ o ∈ pPrimeCore 2 X, o * x₀ = x₀ * o
  central₁ : ∀ o ∈ pPrimeCore 2 X, o * x₁ = x₁ * o
  inverted₀ : ∀ o ∈ pPrimeCore 2 X, d₀ * o * d₀⁻¹ = o⁻¹ → o ∈ Subgroup.zpowers x₀
  inverted₁ : ∀ o ∈ pPrimeCore 2 X, d₁ * o * d₁⁻¹ = o⁻¹ → o ∈ Subgroup.zpowers x₁
  decomp : ∀ o ∈ pPrimeCore 2 X, ∃ a b : ℤ, ∃ k ∈ oddCentralizer d₀ d₁,
    o = x₀ ^ a * x₁ ^ b * k

private theorem conj_inv_comm {G : Type*} [Group G] {d o : G} (hd : d * d = 1) :
    d * (o⁻¹ * (d * o * d⁻¹)) * d⁻¹ = (o⁻¹ * (d * o * d⁻¹))⁻¹ := by
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  rw [hdinv]
  calc d * (o⁻¹ * (d * o * d)) * d = d * o⁻¹ * d * o * (d * d) := by group
    _ = d * o⁻¹ * d * o := by rw [hd, mul_one]
    _ = (o⁻¹ * (d * o * d))⁻¹ := by simp only [mul_inv_rev, inv_inv, hdinv, mul_assoc]

private theorem inv_eq_mul_self_of_mem {G : Type*} [Group G] {x p : G} (hx : x ^ 3 = 1)
    (hp : p ∈ Subgroup.zpowers x) : p⁻¹ = p * p := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  have h3 : (x ^ m) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  rw [pow_three] at h3
  exact inv_eq_of_mul_eq_one_right h3

theorem eq_one_or_of_mem_zpowers {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x * x := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hm : x ^ m = x ^ (m % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod m 3]
    rw [zpow_add, zpow_mul, show x ^ (3 : ℤ) = 1 by rw [zpow_ofNat, hx], one_zpow, one_mul]
  have h0 : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
  have h3 : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r, m % 3 = r := ⟨_, rfl⟩
  rw [hm, hr]
  rw [hr] at h0 h3
  interval_cases r
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (Or.inl (zpow_one x))
  · exact Or.inr (Or.inr (by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]))

private theorem conj_mul_mul_eq {G : Type*} [Group G] {d o x p : G} (hx : x ^ 3 = 1)
    (hp : p ∈ Subgroup.zpowers x) (hpdef : p = o⁻¹ * (d * o * d⁻¹)) (hpinv : d * p * d⁻¹ = p⁻¹) :
    d * (o * p * p) * d⁻¹ = o * p * p := by
  have hop : d * o * d⁻¹ = o * p := by rw [hpdef]; group
  have e : d * (o * p * p) * d⁻¹ = (d * o * d⁻¹) * (d * p * d⁻¹) * (d * p * d⁻¹) := by group
  rw [e, hop, hpinv]
  calc o * p * p⁻¹ * p⁻¹ = o * p⁻¹ := by group
    _ = o * (p * p) := by rw [inv_eq_mul_self_of_mem hx hp]
    _ = o * p * p := by group

theorem exists_isLemma8Pair {V X : Type*} [CommGroup V] [Finite V] [Group X] [Finite X]
    (hV : ∀ v : V, v * v = 1) {ρ : X →* MulAut V} (hρ : Function.Injective ρ) {d₀ d₁ : X}
    (hd₀ : IsTransvection (ρ d₀)) (hd₁ : IsTransvection (ρ d₁)) (hcomm : d₀ * d₁ = d₁ * d₀) :
    ∃ x₀ x₁ : X, IsLemma8Pair d₀ d₁ x₀ x₁ := by
  classical
  set O := pPrimeCore 2 X with hO
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOn : O.Normal := inferInstance
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  have hsq : ∀ {d : X}, IsTransvection (ρ d) → d * d = 1 := by
    intro d hd
    obtain ⟨ht1, w, htw⟩ := hd
    exact hρ (by rw [map_mul, B1.tv_sq hV' htw ht1, map_one])
  have hd₀2 := hsq hd₀
  have hd₁2 := hsq hd₁
  obtain ⟨x₀, hx₀O, hx₀3, hx₀inv, hx₀c, hx₀i⟩ := exists_central_inverted_of_transvection hV hρ
    hd₀ hOodd (fun k hk => hOn.conj_mem k hk d₀)
  obtain ⟨x₁, hx₁O, hx₁3, hx₁inv, hx₁c, hx₁i⟩ := exists_central_inverted_of_transvection hV hρ
    hd₁ hOodd (fun k hk => hOn.conj_mem k hk d₁)
  refine ⟨x₀, x₁, hx₀O, hx₁O, hx₀3, hx₁3, hx₀inv, hx₁inv, hx₀c, hx₁c, hx₀i, hx₁i, ?_⟩
  intro o ho
  set p := o⁻¹ * (d₀ * o * d₀⁻¹) with hp
  have hpO : p ∈ O := O.mul_mem (O.inv_mem ho) (hOn.conj_mem o ho d₀)
  have hpinv : d₀ * p * d₀⁻¹ = p⁻¹ := conj_inv_comm hd₀2
  have hpx : p ∈ Subgroup.zpowers x₀ := hx₀i p hpO hpinv
  set c := o * p * p with hc
  have hcO : c ∈ O := O.mul_mem (O.mul_mem ho hpO) hpO
  have hcd₀ : d₀ * c * d₀⁻¹ = c := conj_mul_mul_eq hx₀3 hpx hp hpinv
  set q := c⁻¹ * (d₁ * c * d₁⁻¹) with hq
  have hqO : q ∈ O := O.mul_mem (O.inv_mem hcO) (hOn.conj_mem c hcO d₁)
  have hqinv : d₁ * q * d₁⁻¹ = q⁻¹ := conj_inv_comm hd₁2
  have hqx : q ∈ Subgroup.zpowers x₁ := hx₁i q hqO hqinv
  have hd₁c : d₀ * d₁ * d₀⁻¹ = d₁ := by rw [hcomm]; group
  have hqd₀ : d₀ * q * d₀⁻¹ = q := by
    have e : d₀ * q * d₀⁻¹ = (d₀ * c * d₀⁻¹)⁻¹ *
        ((d₀ * d₁ * d₀⁻¹) * (d₀ * c * d₀⁻¹) * (d₀ * d₁ * d₀⁻¹)⁻¹) := by rw [hq]; group
    rw [e, hcd₀, hd₁c]
  set k := c * q * q with hk
  have hkO : k ∈ O := O.mul_mem (O.mul_mem hcO hqO) hqO
  have hkd₁ : d₁ * k * d₁⁻¹ = k := conj_mul_mul_eq hx₁3 hqx hq hqinv
  have hkd₀ : d₀ * k * d₀⁻¹ = k := by
    have e : d₀ * k * d₀⁻¹ = (d₀ * c * d₀⁻¹) * (d₀ * q * d₀⁻¹) * (d₀ * q * d₀⁻¹) := by
      rw [hk]; group
    rw [e, hcd₀, hqd₀]
  have hcomm_of : ∀ {d g : X}, d * g * d⁻¹ = g → g * d = d * g := fun {d g} h => by
    calc g * d = d * g * d⁻¹ * d := by rw [h]
      _ = d * g := by group
  have hkK : k ∈ oddCentralizer d₀ d₁ :=
    mem_oddCentralizer.mpr ⟨hkO, hcomm_of hkd₀, hcomm_of hkd₁⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hpx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hqx
  have hpc : ∀ g ∈ O, Commute g p := fun g hg => by
    rw [← hm]
    exact (Commute.zpow_right (hx₀c g hg) m)
  have hqc : ∀ g ∈ O, Commute g q := fun g hg => by
    rw [← hn]
    exact (Commute.zpow_right (hx₁c g hg) n)
  have hpow : ∀ (y : X) (j : ℤ), y ^ j = q → y ^ (-2 * j) = q⁻¹ * q⁻¹ := by
    intro y j hj
    rw [mul_comm, zpow_mul, hj, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
      zpow_natCast, pow_two, mul_inv_rev]
  have hpow' : x₀ ^ (-2 * m) = p⁻¹ * p⁻¹ := by
    rw [mul_comm, zpow_mul, hm, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
      zpow_natCast, pow_two, mul_inv_rev]
  refine ⟨-2 * m, -2 * n, k, hkK, ?_⟩
  rw [hpow', hpow x₁ n hn]
  have ho' : o = k * q⁻¹ * q⁻¹ * p⁻¹ * p⁻¹ := by
    rw [hk, hc]
    group
  have hkq : Commute k (q⁻¹ * q⁻¹) := ((hqc k hkO).inv_right).mul_right (hqc k hkO).inv_right
  have hrest : Commute (k * q⁻¹ * q⁻¹) (p⁻¹ * p⁻¹) := by
    have hm' : k * q⁻¹ * q⁻¹ ∈ O := O.mul_mem (O.mul_mem hkO (O.inv_mem hqO)) (O.inv_mem hqO)
    exact ((hpc _ hm').inv_right).mul_right (hpc _ hm').inv_right
  calc o = (k * q⁻¹ * q⁻¹) * (p⁻¹ * p⁻¹) := by rw [ho']; group
    _ = (p⁻¹ * p⁻¹) * (k * q⁻¹ * q⁻¹) := hrest.eq
    _ = (p⁻¹ * p⁻¹) * (k * (q⁻¹ * q⁻¹)) := by group
    _ = (p⁻¹ * p⁻¹) * ((q⁻¹ * q⁻¹) * k) := by rw [hkq.eq]
    _ = p⁻¹ * p⁻¹ * (q⁻¹ * q⁻¹) * k := by group

theorem eq_one_of_zpow_eq_zpow_neg {G : Type*} [Group G] {y : G} (hy : y ^ 3 = 1)
    {a : ℤ} (h : y ^ a = y ^ (-a)) : y ^ a = 1 := by
  have h2 : y ^ a * y ^ a = 1 := by
    have : y ^ a * y ^ (-a) = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
    rwa [← h] at this
  have h3 : (y ^ a) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  calc y ^ a = y ^ a * (y ^ a * y ^ a) := by rw [h2, mul_one]
    _ = (y ^ a) ^ 3 := by rw [pow_three]
    _ = 1 := h3

theorem lemma8 {V X : Type*} [CommGroup V] [Finite V] [Group X] [Finite X]
    (hV : ∀ v : V, v * v = 1) {ρ : X →* MulAut V} (hρ : Function.Injective ρ) {d₀ d₁ : X}
    {b₀ b₁ : V} (hd₀ : IsTransvectionWith (ρ d₀) b₀) (hd₀1 : ρ d₀ ≠ 1)
    (hd₁ : IsTransvectionWith (ρ d₁) b₁) (hd₁1 : ρ d₁ ≠ 1) (hb : b₀ ≠ b₁)
    (hcomm : d₀ * d₁ = d₁ * d₀) (hL3 : ∀ g : X, ρ g b₀ ≠ b₀ * b₁) :
    ∃ x₀ x₁ : X, IsLemma8Pair d₀ d₁ x₀ x₁ ∧ x₁ * d₀ = d₀ * x₁ ∧ x₀ * d₁ = d₁ * x₀ ∧
      ∀ a b : ℤ, ∀ k ∈ oddCentralizer d₀ d₁, x₀ ^ a * x₁ ^ b * k = 1 →
        x₀ ^ a = 1 ∧ x₁ ^ b = 1 ∧ k = 1 := by
  classical
  obtain ⟨x₀, x₁, hP⟩ := exists_isLemma8Pair hV hρ ⟨hd₀1, b₀, hd₀⟩ ⟨hd₁1, b₁, hd₁⟩ hcomm
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  have hd₀2 : d₀ * d₀ = 1 := hρ (by rw [map_mul, B1.tv_sq hV' hd₀ hd₀1, map_one])
  have hd₁2 : d₁ * d₁ = 1 := hρ (by rw [map_mul, B1.tv_sq hV' hd₁ hd₁1, map_one])
  have hO := (inferInstance : (pPrimeCore 2 X).Normal)
  have hcentral : ∀ {e f y : X} {c₀ c₁ : V}, IsTransvectionWith (ρ e) c₀ → ρ e ≠ 1 →
      IsTransvectionWith (ρ f) c₁ → ρ f ≠ 1 → e * f = f * e → y ∈ pPrimeCore 2 X → y ^ 3 = 1 →
      f * y * f⁻¹ = y⁻¹ →
      (∀ o ∈ pPrimeCore 2 X, f * o * f⁻¹ = o⁻¹ → o ∈ Subgroup.zpowers y) →
      (y ≠ 1 → e * y * e⁻¹ = y⁻¹ → False) → y * e = e * y := by
    intro e f y c₀ c₁ he he1 hf hf1 hef hyO hy3 hyinv hyi hno
    set z := e * y * e⁻¹ with hz
    have hzO : z ∈ pPrimeCore 2 X := hO.conj_mem y hyO e
    have hfe : f * e = e * f := hef.symm
    have hzinv : f * z * f⁻¹ = z⁻¹ := by
      have e1 : f * z * f⁻¹ = e * (f * y * f⁻¹) * e⁻¹ := by
        rw [hz]
        calc f * (e * y * e⁻¹) * f⁻¹ = (f * e) * y * (f * e)⁻¹ := by group
          _ = (e * f) * y * (e * f)⁻¹ := by rw [hfe]
          _ = e * (f * y * f⁻¹) * e⁻¹ := by group
      rw [e1, hyinv, hz]
      group
    rcases eq_one_or_of_mem_zpowers hy3 (hyi z hzO hzinv) with h1 | h1 | h1
    · have hy1 : y = 1 := by
        calc y = e⁻¹ * (e * y * e⁻¹) * e := by group
          _ = 1 := by rw [← hz, h1]; group
      rw [hy1, one_mul, mul_one]
    · have h2 : e * y * e⁻¹ = y := by rw [← hz]; exact h1
      calc y * e = (e * y * e⁻¹) * e := by rw [h2]
        _ = e * y := by group
    · by_cases hy1 : y = 1
      · rw [hy1, one_mul, mul_one]
      · exfalso
        apply hno hy1
        show z = y⁻¹
        rw [h1]
        rw [pow_three] at hy3
        exact (inv_eq_of_mul_eq_one_right hy3).symm
  have hno : ∀ {y : X}, y ^ 3 = 1 → y ≠ 1 → d₀ * y * d₀⁻¹ = y⁻¹ → d₁ * y * d₁⁻¹ = y⁻¹ → False := by
    intro y hy3 hy1 h0 h1
    have hρy1 : ρ y ≠ 1 := fun h => hy1 (hρ (h.trans (map_one ρ).symm))
    rcases eq_mul_of_inverted_two hV hd₀ hd₀1 hd₁ hd₁1 hb (x := ρ y) (r := 3) (by decide)
        (by rw [← map_pow, hy3, map_one]) hρy1
        (by rw [← map_inv, ← map_mul, ← map_mul, h0, map_inv])
        (by rw [← map_inv, ← map_mul, ← map_mul, h1, map_inv]) with h | h
    · exact hL3 y h
    · exact hL3 (y * y) (by rw [map_mul, MulAut.mul_apply]; exact h)
  have hc₁ : x₁ * d₀ = d₀ * x₁ := hcentral hd₀ hd₀1 hd₁ hd₁1 hcomm hP.mem₁ hP.pow₁ hP.inv₁
    hP.inverted₁ (fun hy1 hinv => hno hP.pow₁ hy1 hinv hP.inv₁)
  have hc₀ : x₀ * d₁ = d₁ * x₀ := hcentral hd₁ hd₁1 hd₀ hd₀1 hcomm.symm hP.mem₀ hP.pow₀ hP.inv₀
    hP.inverted₀ (fun hy1 hinv => hno hP.pow₀ hy1 hP.inv₀ hinv)
  refine ⟨x₀, x₁, hP, hc₁, hc₀, fun a b k hk h1 => ?_⟩
  obtain ⟨-, hk₀, hk₁⟩ := mem_oddCentralizer.mp hk
  have hconj : ∀ {d y : X}, d * y * d⁻¹ = y⁻¹ → ∀ j : ℤ, d * y ^ j * d⁻¹ = y ^ (-j) := by
    intro d y hdy j
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hdy, inv_zpow, zpow_neg]
  have hfix : ∀ {d y : X}, y * d = d * y → ∀ j : ℤ, d * y ^ j * d⁻¹ = y ^ j := by
    intro d y hdy j
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    congr 1
    calc d * y * d⁻¹ = y * d * d⁻¹ := by rw [hdy]
      _ = y := by group
  have hk₀' : d₀ * k * d₀⁻¹ = k := by rw [← hk₀]; group
  have hk₁' : d₁ * k * d₁⁻¹ = k := by rw [← hk₁]; group
  have h0 : x₀ ^ (-a) * x₁ ^ b * k = 1 := by
    have := congrArg (fun g => d₀ * g * d₀⁻¹) h1
    simp only [mul_one, mul_inv_cancel] at this
    rw [← this]
    calc x₀ ^ (-a) * x₁ ^ b * k
        = (d₀ * x₀ ^ a * d₀⁻¹) * (d₀ * x₁ ^ b * d₀⁻¹) * (d₀ * k * d₀⁻¹) := by
          rw [hconj hP.inv₀, hfix hc₁, hk₀']
      _ = d₀ * (x₀ ^ a * x₁ ^ b * k) * d₀⁻¹ := by group
  have ha : x₀ ^ a = 1 := by
    have h2 : x₀ ^ a = x₀ ^ (-a) := by
      have := h1.trans h0.symm
      exact mul_right_cancel (mul_right_cancel this)
    exact eq_one_of_zpow_eq_zpow_neg hP.pow₀ h2
  have h0' : x₀ ^ a * x₁ ^ (-b) * k = 1 := by
    have := congrArg (fun g => d₁ * g * d₁⁻¹) h1
    simp only [mul_one, mul_inv_cancel] at this
    rw [← this]
    calc x₀ ^ a * x₁ ^ (-b) * k
        = (d₁ * x₀ ^ a * d₁⁻¹) * (d₁ * x₁ ^ b * d₁⁻¹) * (d₁ * k * d₁⁻¹) := by
          rw [hconj hP.inv₁, hfix hc₀, hk₁']
      _ = d₁ * (x₀ ^ a * x₁ ^ b * k) * d₁⁻¹ := by group
  have hb' : x₁ ^ b = 1 := by
    have h2 : x₁ ^ b = x₁ ^ (-b) := by
      have := h1.trans h0'.symm
      exact mul_left_cancel (mul_right_cancel this)
    exact eq_one_of_zpow_eq_zpow_neg hP.pow₁ h2
  refine ⟨ha, hb', ?_⟩
  rw [ha, hb', one_mul, one_mul] at h1
  exact h1

end CFSG.CGT.Foote81L6.Normalizer
