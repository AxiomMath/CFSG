module

public import CFSG.ClassicalInvolution.AschTight.Sec71Good

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem quad_r (i k a b : ℤ) :
    k * (-a + i * b) ^ 2 - i * k * (-a + i * b) * b + i * b ^ 2 =
      k * a ^ 2 - i * k * a * b + i * b ^ 2 := by ring

theorem quad_t (i k a b : ℤ) :
    k * a ^ 2 - i * k * a * (k * a - b) + i * (k * a - b) ^ 2 =
      k * a ^ 2 - i * k * a * b + i * b ^ 2 := by ring

omit [Finite G] in
theorem conj_r_uv {u v r : G} (huv : Commute u v) {i : ℤ} (hu : r * u * r⁻¹ = u⁻¹)
    (hv : r * v * r⁻¹ = v * u ^ i) (a b : ℤ) :
    r * (u ^ a * v ^ b) * r⁻¹ = u ^ (-a + i * b) * v ^ b := by
  have hvui : Commute v (u ^ i) := (huv.zpow_left i).symm
  calc r * (u ^ a * v ^ b) * r⁻¹ = (r * u * r⁻¹) ^ a * (r * v * r⁻¹) ^ b := by
        rw [conj_zpow, conj_zpow]; group
    _ = u ^ (-a) * (v ^ b * u ^ (i * b)) := by
        rw [hu, hv, hvui.mul_zpow, ← zpow_mul, inv_zpow, zpow_neg]
    _ = u ^ (-a) * u ^ (i * b) * v ^ b := by
        rw [((huv.zpow_zpow (i * b) b).symm).eq]; group
    _ = u ^ (-a + i * b) * v ^ b := by rw [zpow_add]

omit [Finite G] in
theorem conj_t_uv {u v t : G} (huv : Commute u v) {k : ℤ} (hu : t * u * t⁻¹ = u * v ^ k)
    (hv : t * v * t⁻¹ = v⁻¹) (a b : ℤ) :
    t * (u ^ a * v ^ b) * t⁻¹ = u ^ a * v ^ (k * a - b) := by
  calc t * (u ^ a * v ^ b) * t⁻¹ = (t * u * t⁻¹) ^ a * (t * v * t⁻¹) ^ b := by
        rw [conj_zpow, conj_zpow]; group
    _ = u ^ a * v ^ (k * a) * v ^ (-b) := by
        rw [hu, hv, (huv.zpow_right k).mul_zpow, ← zpow_mul, inv_zpow, zpow_neg]
    _ = u ^ a * v ^ (k * a - b) := by rw [mul_assoc, ← zpow_add, sub_eq_add_neg]

omit [Finite G] in
theorem exists_quad_mul {u v x y : G} {i k : ℤ}
    (hx : ∀ a b : ℤ, ∃ a' b' : ℤ, x * (u ^ a * v ^ b) * x⁻¹ = u ^ a' * v ^ b' ∧
      k * a' ^ 2 - i * k * a' * b' + i * b' ^ 2 ≡ k * a ^ 2 - i * k * a * b + i * b ^ 2 [ZMOD 4])
    (hy : ∀ a b : ℤ, ∃ a' b' : ℤ, y * (u ^ a * v ^ b) * y⁻¹ = u ^ a' * v ^ b' ∧
      k * a' ^ 2 - i * k * a' * b' + i * b' ^ 2 ≡ k * a ^ 2 - i * k * a * b + i * b ^ 2 [ZMOD 4])
    (a b : ℤ) : ∃ a' b' : ℤ, x * y * (u ^ a * v ^ b) * (x * y)⁻¹ = u ^ a' * v ^ b' ∧
      k * a' ^ 2 - i * k * a' * b' + i * b' ^ 2 ≡ k * a ^ 2 - i * k * a * b + i * b ^ 2
        [ZMOD 4] := by
  obtain ⟨a₁, b₁, h1, q1⟩ := hy a b
  obtain ⟨a₂, b₂, h2, q2⟩ := hx a₁ b₁
  refine ⟨a₂, b₂, ?_, q2.trans q1⟩
  calc x * y * (u ^ a * v ^ b) * (x * y)⁻¹ = x * (y * (u ^ a * v ^ b) * y⁻¹) * x⁻¹ := by group
    _ = u ^ a₂ * v ^ b₂ := by rw [h1, h2]

theorem exists_quad (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {i k : ℤ} (hi : r * v * r⁻¹ = v * u ^ i)
    (hk : t * u * t⁻¹ = u * v ^ k) {w : G} (hw : w ∈ Subgroup.closure {r, t}) (a b : ℤ) :
    ∃ a' b' : ℤ, w * (u ^ a * v ^ b) * w⁻¹ = u ^ a' * v ^ b' ∧
      k * a' ^ 2 - i * k * a' * b' + i * b' ^ 2 ≡ k * a ^ 2 - i * k * a * b + i * b ^ 2
        [ZMOD 4] := by
  have huv : Commute u v := hWc u hd.u_memW v hd'.u_memW
  have P1 : ∀ a b : ℤ, ∃ a' b' : ℤ, 1 * (u ^ a * v ^ b) * 1⁻¹ = u ^ a' * v ^ b' ∧
      k * a' ^ 2 - i * k * a' * b' + i * b' ^ 2 ≡ k * a ^ 2 - i * k * a * b + i * b ^ 2
        [ZMOD 4] := fun a b => ⟨a, b, by group, Int.ModEq.refl _⟩
  have Ppow : ∀ x : G, (∀ a b : ℤ, ∃ a' b' : ℤ, x * (u ^ a * v ^ b) * x⁻¹ = u ^ a' * v ^ b' ∧
      k * a' ^ 2 - i * k * a' * b' + i * b' ^ 2 ≡ k * a ^ 2 - i * k * a * b + i * b ^ 2
        [ZMOD 4]) → ∀ n : ℕ, ∀ a b : ℤ, ∃ a' b' : ℤ,
      x ^ n * (u ^ a * v ^ b) * (x ^ n)⁻¹ = u ^ a' * v ^ b' ∧
      k * a' ^ 2 - i * k * a' * b' + i * b' ^ 2 ≡ k * a ^ 2 - i * k * a * b + i * b ^ 2
        [ZMOD 4] := by
    intro x hx n
    induction n with
    | zero => simpa using P1
    | succ n ih =>
      rw [pow_succ]
      exact exists_quad_mul ih hx
  induction hw using Subgroup.closure_induction generalizing a b with
  | mem x hx =>
    rcases hx with h | h
    · subst x
      exact ⟨-a + i * b, b, conj_r_uv huv hd.conj_u hi a b, by rw [quad_r]⟩
    · rw [Set.mem_singleton_iff] at h
      subst x
      exact ⟨a, k * a - b, conj_t_uv huv hk hd'.conj_u a b, by rw [quad_t]⟩
  | one => exact P1 a b
  | mul x y _ _ hx hy => exact exists_quad_mul hx hy a b
  | inv x _ hx =>
    have he : x⁻¹ = x ^ (orderOf x - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [he]
    exact Ppow x hx _ a b

theorem four_dvd_of_quad {i k a b : ℤ} (hk : Odd k) (ha : (4 : ℤ) ∣ a) (hb : Odd b)
    (hq : k * a ^ 2 - i * k * a * b + i * b ^ 2 ≡ k * 1 ^ 2 - i * k * 1 * 0 + i * 0 ^ 2
      [ZMOD 4]) : (4 : ℤ) ∣ i * k - 1 := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  obtain ⟨g, rfl⟩ := hk
  obtain ⟨e, he⟩ := Int.ModEq.dvd hq
  exact ⟨g ^ 2 + g - (2 * g + 1) * (e + 4 * (2 * g + 1) * c ^ 2 -
    i * (2 * g + 1) * c * (2 * d + 1) + i * (d ^ 2 + d)),
    by linear_combination (-(2 * g + 1)) * he⟩

theorem conj_ne_of_quad (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hzj : z ≠ j)
    {i k : ℤ} (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hko : Odd k)
    (hbad : ¬ (4 : ℤ) ∣ i * k - 1) {w : G} (hw : w ∈ Subgroup.closure {r, t})
    (hwW : w ∈ Subgroup.normalizer (W : Set G)) : conjSub w K ≠ J := by
  intro hwK
  have hUV := inf_eq_bot_of_ne hd hd' hzj
  have hNv : orderOf v = orderOf u := (orderOf_eq_orderOf hΩ hd hd').symm
  have hconjU : conjSub w (Subgroup.zpowers u) = Subgroup.zpowers v := by
    rw [← hd.inf_eq, conjSub_inf, hwK, mem_normalizer_iff_conjSub_eq.mp hwW, hd'.inf_eq]
  have hwu : w * u * w⁻¹ ∈ Subgroup.zpowers v :=
    hconjU ▸ conj_mem_conjSub (Subgroup.mem_zpowers u)
  obtain ⟨a', b', he, hq⟩ := exists_quad hd hd' hWc hi hk hw 1 0
  rw [zpow_one, zpow_zero, mul_one] at he
  have hua : u ^ a' = 1 := by
    have h1 : u ^ a' ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v := by
      refine ⟨Subgroup.zpow_mem_zpowers u a', ?_⟩
      have := Subgroup.mul_mem _ (he ▸ hwu) (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers v b'))
      rwa [mul_inv_cancel_right] at this
    rw [hUV] at h1
    exact h1
  rw [hua, one_mul] at he
  obtain ⟨n, hn⟩ := hd.orderOf_eq
  have h4N := hd.four_le
  have hn2 : 2 ≤ n := by
    by_contra h
    interval_cases n <;> simp_all
  have h4 : (4 : ℤ) ∣ (orderOf u : ℤ) := by
    rw [hn]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    exact ⟨2 ^ n', by push_cast; ring⟩
  have h4a : (4 : ℤ) ∣ a' := by
    rw [zpow_eq_one_iff_modEq, Int.modEq_zero_iff_dvd] at hua
    exact h4.trans hua
  have hb' : Odd b' := by
    by_contra hb
    obtain ⟨c, hc⟩ := Int.not_odd_iff_even.mp hb
    have hhalf : orderOf u / 2 * 2 = orderOf u := by
      rw [hn]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, Nat.mul_div_cancel _ two_pos]
    have h1 : (w * u * w⁻¹) ^ (orderOf u / 2) = w * z * w⁻¹ := by rw [conj_pow, hd.z_eq]
    have hcast : (orderOf u : ℤ) = ((orderOf u / 2 : ℕ) : ℤ) * 2 := by exact_mod_cast hhalf.symm
    have h2 : (v ^ b') ^ (orderOf u / 2) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, zpow_eq_one_iff_modEq, hNv, Int.modEq_zero_iff_dvd, hc]
      exact ⟨c, by rw [hcast]; ring⟩
    rw [he, h2] at h1
    have h3 := h1.symm
    rw [conj_eq_one_iff] at h3
    exact hd.uinv.ne_one h3
  exact hbad (four_dvd_of_quad hko h4a hb' hq)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
