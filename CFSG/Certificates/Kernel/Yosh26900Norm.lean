module

public import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.Yosh26900

theorem pow_mod_two {K : Type*} [Group K] {x : K} (h2 : x ^ 2 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, h2, one_pow, one_mul]

theorem conj_pow_eq {K : Type*} [Group K] {h x y : K} (hxy : h * x = y * h) (n : ℕ) :
    h * x ^ n = y ^ n * h := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc h * x ^ (n + 1) = h * x ^ n * x := by rw [pow_succ, mul_assoc]
      _ = y ^ n * (h * x) := by rw [ih, mul_assoc]
      _ = y ^ n * (y * h) := by rw [hxy]
      _ = y ^ (n + 1) * h := by rw [pow_succ, mul_assoc]

theorem conj_central {K : Type*} [Group K] {q : K} (hq : ∀ y, q * y = y * q) (h t : K) :
    h * (q * t) * h⁻¹ = q * (h * t * h⁻¹) := by
  calc h * (q * t) * h⁻¹ = (h * q) * t * h⁻¹ := by group
    _ = (q * h) * t * h⁻¹ := by rw [hq h]
    _ = q * (h * t * h⁻¹) := by group

theorem norm_swap {K : Type*} [Group K] (e c s : K) (he2 : e ^ 2 = 1) (hc2 : c ^ 2 = 1)
    (hc1 : c ≠ 1) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (hec : ∀ y, e * y = y * e)
    (hcc : ∀ y, c * y = y * c)
    (hCs : ∀ z, z * s = s * z → ∃ a b r : ℕ, z = e ^ a * c ^ b * s ^ r)
    (hInv : ∃ n, n * s = s * s * n)
    (hSyl : ∀ z, z ^ 3 = 1 → z ≠ 1 → ∃ h, h * z = s * h ∨ h * z = s * s * h)
    (ψ : MulAut K) (hψe : ψ e = e * c) (hψc : ψ c = c) (w : K) (hw : ψ w = w)
    (hw2 : ∀ y, ψ (ψ y) * w = w * y) :
    ∃ h, h * ψ s = s * h ∧ h * ψ h * w = 1 := by
  have hsss : s * s * s = 1 := by rw [← hs3, pow_succ, pow_succ, pow_one]
  have hce : ∀ (n : ℕ) (y : K), e ^ n * y = y * e ^ n := fun n y => (Commute.pow_left (hec y) n).eq
  have hcc' : ∀ (n : ℕ) (y : K), c ^ n * y = y * c ^ n := fun n y =>
    (Commute.pow_left (hcc y) n).eq
  have hecn : ∀ n : ℕ, (e * c) ^ n = e ^ n * c ^ n := fun n => Commute.mul_pow (hec c) n
  obtain ⟨h2, hh2⟩ : ∃ h2, h2 * ψ s = s * h2 := by
    have h3 : ψ s ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
    have h1 : ψ s ≠ 1 := fun h => hs1 (ψ.injective (by rw [h, map_one]))
    obtain ⟨h, hh | hh⟩ := hSyl _ h3 h1
    · exact ⟨h, hh⟩
    · obtain ⟨n, hn⟩ := hInv
      refine ⟨n * h, ?_⟩
      have hn2 : n * (s * s) = s * n := by
        calc n * (s * s) = (n * s) * s := by group
          _ = (s * s * n) * s := by rw [hn]
          _ = s * s * (n * s) := by group
          _ = s * s * (s * s * n) := by rw [hn]
          _ = (s * s * s) * (s * n) := by group
          _ = s * n := by rw [hsss, one_mul]
      calc n * h * ψ s = n * (h * ψ s) := by group
        _ = n * (s * s * h) := by rw [hh]
        _ = n * (s * s) * h := by group
        _ = s * n * h := by rw [hn2]
        _ = s * (n * h) := by group
  set z := h2 * ψ h2 * w with hz
  have hφφ : ∀ k, h2 * ψ (h2 * ψ k * h2⁻¹) * h2⁻¹ * z = z * k := by
    intro k
    calc h2 * ψ (h2 * ψ k * h2⁻¹) * h2⁻¹ * z = h2 * ψ h2 * (ψ (ψ k) * w) := by
          rw [hz, map_mul, map_mul, map_inv]; group
      _ = h2 * ψ h2 * (w * k) := by rw [hw2]
      _ = z * k := by rw [hz]; group
  have hφs : h2 * ψ s * h2⁻¹ = s := by rw [hh2]; group
  have hzs : z * s = s * z := by
    have := hφφ s
    rw [hφs, hφs] at this
    exact this.symm
  obtain ⟨a, b, r, hzabr⟩ := hCs z hzs
  have hφz : h2 * ψ z * h2⁻¹ = z := by
    have : ψ z = ψ h2 * (w * h2) := by
      rw [hz, map_mul, map_mul, hw, ← hw2 h2]
      group
    rw [this, hz]
    group
  have hpsr : ∀ n : ℕ, h2 * ψ s ^ n = s ^ n * h2 := conj_pow_eq hh2
  have hpsr' : h2 * ψ s ^ r * h2⁻¹ = s ^ r := by rw [hpsr]; group
  have hQ : ∀ y, e ^ a * c ^ a * c ^ b * y = y * (e ^ a * c ^ a * c ^ b) := by
    intro y
    calc e ^ a * c ^ a * c ^ b * y = e ^ a * c ^ a * (c ^ b * y) := by group
      _ = e ^ a * ((c ^ a * y) * c ^ b) := by rw [hcc' b y]; group
      _ = e ^ a * ((y * c ^ a) * c ^ b) := by rw [hcc' a y]
      _ = (e ^ a * y) * c ^ a * c ^ b := by group
      _ = (y * e ^ a) * c ^ a * c ^ b := by rw [hce a y]
      _ = y * (e ^ a * c ^ a * c ^ b) := by group
  have hψz : ψ z = e ^ a * c ^ a * c ^ b * ψ s ^ r := by
    rw [hzabr, map_mul, map_mul, map_pow, map_pow, map_pow, hψe, hψc, hecn]
  have hca : c ^ a = 1 := by
    have h1 : h2 * ψ z * h2⁻¹ = e ^ a * c ^ a * c ^ b * s ^ r := by
      rw [hψz, conj_central hQ, hpsr']
    have h5 : e ^ a * c ^ b * s ^ r = e ^ a * c ^ a * c ^ b * s ^ r :=
      hzabr.symm.trans (hφz.symm.trans h1)
    have h6 := mul_right_cancel h5
    have h6' : e ^ a * c ^ b = e ^ a * (c ^ a * c ^ b) := by rw [h6, mul_assoc]
    have h7 : c ^ b = c ^ a * c ^ b := mul_left_cancel h6'
    exact (mul_right_cancel ((one_mul (c ^ b)).trans h7)).symm
  have ha : a % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one a with h | h
    · exact h
    · exfalso
      apply hc1
      rw [← pow_one c, ← h, ← pow_mod_two hc2, hca]
  have hea : e ^ a = 1 := by rw [pow_mod_two he2, ha, pow_zero]
  have hzbr : z = c ^ b * s ^ r := by rw [hzabr, hea, one_mul]
  refine ⟨e ^ b * s ^ r * h2, ?_, ?_⟩
  · calc e ^ b * s ^ r * h2 * ψ s = e ^ b * s ^ r * (h2 * ψ s) := by group
      _ = e ^ b * (s ^ r * s) * h2 := by rw [hh2]; group
      _ = e ^ b * (s * s ^ r) * h2 := by rw [← pow_succ, pow_succ']
      _ = (e ^ b * s) * s ^ r * h2 := by group
      _ = (s * e ^ b) * s ^ r * h2 := by rw [hce b s]
      _ = s * (e ^ b * s ^ r * h2) := by group
  · have hψh : ψ (e ^ b * s ^ r * h2) = e ^ b * c ^ b * ψ s ^ r * ψ h2 := by
      rw [map_mul, map_mul, map_pow, map_pow, hψe, hecn]
    rw [hψh]
    have hsr3 : s ^ r * s ^ r * s ^ r = 1 := by
      rw [← pow_add, ← pow_add, show r + r + r = 3 * r by ring, pow_mul, hs3, one_pow]
    have he2b : e ^ b * e ^ b = 1 := by rw [← pow_add, ← two_mul, pow_mul, he2, one_pow]
    have hc2b : c ^ b * c ^ b = 1 := by rw [← pow_add, ← two_mul, pow_mul, hc2, one_pow]
    calc e ^ b * s ^ r * h2 * (e ^ b * c ^ b * ψ s ^ r * ψ h2) * w
        = e ^ b * s ^ r * (h2 * e ^ b) * c ^ b * ψ s ^ r * ψ h2 * w := by group
      _ = e ^ b * s ^ r * (e ^ b * h2) * c ^ b * ψ s ^ r * ψ h2 * w := by rw [hce b h2]
      _ = e ^ b * s ^ r * e ^ b * (h2 * c ^ b) * ψ s ^ r * ψ h2 * w := by group
      _ = e ^ b * s ^ r * e ^ b * (c ^ b * h2) * ψ s ^ r * ψ h2 * w := by rw [hcc' b h2]
      _ = e ^ b * s ^ r * e ^ b * c ^ b * (h2 * ψ s ^ r) * (ψ h2 * w) := by group
      _ = e ^ b * s ^ r * e ^ b * c ^ b * (s ^ r * h2) * (ψ h2 * w) := by rw [hpsr]
      _ = e ^ b * s ^ r * e ^ b * c ^ b * s ^ r * z := by rw [hz]; group
      _ = e ^ b * s ^ r * e ^ b * c ^ b * s ^ r * (c ^ b * s ^ r) := by rw [hzbr]
      _ = e ^ b * (s ^ r * e ^ b) * (c ^ b * (s ^ r * c ^ b)) * s ^ r := by group
      _ = e ^ b * (e ^ b * s ^ r) * (c ^ b * (c ^ b * s ^ r)) * s ^ r := by
          rw [← hce b (s ^ r), ← hcc' b (s ^ r)]
      _ = (e ^ b * e ^ b) * (s ^ r * (c ^ b * c ^ b)) * s ^ r * s ^ r := by group
      _ = 1 * (s ^ r * 1) * s ^ r * s ^ r := by rw [he2b, hc2b]
      _ = 1 := by rw [one_mul, mul_one, hsr3]

end CFSG.KC.Yosh26900

end
