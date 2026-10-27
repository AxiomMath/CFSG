module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

section Heis

variable {G : Type*} [Group G]

theorem conj_pow_central {x y z : G} (hzx : Commute z x) (hzy : Commute z y) {k : ℕ}
    (h : x * y * x⁻¹ = y * z ^ k) (a n : ℕ) :
    x ^ a * y ^ n * (x ^ a)⁻¹ = y ^ n * z ^ (k * a * n) := by
  have hxz : x * z * x⁻¹ = z := by rw [← hzx.eq, mul_inv_cancel_right]
  have key : ∀ a : ℕ, x ^ a * y * (x ^ a)⁻¹ = y * z ^ (k * a) := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      calc x ^ (a + 1) * y * (x ^ (a + 1))⁻¹ = x * (x ^ a * y * (x ^ a)⁻¹) * x⁻¹ := by group
        _ = x * (y * z ^ (k * a)) * x⁻¹ := by rw [ih]
        _ = (x * y * x⁻¹) * (x * z * x⁻¹) ^ (k * a) := by rw [conj_pow]; group
        _ = y * z ^ k * z ^ (k * a) := by rw [h, hxz]
        _ = y * z ^ (k * (a + 1)) := by rw [mul_assoc, ← pow_add, Nat.mul_succ, add_comm]
  rw [← conj_pow, key a, (hzy.symm.pow_right (k * a)).mul_pow, ← pow_mul]

variable {g d c : G}

theorem gd_conj (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (hc13 : c ^ 13 = 1) : g * d * g⁻¹ = d * c ^ 9 := by
  have hcd' : Commute c d := hcd
  have hcg' : Commute c g := hcg
  have hc9 : c ^ 4 * c ^ 9 = 1 := by rw [← pow_add]; exact hc13
  have h1 : g⁻¹ * d * g = d * c ^ 4 := by rw [mul_assoc, hdg, inv_mul_cancel_left]
  calc g * d * g⁻¹ = g * (d * c ^ 4 * c ^ 9) * g⁻¹ := by rw [mul_assoc d, hc9, mul_one]
    _ = g * (g⁻¹ * d * g * c ^ 9) * g⁻¹ := by rw [h1]
    _ = d * (g * c ^ 9 * g⁻¹) := by group
    _ = d * c ^ 9 := by rw [← (hcg'.pow_left 9).eq, mul_inv_cancel_right]

theorem dg_conj (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4)) :
    d * g * d⁻¹ = g * c ^ 4 := by
  have hcd' : Commute c d := hcd
  rw [hdg, ← (hcd'.pow_left 4).eq]
  group

theorem gpow_dpow (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (hc13 : c ^ 13 = 1) (a n : ℕ) : g ^ a * d ^ n = d ^ n * g ^ a * c ^ (9 * a * n) := by
  have hcg' : Commute c g := hcg
  have h := conj_pow_central hcg' hcd (gd_conj hcg hcd hdg hc13) a n
  calc g ^ a * d ^ n = g ^ a * d ^ n * (g ^ a)⁻¹ * g ^ a := by group
    _ = d ^ n * c ^ (9 * a * n) * g ^ a := by rw [h]
    _ = d ^ n * g ^ a * c ^ (9 * a * n) := by
        rw [mul_assoc, (hcg'.pow_pow (9 * a * n) a).eq, ← mul_assoc]

theorem heis_pow (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (hc13 : c ^ 13 = 1) (a b μ : ℕ) :
    ∃ f : ℕ, g ^ (a * μ) * d ^ (b * μ) = (g ^ a * d ^ b) ^ μ * c ^ f := by
  have hcg' : Commute c g := hcg
  have hcd' : Commute c d := hcd
  induction μ with
  | zero => exact ⟨0, by simp⟩
  | succ μ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 9 * a * (b * μ), ?_⟩
    rw [Nat.mul_succ, Nat.mul_succ, pow_add, pow_add, pow_succ]
    calc g ^ (a * μ) * g ^ a * (d ^ (b * μ) * d ^ b) =
        g ^ (a * μ) * ((g ^ a * d ^ (b * μ)) * d ^ b) := by simp only [mul_assoc]
      _ = g ^ (a * μ) * ((d ^ (b * μ) * g ^ a * c ^ (9 * a * (b * μ))) * d ^ b) := by
          rw [gpow_dpow hcg hcd hdg hc13]
      _ = (g ^ (a * μ) * d ^ (b * μ)) * (g ^ a * (c ^ (9 * a * (b * μ)) * d ^ b)) := by
          simp only [mul_assoc]
      _ = (g ^ (a * μ) * d ^ (b * μ)) * (g ^ a * (d ^ b * c ^ (9 * a * (b * μ)))) := by
          rw [(hcd'.pow_pow _ _).eq]
      _ = ((g ^ a * d ^ b) ^ μ * c ^ f) * (g ^ a * (d ^ b * c ^ (9 * a * (b * μ)))) := by rw [hf]
      _ = (g ^ a * d ^ b) ^ μ * (c ^ f * (g ^ a * (d ^ b * c ^ (9 * a * (b * μ))))) := by
          simp only [mul_assoc]
      _ = (g ^ a * d ^ b) ^ μ * (g ^ a * (d ^ b * (c ^ f * c ^ (9 * a * (b * μ))))) := by
          rw [(hcg'.pow_pow f a).left_comm, (hcd'.pow_pow f b).left_comm]
      _ = (g ^ a * d ^ b) ^ μ * (g ^ a * d ^ b) * c ^ (f + 9 * a * (b * μ)) := by
          rw [← pow_add]; simp only [mul_assoc]

theorem heis_pow_choose (hcg : c * g = g * c) (hcd : c * d = d * c)
    (hdg : d * g = g * (d * c ^ 4)) (hc13 : c ^ 13 = 1) (a b μ : ℕ) :
    g ^ (a * μ) * d ^ (b * μ) = (g ^ a * d ^ b) ^ μ * c ^ (9 * a * b * μ.choose 2) := by
  have hcg' : Commute c g := hcg
  have hcd' : Commute c d := hcd
  induction μ with
  | zero => simp
  | succ μ ih =>
    rw [Nat.mul_succ, Nat.mul_succ, pow_add, pow_add, pow_succ, Nat.choose_succ_succ,
      Nat.choose_one_right, show 9 * a * b * (μ + μ.choose 2) =
        9 * a * b * μ.choose 2 + 9 * a * (b * μ) by ring]
    calc g ^ (a * μ) * g ^ a * (d ^ (b * μ) * d ^ b) =
        g ^ (a * μ) * ((g ^ a * d ^ (b * μ)) * d ^ b) := by simp only [mul_assoc]
      _ = g ^ (a * μ) * ((d ^ (b * μ) * g ^ a * c ^ (9 * a * (b * μ))) * d ^ b) := by
          rw [gpow_dpow hcg hcd hdg hc13]
      _ = (g ^ (a * μ) * d ^ (b * μ)) * (g ^ a * (c ^ (9 * a * (b * μ)) * d ^ b)) := by
          simp only [mul_assoc]
      _ = (g ^ (a * μ) * d ^ (b * μ)) * (g ^ a * (d ^ b * c ^ (9 * a * (b * μ)))) := by
          rw [(hcd'.pow_pow _ _).eq]
      _ = ((g ^ a * d ^ b) ^ μ * c ^ (9 * a * b * μ.choose 2)) *
          (g ^ a * (d ^ b * c ^ (9 * a * (b * μ)))) := by rw [ih]
      _ = (g ^ a * d ^ b) ^ μ * (c ^ (9 * a * b * μ.choose 2) *
          (g ^ a * (d ^ b * c ^ (9 * a * (b * μ))))) := by simp only [mul_assoc]
      _ = (g ^ a * d ^ b) ^ μ * (g ^ a * (d ^ b * (c ^ (9 * a * b * μ.choose 2) *
          c ^ (9 * a * (b * μ))))) := by
          rw [(hcg'.pow_pow _ a).left_comm, (hcd'.pow_pow _ b).left_comm]
      _ = (g ^ a * d ^ b) ^ μ * (g ^ a * d ^ b) *
          c ^ (9 * a * b * μ.choose 2 + 9 * a * (b * μ)) := by
          rw [← pow_add]; simp only [mul_assoc]

theorem heis_pow_thirteen (hcg : c * g = g * c) (hcd : c * d = d * c)
    (hdg : d * g = g * (d * c ^ 4)) (hc13 : c ^ 13 = 1) (hg13 : g ^ 13 = 1) (hd13 : d ^ 13 = 1)
    (a b k : ℕ) : (c ^ k * d ^ b * g ^ a) ^ 13 = 1 := by
  have hcg' : Commute c g := hcg
  have hcd' : Commute c d := hcd
  have hswap : d ^ b * g ^ a = g ^ a * d ^ b * c ^ (4 * a * b) := by
    have h := gpow_dpow hcg hcd hdg hc13 a b
    have h13 : c ^ (9 * a * b) * c ^ (4 * a * b) = 1 := by
      rw [← pow_add, show 9 * a * b + 4 * a * b = 13 * (a * b) by ring, pow_mul, hc13, one_pow]
    calc d ^ b * g ^ a = d ^ b * g ^ a * (c ^ (9 * a * b) * c ^ (4 * a * b)) := by
          rw [h13, mul_one]
      _ = g ^ a * d ^ b * c ^ (4 * a * b) := by
          rw [← mul_assoc, ← h]
  have hcomm : Commute (c ^ k) (d ^ b * g ^ a) := (hcd'.pow_pow k b).mul_right (hcg'.pow_pow k a)
  rw [mul_assoc, hcomm.mul_pow, ← pow_mul, show k * 13 = 13 * k by ring, pow_mul c 13, hc13,
    one_pow, one_mul, hswap]
  have hcomm2 : Commute (g ^ a * d ^ b) (c ^ (4 * a * b)) :=
    ((hcg'.pow_pow (4 * a * b) a).symm.mul_left (hcd'.pow_pow (4 * a * b) b).symm)
  rw [hcomm2.mul_pow, ← pow_mul, show 4 * a * b * 13 = 13 * (4 * a * b) by ring, pow_mul c 13, hc13,
    one_pow, mul_one]
  have h := heis_pow_choose hcg hcd hdg hc13 a b 13
  rw [show (13 : ℕ).choose 2 = 13 * 6 by decide, show 9 * a * b * (13 * 6) = 13 * (9 * a * b * 6) by
    ring, pow_mul c 13, hc13, one_pow, mul_one] at h
  rw [← h, pow_mul' g a 13, pow_mul' d b 13, hg13, hd13, one_pow, one_pow, one_mul]

theorem dpow_conj (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (b j : ℕ) : d ^ j * (g * d ^ b) * (d ^ j)⁻¹ = g * d ^ b * c ^ (4 * j) := by
  have hcd' : Commute c d := hcd
  have hcg' : Commute c g := hcg
  have h := conj_pow_central hcd' hcg' (dg_conj hcg hcd hdg) j 1
  simp only [pow_one, Nat.mul_one] at h
  calc d ^ j * (g * d ^ b) * (d ^ j)⁻¹ = (d ^ j * g * (d ^ j)⁻¹) * d ^ b := by group
    _ = g * c ^ (4 * j) * d ^ b := by rw [h]
    _ = g * d ^ b * c ^ (4 * j) := by
        rw [mul_assoc, (hcd'.pow_pow _ _).eq, ← mul_assoc]

theorem gpow_conj_d (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (hc13 : c ^ 13 = 1) (j : ℕ) : g ^ j * d * (g ^ j)⁻¹ = d * c ^ (9 * j) := by
  have h := conj_pow_central (show Commute c g from hcg) hcd (gd_conj hcg hcd hdg hc13) j 1
  simpa only [pow_one, Nat.mul_one] using h

end Heis

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
