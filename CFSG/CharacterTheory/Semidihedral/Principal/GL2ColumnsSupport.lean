module

public import CFSG.CharacterTheory.Semidihedral.Principal.OddKernelGL2Characters
public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.PrincipalNonvanishing

public section

namespace CFSG.Semidihedral.Principal

namespace GL2Columns

open CFSG.TwoRankLowerBound.Helpers GL2ThreeCharacters

universe w

theorem x_system (A1 A2 A3 A4 A5 A6 A7 : ℤ) (h12 : A2 = A1 + 1) (h13 : A3 = A1)
    (h34 : A4 = A3) (h4 : A2 + A5 + A6 = 4) (h5 : A1 + A5 + A7 = 0)
    (hsum : 1 + A1 ^ 2 + A2 ^ 2 + A3 ^ 2 + A4 ^ 2 + A5 ^ 2 + A6 ^ 2 + A7 ^ 2 ≤ 8) :
    A1 = 0 ∧ A2 = 1 ∧ A3 = 0 ∧ A4 = 0 ∧ A5 = 1 ∧ A6 = 2 ∧ A7 = -1 := by
  have h6 : A6 = 3 - A1 - A5 := by omega
  have h7 : A7 = -A1 - A5 := by omega
  subst A2 A3 A4 A6 A7
  have hA1 : A1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (A1 + 1), sq_nonneg A5, sq_nonneg (3 - A1 - A5), sq_nonneg (A1 + A5)]
  have hA5 : A5 ^ 2 ≤ 9 := by
    nlinarith [sq_nonneg (A1 + 1), sq_nonneg A1, sq_nonneg (3 - A1 - A5), sq_nonneg (A1 + A5)]
  have h1l : -1 ≤ A1 := by nlinarith
  have h1u : A1 ≤ 1 := by nlinarith
  have h5l : -3 ≤ A5 := by nlinarith
  have h5u : A5 ≤ 3 := by nlinarith
  revert hsum
  interval_cases A1 <;> interval_cases A5 <;> norm_num

theorem y_system (B1 B2 B3 B4 B5 B6 B7 : ℤ) (h12 : B2 = B1) (h13 : B3 = B1 - 2)
    (h34 : B4 = B3) (h4 : B2 + B5 + B6 = 2) (h5 : B1 + B5 + B7 = 0)
    (hsum : B1 ^ 2 + B2 ^ 2 + B3 ^ 2 + B4 ^ 2 + B5 ^ 2 + B6 ^ 2 + B7 ^ 2 ≤ 6) :
    B1 = 1 ∧ B2 = 1 ∧ B3 = -1 ∧ B4 = -1 ∧ B5 = 0 ∧ B6 = 1 ∧ B7 = -1 := by
  have h6 : B6 = 2 - B1 - B5 := by omega
  have h7 : B7 = -B1 - B5 := by omega
  subst B2 B3 B4 B6 B7
  have h1l : 0 ≤ B1 := by
    nlinarith [sq_nonneg B5, sq_nonneg (2 - B1 - B5), sq_nonneg (B1 + B5)]
  have h1u : B1 ≤ 2 := by
    nlinarith [sq_nonneg B5, sq_nonneg (2 - B1 - B5), sq_nonneg (B1 + B5)]
  have h5l : -2 ≤ B5 := by
    nlinarith [sq_nonneg B1, sq_nonneg (B1 - 2), sq_nonneg (2 - B1 - B5), sq_nonneg (B1 + B5)]
  have h5u : B5 ≤ 2 := by
    nlinarith [sq_nonneg B1, sq_nonneg (B1 - 2), sq_nonneg (2 - B1 - B5), sq_nonneg (B1 + B5)]
  revert hsum
  interval_cases B1 <;> interval_cases B5 <;> norm_num

theorem sq_eq_sign_mul_sq {s : ℤ} (hs : s = 1 ∨ s = -1) (x : ℤ) : x ^ 2 = (s * x) ^ 2 := by
  rcases hs with rfl | rfl <;> ring

theorem eq_sign_mul_sign_mul {s : ℤ} (hs : s = 1 ∨ s = -1) (x : ℤ) : x = s * (s * x) := by
  rcases hs with rfl | rfl <;> ring

theorem sum_sq_split {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ℤ) (l : Fin 8 → ι)
    (hl : Function.Injective l) (hlT : ∀ k, l k ∈ T) :
    ∑ i ∈ T, f i ^ 2 = (∑ k, f (l k) ^ 2) +
      ∑ i ∈ T.filter (fun i => ∀ k, l k ≠ i), f i ^ 2 := by
  have himage : Finset.univ.image l ⊆ T := by
    intro i hi
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hi
    exact hlT k
  have hsdiff : T \ Finset.univ.image l = T.filter (fun i => ∀ k, l k ≠ i) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and, not_exists,
      Finset.mem_filter]
  rw [← Finset.sum_sdiff himage, hsdiff, add_comm,
    Finset.sum_image (fun a _ b _ h => hl h)]

theorem column_coordinates_forced {ι : Type*} (T : Finset ι) (X Y : ι → ℤ)
    (hX : ∑ i ∈ T, X i ^ 2 = 8) (hY : ∑ i ∈ T, Y i ^ 2 = 6)
    (l : Fin 8 → ι) (hl : Function.Injective l) (hlT : ∀ k, l k ∈ T)
    (hX0 : X (l 0) = 1) (hY0 : Y (l 0) = 0) {ε ε₁ ε₂ ε₃ : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (h1x : 1 + ε * (X (l 1) - X (l 2)) = 0) (h1y : ε * (Y (l 1) - Y (l 2)) = 0)
    (h2x : ε * (X (l 1) - X (l 3)) = 0) (h2y : ε * (Y (l 1) - Y (l 3)) = 2)
    (h3x : ε * (X (l 3) - X (l 4)) = 0) (h3y : ε * (Y (l 3) - Y (l 4)) = 0)
    (h4x : ε * X (l 2) + ε₁ * X (l 5) + ε₂ * X (l 6) = 4)
    (h4y : ε * Y (l 2) + ε₁ * Y (l 5) + ε₂ * Y (l 6) = 2)
    (h5x : ε * X (l 1) + ε₁ * X (l 5) + ε₃ * X (l 7) = 0)
    (h5y : ε * Y (l 1) + ε₁ * Y (l 5) + ε₃ * Y (l 7) = 0) :
    (X (l 1) = 0 ∧ Y (l 1) = ε) ∧ (X (l 2) = ε ∧ Y (l 2) = ε) ∧
    (X (l 3) = 0 ∧ Y (l 3) = -ε) ∧ (X (l 4) = 0 ∧ Y (l 4) = -ε) ∧
    (X (l 5) = ε₁ ∧ Y (l 5) = 0) ∧ (X (l 6) = 2 * ε₂ ∧ Y (l 6) = ε₂) ∧
    (X (l 7) = -ε₃ ∧ Y (l 7) = -ε₃) ∧
    ∀ i ∈ T, (∀ k, l k ≠ i) → X i = 0 ∧ Y i = 0 := by
  classical
  rw [sum_sq_split T X l hl hlT, Fin.sum_univ_eight, hX0] at hX
  rw [sum_sq_split T Y l hl hlT, Fin.sum_univ_eight, hY0] at hY
  rw [sq_eq_sign_mul_sq hε (X (l 1)), sq_eq_sign_mul_sq hε (X (l 2)),
    sq_eq_sign_mul_sq hε (X (l 3)), sq_eq_sign_mul_sq hε (X (l 4)),
    sq_eq_sign_mul_sq hε₁ (X (l 5)), sq_eq_sign_mul_sq hε₂ (X (l 6)),
    sq_eq_sign_mul_sq hε₃ (X (l 7))] at hX
  rw [sq_eq_sign_mul_sq hε (Y (l 1)), sq_eq_sign_mul_sq hε (Y (l 2)),
    sq_eq_sign_mul_sq hε (Y (l 3)), sq_eq_sign_mul_sq hε (Y (l 4)),
    sq_eq_sign_mul_sq hε₁ (Y (l 5)), sq_eq_sign_mul_sq hε₂ (Y (l 6)),
    sq_eq_sign_mul_sq hε₃ (Y (l 7))] at hY
  have hrestX := Finset.sum_nonneg (fun i (_ : i ∈ T.filter (fun i => ∀ k, l k ≠ i)) =>
    sq_nonneg (X i))
  have hrestY := Finset.sum_nonneg (fun i (_ : i ∈ T.filter (fun i => ∀ k, l k ≠ i)) =>
    sq_nonneg (Y i))
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := x_system (ε * X (l 1)) (ε * X (l 2)) (ε * X (l 3))
    (ε * X (l 4)) (ε₁ * X (l 5)) (ε₂ * X (l 6)) (ε₃ * X (l 7)) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := y_system (ε * Y (l 1)) (ε * Y (l 2)) (ε * Y (l 3))
    (ε * Y (l 4)) (ε₁ * Y (l 5)) (ε₂ * Y (l 6)) (ε₃ * Y (l 7)) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hzeroX : ∑ i ∈ T.filter (fun i => ∀ k, l k ≠ i), X i ^ 2 = 0 := by
    rw [a1, a2, a3, a4, a5, a6, a7] at hX
    linarith
  have hzeroY : ∑ i ∈ T.filter (fun i => ∀ k, l k ≠ i), Y i ^ 2 = 0 := by
    rw [b1, b2, b3, b4, b5, b6, b7] at hY
    linarith
  rw [eq_sign_mul_sign_mul hε (X (l 1)), eq_sign_mul_sign_mul hε (X (l 2)),
    eq_sign_mul_sign_mul hε (X (l 3)), eq_sign_mul_sign_mul hε (X (l 4)),
    eq_sign_mul_sign_mul hε₁ (X (l 5)), eq_sign_mul_sign_mul hε₂ (X (l 6)),
    eq_sign_mul_sign_mul hε₃ (X (l 7)), eq_sign_mul_sign_mul hε (Y (l 1)),
    eq_sign_mul_sign_mul hε (Y (l 2)), eq_sign_mul_sign_mul hε (Y (l 3)),
    eq_sign_mul_sign_mul hε (Y (l 4)), eq_sign_mul_sign_mul hε₁ (Y (l 5)),
    eq_sign_mul_sign_mul hε₂ (Y (l 6)), eq_sign_mul_sign_mul hε₃ (Y (l 7)),
    a1, a2, a3, a4, a5, a6, a7, b1, b2, b3, b4, b5, b6, b7]
  refine ⟨⟨by ring, by ring⟩, ⟨by ring, by ring⟩, ⟨by ring, by ring⟩, ⟨by ring, by ring⟩,
    ⟨by ring, by ring⟩, ⟨by ring, by ring⟩, ⟨by ring, by ring⟩, fun i hi hni => ?_⟩
  have hmem : i ∈ T.filter (fun i => ∀ k, l k ≠ i) := Finset.mem_filter.mpr ⟨hi, hni⟩
  have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (X j))).mp hzeroX i hmem
  have hy := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (Y j))).mp hzeroY i hmem
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy⟩

theorem column_values_forced {ι : Type*} (T : Finset ι) (u v : ι → ℂ)
    (hcoord : ∀ i ∈ T, ∃ x y : ℤ, u i = x + 2 * y ∧ v i = x - y)
    (htt : ∑ i ∈ T, u i ^ 2 = 48) (hqq : ∑ i ∈ T, v i ^ 2 = 6)
    (htq : ∑ i ∈ T, u i * v i = 0)
    (l : Fin 8 → ι) (hl : Function.Injective l) (hlT : ∀ k, l k ∈ T)
    (hu0 : u (l 0) = 1) (hv0 : v (l 0) = 1) {ε ε₁ ε₂ ε₃ : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (h1t : 0 = 1 + (ε : ℂ) * (u (l 1) - u (l 2)))
    (h1q : 0 = 1 + (ε : ℂ) * (v (l 1) - v (l 2)))
    (h2t : 4 = (ε : ℂ) * (u (l 1) - u (l 3))) (h2q : -2 = (ε : ℂ) * (v (l 1) - v (l 3)))
    (h3t : 0 = (ε : ℂ) * (u (l 3) - u (l 4))) (h3q : 0 = (ε : ℂ) * (v (l 3) - v (l 4)))
    (h4t : 8 = (ε : ℂ) * u (l 2) + (ε₁ : ℂ) * u (l 5) + (ε₂ : ℂ) * u (l 6))
    (h4q : 2 = (ε : ℂ) * v (l 2) + (ε₁ : ℂ) * v (l 5) + (ε₂ : ℂ) * v (l 6))
    (h5t : 0 = (ε : ℂ) * u (l 1) + (ε₁ : ℂ) * u (l 5) + (ε₃ : ℂ) * u (l 7))
    (h5q : 0 = (ε : ℂ) * v (l 1) + (ε₁ : ℂ) * v (l 5) + (ε₃ : ℂ) * v (l 7)) :
    (u (l 1) = 2 * ε ∧ v (l 1) = -ε) ∧ (u (l 2) = 3 * ε ∧ v (l 2) = 0) ∧
    (u (l 3) = -2 * ε ∧ v (l 3) = ε) ∧ (u (l 4) = -2 * ε ∧ v (l 4) = ε) ∧
    (u (l 5) = ε₁ ∧ v (l 5) = ε₁) ∧ (u (l 6) = 4 * ε₂ ∧ v (l 6) = ε₂) ∧
    (u (l 7) = -3 * ε₃ ∧ v (l 7) = 0) ∧
    ∀ i ∈ T, (∀ k, l k ≠ i) → u i = 0 ∧ v i = 0 := by
  choose! X Y hXY using hcoord
  have hXsum : ∑ i ∈ T, X i ^ 2 = 8 := by
    have h : ∑ i ∈ T, ((X i : ℂ)) ^ 2 =
        (∑ i ∈ T, u i ^ 2 + 4 * ∑ i ∈ T, u i * v i + 4 * ∑ i ∈ T, v i ^ 2) / 9 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hXY i hi).1, (hXY i hi).2]
      ring
    rw [htt, htq, hqq] at h
    norm_num at h
    exact_mod_cast h
  have hYsum : ∑ i ∈ T, Y i ^ 2 = 6 := by
    have h : ∑ i ∈ T, ((Y i : ℂ)) ^ 2 =
        (∑ i ∈ T, u i ^ 2 - 2 * ∑ i ∈ T, u i * v i + ∑ i ∈ T, v i ^ 2) / 9 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hXY i hi).1, (hXY i hi).2]
      ring
    rw [htt, htq, hqq] at h
    norm_num at h
    exact_mod_cast h
  have e : ∀ k, u (l k) = X (l k) + 2 * Y (l k) ∧ v (l k) = X (l k) - Y (l k) :=
    fun k => hXY (l k) (hlT k)
  rw [(e 0).1] at hu0
  rw [(e 0).2] at hv0
  rw [(e 1).1, (e 2).1] at h1t
  rw [(e 1).2, (e 2).2] at h1q
  rw [(e 1).1, (e 3).1] at h2t
  rw [(e 1).2, (e 3).2] at h2q
  rw [(e 3).1, (e 4).1] at h3t
  rw [(e 3).2, (e 4).2] at h3q
  rw [(e 2).1, (e 5).1, (e 6).1] at h4t
  rw [(e 2).2, (e 5).2, (e 6).2] at h4q
  rw [(e 1).1, (e 5).1, (e 7).1] at h5t
  rw [(e 1).2, (e 5).2, (e 7).2] at h5q
  have hu0' : X (l 0) + 2 * Y (l 0) = 1 := by exact_mod_cast hu0
  have hv0' : X (l 0) - Y (l 0) = 1 := by exact_mod_cast hv0
  have h1x : 1 + ε * (X (l 1) - X (l 2)) = 0 := by
    have h : (1 : ℂ) + ε * (X (l 1) - X (l 2)) = 0 := by
      linear_combination (-1 / 3 : ℂ) * h1t + (-2 / 3 : ℂ) * h1q
    exact_mod_cast h
  have h1y : ε * (Y (l 1) - Y (l 2)) = 0 := by
    have h : (ε : ℂ) * (Y (l 1) - Y (l 2)) = 0 := by
      linear_combination (-1 / 3 : ℂ) * h1t + (1 / 3 : ℂ) * h1q
    exact_mod_cast h
  have h2x : ε * (X (l 1) - X (l 3)) = 0 := by
    have h : (ε : ℂ) * (X (l 1) - X (l 3)) = 0 := by
      linear_combination (-1 / 3 : ℂ) * h2t + (-2 / 3 : ℂ) * h2q
    exact_mod_cast h
  have h2y : ε * (Y (l 1) - Y (l 3)) = 2 := by
    have h : (ε : ℂ) * (Y (l 1) - Y (l 3)) = 2 := by
      linear_combination (-1 / 3 : ℂ) * h2t + (1 / 3 : ℂ) * h2q
    exact_mod_cast h
  have h3x : ε * (X (l 3) - X (l 4)) = 0 := by
    have h : (ε : ℂ) * (X (l 3) - X (l 4)) = 0 := by
      linear_combination (-1 / 3 : ℂ) * h3t + (-2 / 3 : ℂ) * h3q
    exact_mod_cast h
  have h3y : ε * (Y (l 3) - Y (l 4)) = 0 := by
    have h : (ε : ℂ) * (Y (l 3) - Y (l 4)) = 0 := by
      linear_combination (-1 / 3 : ℂ) * h3t + (1 / 3 : ℂ) * h3q
    exact_mod_cast h
  have h4x : ε * X (l 2) + ε₁ * X (l 5) + ε₂ * X (l 6) = 4 := by
    have h : (ε : ℂ) * X (l 2) + ε₁ * X (l 5) + ε₂ * X (l 6) = 4 := by
      linear_combination (-1 / 3 : ℂ) * h4t + (-2 / 3 : ℂ) * h4q
    exact_mod_cast h
  have h4y : ε * Y (l 2) + ε₁ * Y (l 5) + ε₂ * Y (l 6) = 2 := by
    have h : (ε : ℂ) * Y (l 2) + ε₁ * Y (l 5) + ε₂ * Y (l 6) = 2 := by
      linear_combination (-1 / 3 : ℂ) * h4t + (1 / 3 : ℂ) * h4q
    exact_mod_cast h
  have h5x : ε * X (l 1) + ε₁ * X (l 5) + ε₃ * X (l 7) = 0 := by
    have h : (ε : ℂ) * X (l 1) + ε₁ * X (l 5) + ε₃ * X (l 7) = 0 := by
      linear_combination (-1 / 3 : ℂ) * h5t + (-2 / 3 : ℂ) * h5q
    exact_mod_cast h
  have h5y : ε * Y (l 1) + ε₁ * Y (l 5) + ε₃ * Y (l 7) = 0 := by
    have h : (ε : ℂ) * Y (l 1) + ε₁ * Y (l 5) + ε₃ * Y (l 7) = 0 := by
      linear_combination (-1 / 3 : ℂ) * h5t + (1 / 3 : ℂ) * h5q
    exact_mod_cast h
  obtain ⟨⟨x1, y1⟩, ⟨x2, y2⟩, ⟨x3, y3⟩, ⟨x4, y4⟩, ⟨x5, y5⟩, ⟨x6, y6⟩, ⟨x7, y7⟩, hrest⟩ :=
    column_coordinates_forced T X Y hXsum hYsum l hl hlT (by omega) (by omega) hε hε₁ hε₂ hε₃
      h1x h1y h2x h2y h3x h3y h4x h4y h5x h5y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi hni => ?_⟩
  · rw [(e 1).1, (e 1).2, x1, y1]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  · rw [(e 2).1, (e 2).2, x2, y2]
    exact ⟨by ring, by ring⟩
  · rw [(e 3).1, (e 3).2, x3, y3]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  · rw [(e 4).1, (e 4).2, x4, y4]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  · rw [(e 5).1, (e 5).2, x5, y5]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  · rw [(e 6).1, (e 6).2, x6, y6]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  · rw [(e 7).1, (e 7).2, x7, y7]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  · obtain ⟨hx, hy⟩ := hrest i hi hni
    rw [(hXY i hi).1, (hXY i hi).2, hx, hy]
    simp

theorem exists_label_of_mem_blocksIrr {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) {χ : G → ℂ} (hχ : χ ∈ CFSG.BlocksIrr G) :
    ∃ l : basis.index, (basis.representation l).character = χ := by
  rw [CFSG.blocksIrr_eq_irreducible_characters] at hχ
  obtain ⟨data, hirr, rfl⟩ := hχ
  exact finiteIrreducibleCharacterBasis_contains_irreducible basis data hirr

theorem label_mem_blocksIrr {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (l : basis.index) :
    (basis.representation l).character ∈ CFSG.BlocksIrr G := by
  rw [CFSG.blocksIrr_eq_irreducible_characters]
  exact ⟨basis.representation l, basis.irreducible l, rfl⟩

theorem injective_of_nodup {G : Type} [Group G] {χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G}
    (hnd : [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup) (h1 : (χ₁ : G → ℂ) ≠ 1)
    (h2 : (χ₂ : G → ℂ) ≠ 1) (h3 : (χ₃ : G → ℂ) ≠ 1) (h4 : (χ₄ : G → ℂ) ≠ 1)
    (h5 : (χ₅ : G → ℂ) ≠ 1) (h6 : (χ₆ : G → ℂ) ≠ 1) (h7 : (χ₇ : G → ℂ) ≠ 1) :
    Function.Injective (![1, (χ₁ : G → ℂ), χ₂, χ₃, χ₄, χ₅, χ₆, χ₇] : Fin 8 → G → ℂ) := by
  rw [← List.nodup_ofFn]
  have hmap : ([χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].map Subtype.val).Nodup :=
    hnd.map Subtype.val_injective
  have hlist : List.ofFn (![1, (χ₁ : G → ℂ), χ₂, χ₃, χ₄, χ₅, χ₆, χ₇] : Fin 8 → G → ℂ) =
      1 :: [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].map Subtype.val := by
    simp [List.ofFn_succ]
  rw [hlist, List.nodup_cons]
  refine ⟨?_, hmap⟩
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm⟩

theorem label_coords (basis : FiniteIrreducibleCharacterBasis G23) {a p b : G23}
    (ha : orderOf a = 8) (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center G23) (l : basis.index) :
    ∃ x y : ℤ, (basis.representation l).character (-1) = x + 2 * y ∧
      (basis.representation l).character (-1 * p) = x - y := by
  obtain ⟨-, -, -, -, φ, hφ, -, hval, -⟩ :=
    GL2_three_ordinary_character_table_construction basis a p b ha hp hb hbz
  obtain ⟨i, rfl⟩ := hφ.2 l
  have h1 := hval i 1
  have h4 := hval i 4
  fin_cases i
  · exact ⟨1, 0, by norm_num at h1 ⊢; linear_combination h1,
    by norm_num at h4 ⊢; linear_combination h4⟩
  · exact ⟨1, 0, by norm_num at h1 ⊢; linear_combination h1,
    by norm_num at h4 ⊢; linear_combination h4⟩
  · exact ⟨0, 1, by norm_num at h1 ⊢; linear_combination h1,
    by norm_num at h4 ⊢; linear_combination h4⟩
  · exact ⟨1, 1, by norm_num at h1 ⊢; linear_combination h1,
    by norm_num at h4 ⊢; linear_combination h4⟩
  · exact ⟨1, 1, by norm_num at h1 ⊢; linear_combination h1,
    by norm_num at h4 ⊢; linear_combination h4⟩
  · exact ⟨-2, -1, by norm_num at h1 ⊢; linear_combination h1,
    by norm_num at h4 ⊢; linear_combination h4⟩
  · exact ⟨0, -1, by norm_num at h1 ⊢; linear_combination h1,
    by norm_num at h4 ⊢; linear_combination h4⟩
  · exact ⟨0, -1, by norm_num at h1 ⊢; linear_combination h1,
    by norm_num at h4 ⊢; linear_combination h4⟩

theorem sum_label_coords (basis : FiniteIrreducibleCharacterBasis G23) {a p b : G23}
    (ha : orderOf a = 8) (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center G23) (s : Finset basis.index) (m : basis.index → ℤ) :
    ∃ x y : ℤ, ∑ l ∈ s, (m l : ℂ) * (basis.representation l).character (-1) = x + 2 * y ∧
      ∑ l ∈ s, (m l : ℂ) * (basis.representation l).character (-1 * p) = x - y := by
  choose x y hxy using label_coords basis ha hp hb hbz
  refine ⟨∑ l ∈ s, m l * x l, ∑ l ∈ s, m l * y l, ?_, ?_⟩
  · push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [(hxy l).1]; ring
  · push_cast
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [(hxy l).2]; ring

theorem character_coords {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23)
    (data : FiniteComplexRepresentation.{0, w} G23) :
    ∃ x y : ℤ, data.character (-1) = x + 2 * y ∧ data.character (-1 * p) = x - y := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G23)
  have hsum := character_eq_sum_multiplicity basis data
  choose m hm using characterPairing_basis_natural basis data
  obtain ⟨x, y, hx, hy⟩ := sum_label_coords basis ha hp hb hbz Finset.univ (fun l => m l)
  refine ⟨x, y, ?_, ?_⟩
  · rw [hsum, ← hx]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm, Int.cast_natCast]
  · rw [hsum, ← hy]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm, Int.cast_natCast]

theorem card_centralizer_neg_one_mul {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23) :
    Nat.card (Subgroup.centralizer ({-1 * p} : Set G23)) = 6 := by
  have h := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer (-1 * p : G23)
  obtain ⟨-, -, hsize⟩ := GL2OddKernel.rep_facts ha hp hb hbz
  have h8 : Nat.card (ConjClasses.mk (-1 * p : G23)).carrier = 8 := by
    have e : Nat.card {h : G23 // IsConj (-1 * p) h} = 8 := hsize 4
    rw [← e]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun h => by
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm])
  rw [h8, card_G23] at h
  omega

theorem t_mul_mem_section {G : Type*} [Group G] {t : G} (ht : orderOf t = 2) {r : G}
    (hr : r ∈ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf r)) :
    t * r ∈ centralInvolutionSection t := by
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcomm : Commute t r := (Subgroup.mem_centralizer_singleton_iff.mp hr).symm
  have hcop : Nat.Coprime (orderOf t) (orderOf r) := by
    rw [ht]
    exact Nat.coprime_two_left.mpr hodd
  have hord : orderOf (t * r) = 2 * orderOf r := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ht]
  refine ⟨Subgroup.mul_mem _ htC hr, ?_, ?_⟩
  · rw [hord]
    exact even_two_mul _
  · rw [hord, Nat.mul_div_cancel_left _ (by norm_num), hcomm.mul_pow, pow_orderOf_eq_one,
      mul_one]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, ← ht, pow_orderOf_eq_one, one_pow, one_mul]

theorem self_mem_section {G : Type*} [Group G] {t : G} (ht : orderOf t = 2) :
    t ∈ centralInvolutionSection t := by
  simpa using t_mul_mem_section ht (Subgroup.one_mem _) (by simp)

theorem odd_orderOf_of_map_eq {G : Type*} [Group G] {t : G}
    (π : Subgroup.centralizer ({t} : Set G) →* G23) (hN : Odd (Nat.card π.ker)) {p : G23}
    (hp : orderOf p = 3) (q : Subgroup.centralizer ({t} : Set G)) (hq : π q = p) :
    Odd (orderOf q) := by
  have hp3 : p ^ 3 = 1 := by
    have h := pow_orderOf_eq_one p
    rwa [hp] at h
  have hker : q ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hq, hp3]
  have hodd3 : Odd (orderOf (q ^ 3)) := hN.of_dvd_nat (π.ker.orderOf_dvd_natCard hker)
  have hdvd : orderOf q ∣ 3 * orderOf (q ^ 3) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  exact (Odd.mul (by decide) hodd3).of_dvd_nat hdvd

section Induced

open GL2OddKernel

variable {G : Type} [Group G] [Fintype G] {t : G}

omit [Fintype G] in
theorem bigPhi_comp_eq_zero_of_not_mem (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* G23) (hN : Odd (Nat.card π.ker))
    (hπt : π (tC t) = -1) {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23) {φ : Fin 8 → G23 → ℂ}
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr G23)
    (hφ' : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8)
    (i : Fin 5) (x : Subgroup.centralizer ({t} : Set G))
    (hx : (x : G) ∉ centralInvolutionSection t) : bigPhi φ i (π x) = 0 := by
  obtain ⟨k, hk⟩ := (rep_facts ha hp hb hbz).1 (π x)
  have hval : bigPhi φ i (π x) = bigPhi φ i (rep a p b k) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hk
    rw [← hc, bigPhi_conj hφirr]
  rw [hval]
  rcases fin8_cases k with hk' | hk''
  · exact bigPhi_rep_zero hφ' i k hk'
  · exfalso
    exact hx (mem_section_of_neg_one_mem π ht hN hπt x
      (neg_one_mem_zpowers_conj hk (neg_one_mem_zpowers_rep ha hp k hk'')))

theorem induced_bigPhi_eq_on_section (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* G23) (hN : Odd (Nat.card π.ker))
    (hπt : π (tC t) = -1) {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23) {φ : Fin 8 → G23 → ℂ}
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr G23)
    (hφ' : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8)
    (i : Fin 5) (x : Subgroup.centralizer ({t} : Set G))
    (hx : (x : G) ∈ centralInvolutionSection t) :
    inducedFunction (Subgroup.centralizer ({t} : Set G)) (fun c => bigPhi φ i (π c)) x =
      bigPhi φ i (π x) := by
  refine ((central_involution_section_induction_isometry t).1 _ (fun g h => ?_)
    (fun y hy => bigPhi_comp_eq_zero_of_not_mem ht π hN hπt ha hp hb hbz hφirr hφ' i y hy)).1
      x hx
  simp only [map_mul, map_inv]
  exact bigPhi_conj hφirr i _ _

theorem bigPhi_columns {a p b : G23} {φ : Fin 8 → G23 → ℂ}
    (hφ' : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8) :
    bigPhi φ 0 (-1) = 0 ∧ bigPhi φ 0 (-1 * p) = 0 ∧ bigPhi φ 1 (-1) = 4 ∧
      bigPhi φ 1 (-1 * p) = -2 ∧ bigPhi φ 2 (-1) = 0 ∧ bigPhi φ 2 (-1 * p) = 0 ∧
      bigPhi φ 3 (-1) = 8 ∧ bigPhi φ 3 (-1 * p) = 2 ∧ bigPhi φ 4 (-1) = 0 ∧
      bigPhi φ 4 (-1 * p) = 0 := by
  have h1 : ∀ i, bigPhi φ i (-1) = (phiA i 1 : ℂ) + (phiB i 1 : ℂ) * omega8 :=
    fun i => bigPhi_rep hφ' i 1
  have h4 : ∀ i, bigPhi φ i (-1 * p) = (phiA i 4 : ℂ) + (phiB i 4 : ℂ) * omega8 :=
    fun i => bigPhi_rep hφ' i 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | (rw [h1]; simp [phiA, phiB]) | (rw [h4]; simp [phiA, phiB])

theorem columns_of_identities (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* G23) (hN : Odd (Nat.card π.ker))
    (hπt : π (tC t) = -1) {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23) {φ : Fin 8 → G23 → ℂ}
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr G23)
    (hφ' : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8)
    (q : Subgroup.centralizer ({t} : Set G)) (hq : π q = p)
    (basis : FiniteIrreducibleCharacterBasis G) (T : Finset basis.index)
    (hcoord : ∀ i ∈ T, ∃ x y : ℤ, (basis.representation i).character t = x + 2 * y ∧
      (basis.representation i).character (t * q) = x - y)
    (htt : ∑ i ∈ T, (basis.representation i).character t ^ 2 = 48)
    (hqq : ∑ i ∈ T, (basis.representation i).character (t * q) ^ 2 = 6)
    (htq : ∑ i ∈ T, (basis.representation i).character t *
      (basis.representation i).character (t * q) = 0)
    (c : Fin 8 → G → ℂ) (hc0 : c 0 = 1) (l : Fin 8 → basis.index)
    (hl : ∀ k, (basis.representation (l k)).character = c k) (hlinj : Function.Injective l)
    (hlT : ∀ k, l k ∈ T) {ε ε₁ ε₂ ε₃ : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hβ0 : inducedFunction (Subgroup.centralizer ({t} : Set G)) (fun x => bigPhi φ 0 (π x)) =
      1 + (ε : ℂ) • (c 1 - c 2))
    (hβ1 : inducedFunction (Subgroup.centralizer ({t} : Set G)) (fun x => bigPhi φ 1 (π x)) =
      (ε : ℂ) • (c 1 - c 3))
    (hβ2 : inducedFunction (Subgroup.centralizer ({t} : Set G)) (fun x => bigPhi φ 2 (π x)) =
      (ε : ℂ) • (c 3 - c 4))
    (hβ3 : inducedFunction (Subgroup.centralizer ({t} : Set G)) (fun x => bigPhi φ 3 (π x)) =
      (ε : ℂ) • c 2 + (ε₁ : ℂ) • c 5 + (ε₂ : ℂ) • c 6)
    (hβ4 : inducedFunction (Subgroup.centralizer ({t} : Set G)) (fun x => bigPhi φ 4 (π x)) =
      (ε : ℂ) • c 1 + (ε₁ : ℂ) • c 5 + (ε₃ : ℂ) • c 7) :
    (c 1 t = 2 * ε ∧ c 1 (t * q) = -ε) ∧ (c 2 t = 3 * ε ∧ c 2 (t * q) = 0) ∧
    (c 3 t = -2 * ε ∧ c 3 (t * q) = ε) ∧ (c 4 t = -2 * ε ∧ c 4 (t * q) = ε) ∧
    (c 5 t = ε₁ ∧ c 5 (t * q) = ε₁) ∧ (c 6 t = 4 * ε₂ ∧ c 6 (t * q) = ε₂) ∧
    (c 7 t = -3 * ε₃ ∧ c 7 (t * q) = 0) ∧
    ∀ i ∈ T, (∀ k, l k ≠ i) →
      (basis.representation i).character t = 0 ∧
        (basis.representation i).character (t * q) = 0 := by
  have hCt : ((tC t : Subgroup.centralizer ({t} : Set G)) : G) ∈ centralInvolutionSection t :=
    self_mem_section ht
  have hqodd := odd_orderOf_of_map_eq π hN hp q hq
  have hCtq : ((tC t * q : Subgroup.centralizer ({t} : Set G)) : G) ∈
      centralInvolutionSection t :=
    t_mul_mem_section ht q.2 (by rwa [Subgroup.orderOf_coe])
  have hπtq : π (tC t * q) = -1 * p := by rw [map_mul, hπt, hq]
  obtain ⟨v01, v04, v11, v14, v21, v24, v31, v34, v41, v44⟩ := bigPhi_columns hφ'
  have hβt : ∀ i, inducedFunction (Subgroup.centralizer ({t} : Set G))
      (fun x => bigPhi φ i (π x)) t = bigPhi φ i (-1) := fun i => by
    have h := induced_bigPhi_eq_on_section ht π hN hπt ha hp hb hbz hφirr hφ' i (tC t) hCt
    rw [hπt] at h
    exact h
  have hβq : ∀ i, inducedFunction (Subgroup.centralizer ({t} : Set G))
      (fun x => bigPhi φ i (π x)) (t * q) = bigPhi φ i (-1 * p) := fun i => by
    have h := induced_bigPhi_eq_on_section ht π hN hπt ha hp hb hbz hφirr hφ' i
      (tC t * q) hCtq
    rw [hπtq] at h
    exact h
  have e0t := congrFun hβ0 t
  have e0q := congrFun hβ0 (t * q)
  have e1t := congrFun hβ1 t
  have e1q := congrFun hβ1 (t * q)
  have e2t := congrFun hβ2 t
  have e2q := congrFun hβ2 (t * q)
  have e3t := congrFun hβ3 t
  have e3q := congrFun hβ3 (t * q)
  have e4t := congrFun hβ4 t
  have e4q := congrFun hβ4 (t * q)
  rw [hβt, v01] at e0t
  rw [hβq, v04] at e0q
  rw [hβt, v11] at e1t
  rw [hβq, v14] at e1q
  rw [hβt, v21] at e2t
  rw [hβq, v24] at e2q
  rw [hβt, v31] at e3t
  rw [hβq, v34] at e3q
  rw [hβt, v41] at e4t
  rw [hβq, v44] at e4q
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul,
    ← hl] at e0t e0q e1t e1q e2t e2q e3t e3q e4t e4q
  have hu0 : (basis.representation (l 0)).character t = 1 := by rw [hl 0, hc0]; rfl
  have hv0 : (basis.representation (l 0)).character (t * q) = 1 := by rw [hl 0, hc0]; rfl
  obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩, hrest⟩ :=
    column_values_forced T (fun i => (basis.representation i).character t)
      (fun i => (basis.representation i).character (t * q)) hcoord htt hqq htq l hlinj hlT
      hu0 hv0 hε hε₁ hε₂ hε₃ e0t e0q (by linear_combination e1t) (by linear_combination e1q)
      e2t e2q (by linear_combination e3t) (by linear_combination e3q) e4t e4q
  simp only [hl] at a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7
  exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩, hrest⟩

end Induced

end GL2Columns

end CFSG.Semidihedral.Principal
