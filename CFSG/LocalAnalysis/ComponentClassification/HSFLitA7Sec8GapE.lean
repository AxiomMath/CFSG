module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapFix

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

namespace GapE

@[expose] def top (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem top_mul {M N : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h0 : M 0 2 = 0) (h1 : M 1 2 = 0) :
    top (M * N) = top M * top N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [top, Matrix.mul_apply, Fin.sum_univ_three, h0, h1]

theorem top_one : top 1 = 1 := by decide

theorem top_pow {M : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h0 : M 0 2 = 0) (h1 : M 1 2 = 0) :
    ∀ n : ℕ, top (M ^ n) = top M ^ n
  | 0 => by rw [pow_zero, pow_zero, top_one]
  | n + 1 => by rw [pow_succ', pow_succ', top_mul h0 h1, top_pow h0 h1 n]

theorem pow_eight (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) (h : B ^ 8 = 1) : B ^ 4 = 1 := by
  rw [Matrix.eta_fin_two B] at h ⊢
  generalize B 0 0 = p at h ⊢
  generalize B 0 1 = q at h ⊢
  generalize B 1 0 = r at h ⊢
  generalize B 1 1 = s at h ⊢
  revert p q r s
  decide

theorem pow_four_of_two_pow :
    ∀ (m : ℕ) (B : Matrix (Fin 2) (Fin 2) (ZMod 2)), B ^ 2 ^ m = 1 → B ^ 4 = 1
  | 0, B, h => by rw [pow_zero, pow_one] at h; rw [h, one_pow]
  | 1, B, h => by rw [show 4 = 2 ^ 1 * 2 by rfl, pow_mul, h, one_pow]
  | 2, _, h => h
  | m + 3, B, h => by
    have h8 : (B ^ 2 ^ m) ^ 8 = 1 := by
      rw [← pow_mul, show 2 ^ m * 8 = 2 ^ (m + 3) by ring]
      exact h
    refine pow_four_of_two_pow (m + 2) B ?_
    rw [show 2 ^ (m + 2) = 2 ^ m * 4 by ring, pow_mul]
    exact pow_eight _ h8

theorem top_cases (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) (h : B ^ 4 = 1)
    (hU : (B * !![1, 1; 0, 1]) ^ 4 = 1) : B = 1 ∨ B = !![1, 1; 0, 1] := by
  rw [Matrix.eta_fin_two B] at h hU ⊢
  generalize B 0 0 = p at h hU ⊢
  generalize B 0 1 = q at h hU ⊢
  generalize B 1 0 = r at h hU ⊢
  generalize B 1 1 = s at h hU ⊢
  revert p q r s
  decide

theorem top_Ub : top (blk 1 1 0 1) = !![1, 1; 0, 1] := by decide

theorem sq_E4 : ∀ e f : ZMod 2,
    !![1, 0, 0; 0, 1, 0; e, f, 1] * !![1, 0, 0; 0, 1, 0; e, f, 1] = 1 := by
  decide

theorem col_zero : ∀ m00 m01 m11 m02 m21 : ZMod 4, r2 m00 = 1 → r2 m11 = 1 → r2 m01 = 0 →
    r2 m02 = 0 → r2 m21 = 1 → m00 * m01 + m01 * m11 + m02 * m21 = 0 → m02 = 0 := by
  decide

theorem col_zero' : ∀ m00 m11 m02 m20 : ZMod 4, r2 m00 = 1 → r2 m11 = 1 → r2 m02 = 0 →
    r2 m20 = 1 → m00 * m00 + m02 * m20 = m11 * m11 → m02 = 0 := by
  decide

theorem entries_four {P : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (h : P = 1 ∨ P = -1 ∨ P = Dmat ∨ P = -Dmat) : P 0 1 = 0 ∧ P 1 0 = 0 ∧ P 0 0 = P 1 1 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem col_four {P : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (h : P = 1 ∨ P = -1 ∨ P = Dmat ∨ P = -Dmat) : P 0 2 = 0 ∧ P 1 2 = 0 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem r2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem mul_apply_three (N : Matrix (Fin 3) (Fin 3) (ZMod 4)) (i j : Fin 3) :
    (N * N) i j = N i 0 * N 0 j + N i 1 * N 1 j + N i 2 * N 2 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem col_mulVec {R : Type} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R) (x : R) (i : Fin 3) :
    (N *ᵥ ![0, 0, x]) i = N i 2 * x := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem col_mulVec₀ {R : Type} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R) (x : R) (i : Fin 3) :
    (N *ᵥ ![x, 0, 0]) i = N i 0 * x := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end GapE

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

theorem BData.redM_col (A : BData S F T₁) (hnc : ¬ SubConj F.E₁ F.E₂) (n : A.NA) :
    r2 (A.mat n 0 2) = 0 ∧ r2 (A.mat n 1 2) = 0 ∧ r2 (A.mat n 2 2) = 1 := by
  have h := A.mulVec_c hnc n
  have e : ∀ i, r2 (A.mat n i 2) = ![0, 0, 1] i := fun i => by
    rw [← congrFun h i, GapE.col_mulVec, mul_one]
    rfl
  exact ⟨e 0, e 1, e 2⟩

namespace BData.Syl

variable {A : BData S F T₁} (Y : A.Syl)

open GapE

theorem top_cases (hnc : ¬ SubConj F.E₁ F.E₂) {p : X} (hp : p ∈ Y.P) :
    top (redM (A.mat ⟨p, Y.mem_NA hp⟩)) = 1 ∨
      top (redM (A.mat ⟨p, Y.mem_NA hp⟩)) = !![1, 1; 0, 1] := by
  have key : ∀ x : X, ∀ hx : x ∈ Y.P, top (redM (A.mat ⟨x, Y.mem_NA hx⟩)) ^ 4 = 1 := by
    intro x hx
    obtain ⟨m, hm⟩ := Y.isPGroup ⟨x, hx⟩
    have hm' : (⟨x, Y.mem_NA hx⟩ : A.NA) ^ 2 ^ m = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hm)
    have h1 : redM (A.mat ⟨x, Y.mem_NA hx⟩) ^ 2 ^ m = 1 := by
      rw [← redM_pow, ← BData.matHom_apply, ← map_pow, hm', map_one, redM_one]
    obtain ⟨c0, c1, -⟩ := A.redM_col hnc ⟨x, Y.mem_NA hx⟩
    refine pow_four_of_two_pow m _ ?_
    rw [← top_pow c0 c1, h1, top_one]
  have hu := key _ (mul_mem hp Y.u_mem)
  rw [show (⟨p * A.D₁.u, Y.mem_NA (mul_mem hp Y.u_mem)⟩ : A.NA) =
    ⟨p, Y.mem_NA hp⟩ * ⟨A.D₁.u, A.u_mem_NA⟩ from rfl, A.mat_mul, A.mat_u, redM_mul,
    GapNH.redM_Umat] at hu
  obtain ⟨c0, c1, -⟩ := A.redM_col hnc ⟨p, Y.mem_NA hp⟩
  rw [top_mul c0 c1, top_Ub] at hu
  exact GapE.top_cases _ (key p hp) hu

theorem col_of_top (hnc : ¬ SubConj F.E₁ F.E₂) {p : X} (hp : p ∈ Y.P)
    (htop : top (redM (A.mat ⟨p, Y.mem_NA hp⟩)) = 1) :
    A.mat ⟨p, Y.mem_NA hp⟩ 0 2 = 0 ∧ A.mat ⟨p, Y.mem_NA hp⟩ 1 2 = 0 := by
  obtain ⟨c0, c1, c2⟩ := A.redM_col hnc ⟨p, Y.mem_NA hp⟩
  set N := A.mat ⟨p, Y.mem_NA hp⟩ with hN
  have t00 : r2 (N 0 0) = 1 := congrFun (congrFun htop 0) 0
  have t01 : r2 (N 0 1) = 0 := congrFun (congrFun htop 0) 1
  have t10 : r2 (N 1 0) = 0 := congrFun (congrFun htop 1) 0
  have t11 : r2 (N 1 1) = 1 := congrFun (congrFun htop 1) 1
  have hred : redM N = !![1, 0, 0; 0, 1, 0; r2 (N 2 0), r2 (N 2 1), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [redM, t00, t01, t10, t11, c0, c1, c2]
  have hp2 : redM (A.mat ⟨p * p, Y.mem_NA (mul_mem hp hp)⟩) = 1 := by
    rw [show (⟨p * p, Y.mem_NA (mul_mem hp hp)⟩ : A.NA) = ⟨p, Y.mem_NA hp⟩ * ⟨p, Y.mem_NA hp⟩
      from rfl, A.mat_mul, redM_mul, ← hN, hred, sq_E4]
  have h4 := Y.mat_mem_of_redM hnc (mul_mem hp hp) hp2
  rw [show (⟨p * p, Y.mem_NA (mul_mem hp hp)⟩ : A.NA) = ⟨p, Y.mem_NA hp⟩ * ⟨p, Y.mem_NA hp⟩
    from rfl, A.mat_mul, ← hN] at h4
  obtain ⟨e01, e10, e00⟩ := entries_four h4
  rw [mul_apply_three] at e01 e10
  rw [mul_apply_three, mul_apply_three] at e00
  rcases r2_cases (r2 (N 2 0)) with h20 | h20 <;> rcases r2_cases (r2 (N 2 1)) with h21 | h21
  ·
    have hr : redM N = 1 := by rw [hred, h20, h21]; decide
    exact col_four (Y.mat_mem_of_redM hnc hp hr)
  · have h02 : N 0 2 = 0 := col_zero _ _ _ _ _ t00 t11 t01 c0 h21 e01
    refine ⟨h02, col_zero' (N 1 1) (N 0 0) (N 1 2) (N 2 1) t11 t00 c1 h21 ?_⟩
    rw [h02] at e00
    linear_combination -e00
  · have h12 : N 1 2 = 0 := col_zero (N 1 1) (N 1 0) (N 0 0) (N 1 2) (N 2 0) t11 t00 t10 c1 h20
      (by linear_combination e10)
    refine ⟨col_zero' (N 0 0) (N 1 1) (N 0 2) (N 2 0) t00 t11 c0 h20 ?_, h12⟩
    rw [h12] at e00
    linear_combination e00
  · exact ⟨col_zero _ _ _ _ _ t00 t11 t01 c0 h21 e01,
      col_zero (N 1 1) (N 1 0) (N 0 0) (N 1 2) (N 2 0) t11 t00 t10 c1 h20
        (by linear_combination e10)⟩

theorem mat_col (hnc : ¬ SubConj F.E₁ F.E₂) {p : X} (hp : p ∈ Y.P) :
    A.mat ⟨p, Y.mem_NA hp⟩ 0 2 = 0 ∧ A.mat ⟨p, Y.mem_NA hp⟩ 1 2 = 0 := by
  rcases Y.top_cases hnc hp with h | h
  · exact Y.col_of_top hnc hp h
  · have hpu : p * A.D₁.u ∈ Y.P := mul_mem hp Y.u_mem
    have htop : top (redM (A.mat ⟨p * A.D₁.u, Y.mem_NA hpu⟩)) = 1 := by
      obtain ⟨c0, c1, -⟩ := A.redM_col hnc ⟨p, Y.mem_NA hp⟩
      rw [show (⟨p * A.D₁.u, Y.mem_NA hpu⟩ : A.NA) = ⟨p, Y.mem_NA hp⟩ * ⟨A.D₁.u, A.u_mem_NA⟩
        from rfl, A.mat_mul, A.mat_u, redM_mul, GapNH.redM_Umat, top_mul c0 c1, h, top_Ub]
      decide
    obtain ⟨h0, h1⟩ := Y.col_of_top hnc hpu htop
    have e : A.mat ⟨p, Y.mem_NA hp⟩ = A.mat ⟨p * A.D₁.u, Y.mem_NA hpu⟩ * Umat := by
      rw [show (⟨p * A.D₁.u, Y.mem_NA hpu⟩ : A.NA) = ⟨p, Y.mem_NA hp⟩ * ⟨A.D₁.u, A.u_mem_NA⟩
        from rfl, A.mat_mul, A.mat_u, mul_assoc, Umat_sq, mul_one]
    rw [e]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    simp [Umat, h0, h1]

theorem conj_c (hnc : ¬ SubConj F.E₁ F.E₂) {p : X} (hp : p ∈ Y.P) :
    p * A.Φ ![0, 0, 1] * p⁻¹ = A.Φ ![0, 0, 1] ∨
      p * A.Φ ![0, 0, 1] * p⁻¹ = (A.Φ ![0, 0, 1])⁻¹ := by
  obtain ⟨h0, h1⟩ := Y.mat_col hnc hp
  obtain ⟨-, -, c2⟩ := A.redM_col hnc ⟨p, Y.mem_NA hp⟩
  have e : A.mat ⟨p, Y.mem_NA hp⟩ *ᵥ ![0, 0, 1] = ![0, 0, A.mat ⟨p, Y.mem_NA hp⟩ 2 2] := by
    funext i
    rw [col_mulVec, mul_one]
    fin_cases i
    · exact h0
    · exact h1
    · rfl
  rw [show p * A.Φ ![0, 0, 1] * p⁻¹ = A.Φ (A.mat ⟨p, Y.mem_NA hp⟩ *ᵥ ![0, 0, 1]) from
    A.conj_Φ ⟨p, Y.mem_NA hp⟩ _, e, ← A.Φ_neg]
  generalize A.mat ⟨p, Y.mem_NA hp⟩ 2 2 = m at c2 ⊢
  have : m = 1 ∨ m = -1 := by revert m; decide
  rcases this with rfl | rfl
  · left; rfl
  · right; congr 1; funext i; fin_cases i <;> simp

theorem conj_z (hnc : ¬ SubConj F.E₁ F.E₂) {p : X} (hp : p ∈ Y.P) :
    p * S.z * p⁻¹ = S.z ∨ p * S.z * p⁻¹ = S.z * F.kF := by
  set N := A.mat ⟨p, Y.mem_NA hp⟩ with hN
  obtain ⟨h00, h10⟩ : r2 (N 0 0) = 1 ∧ r2 (N 1 0) = 0 := by
    rcases Y.top_cases hnc hp with h | h
    · exact ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 1) 0⟩
    · exact ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 1) 0⟩
  have e : N *ᵥ ![2, 0, 0] = ![N 0 0 * 2, N 1 0 * 2, N 2 0 * 2] := by
    funext i
    rw [col_mulVec₀]
    fin_cases i <;> rfl
  have h1 : N 0 0 * 2 = 2 := by
    generalize N 0 0 = m at h00
    revert m
    decide
  have h2 : N 1 0 * 2 = 0 := by
    generalize N 1 0 = m at h10
    revert m
    decide
  rw [← A.Φ_z, show p * A.Φ ![2, 0, 0] * p⁻¹ = A.Φ (N *ᵥ ![2, 0, 0]) from
    A.conj_Φ ⟨p, Y.mem_NA hp⟩ _, e, h1, h2]
  rcases (show ∀ m : ZMod 4, m * 2 = 0 ∨ m * 2 = 2 by decide) (N 2 0) with h | h <;> rw [h]
  · left; rfl
  · right
    rw [← A.Φ_k, ← A.Φ_add]
    congr 1
    decide

end BData.Syl

end Sec8

end CFSG.ComponentClassification.HSFLit
