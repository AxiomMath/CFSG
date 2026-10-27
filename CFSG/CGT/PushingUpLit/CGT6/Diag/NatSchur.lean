module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Nat

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

theorem schur_vec (φ : (Fin 2 → F) → (Fin 2 → F)) (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hequiv : ∀ (s : SL(2, F)) (x : Fin 2 → F),
      φ ((s : Matrix (Fin 2) (Fin 2) F).mulVec x) = (s : Matrix (Fin 2) (Fin 2) F).mulVec (φ x)) :
    ∃ c : F, ∀ x, φ x = c • x := by
  have h0 : φ 0 = 0 := by simpa using hadd 0 0
  obtain ⟨c, hc⟩ : ∃ c : F, φ ![1, 0] = c • ![1, 0] := by
    refine ⟨φ ![1, 0] 0, ?_⟩
    have h := hequiv ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ ![1, 0]
    have hu : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = ![1, 0] := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp only [hu] at h
    have h1 : φ ![1, 0] 1 = 0 := by
      have := congrFun h 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      exact this
    ext i; fin_cases i
    · simp
    · simpa using h1
  have htrans : ∀ x : Fin 2 → F, x ≠ 0 →
      ∃ s : SL(2, F), (s : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = x := by
    intro x hx
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1; apply hx; ext i; fin_cases i <;> simp [h0, h1]
      refine ⟨⟨!![0, -(x 1)⁻¹; x 1, 0], ?_⟩, ?_⟩
      · simp [Matrix.det_fin_two, h1]
      · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
    · refine ⟨⟨!![x 0, 0; x 1, (x 0)⁻¹], ?_⟩, ?_⟩
      · simp [Matrix.det_fin_two, h0]
      · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨c, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp [h0]
  · obtain ⟨s, hs⟩ := htrans x hx
    rw [← hs, hequiv s, hc, Matrix.mulVec_smul]

theorem schur_proj (ψ : (Fin 2 → F) → Matrix (Fin 2) (Fin 2) F)
    (hadd : ∀ a b, ψ (a + b) = ψ a + ψ b)
    (hequiv : ∀ (s : SL(2, F)) a, ψ ((s : Matrix (Fin 2) (Fin 2) F).mulVec a) =
      (s : Matrix (Fin 2) (Fin 2) F) * ψ a) (k : Fin 2) :
    ∃ r : F, ∀ a i, ψ a i k = r * a i := by
  obtain ⟨c, hc⟩ := schur_vec (fun a i => ψ a i k) (by intro a b; ext i; simp [hadd])
    (by intro s a; ext i; simp [hequiv, Matrix.mul_apply, Matrix.mulVec, dotProduct])
  exact ⟨c, fun a i => by simpa using congrFun (hc a) i⟩

theorem schur_mat (Φ : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F)
    (hadd : ∀ M N, Φ (M + N) = Φ M + Φ N)
    (hequiv : ∀ (s : SL(2, F)) M, Φ ((s : Matrix (Fin 2) (Fin 2) F) * M) =
      (s : Matrix (Fin 2) (Fin 2) F) * Φ M) :
    ∀ M, Φ M = M * Φ 1 := by
  let L : (Fin 2 → F) → Matrix (Fin 2) (Fin 2) F := fun a => !![a 0, 0; a 1, 0]
  let R : (Fin 2 → F) → Matrix (Fin 2) (Fin 2) F := fun a => !![0, a 0; 0, a 1]
  have hL : ∀ (s : Matrix (Fin 2) (Fin 2) F) a, s * L a = L (s.mulVec a) := by
    intro s a; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hR : ∀ (s : Matrix (Fin 2) (Fin 2) F) a, s * R a = R (s.mulVec a) := by
    intro s a; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hLa : ∀ a b, L (a + b) = L a + L b := by
    intro a b; ext i j; fin_cases i <;> fin_cases j <;> simp [L]
  have hRa : ∀ a b, R (a + b) = R a + R b := by
    intro a b; ext i j; fin_cases i <;> fin_cases j <;> simp [R]
  obtain ⟨r00, h00⟩ := schur_proj (fun a => Φ (L a)) (fun a b => by simp [hLa, hadd])
    (fun s a => by simp [← hL, hequiv]) 0
  obtain ⟨r01, h01⟩ := schur_proj (fun a => Φ (L a)) (fun a b => by simp [hLa, hadd])
    (fun s a => by simp [← hL, hequiv]) 1
  obtain ⟨r10, h10⟩ := schur_proj (fun a => Φ (R a)) (fun a b => by simp [hRa, hadd])
    (fun s a => by simp [← hR, hequiv]) 0
  obtain ⟨r11, h11⟩ := schur_proj (fun a => Φ (R a)) (fun a b => by simp [hRa, hadd])
    (fun s a => by simp [← hR, hequiv]) 1
  have hdec : ∀ M : Matrix (Fin 2) (Fin 2) F,
      Φ M = Φ (L (fun i => M i 0)) + Φ (R (fun i => M i 1)) := by
    intro M
    rw [← hadd]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [L, R]
  intro M
  rw [hdec M, hdec 1]
  ext i k
  fin_cases k
  · simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, h00, h10]
    ring
  · simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
    ring

end CFSG.CGT.PushingUpLit.CGT6.Diag.Nat
