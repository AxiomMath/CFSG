module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Frame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.Orth15
  QuadraticMap
open scoped MatrixGroups

section Frame

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_mul_of_commute_La (h2 : (2 : F) ≠ 0) (fr : Frame Q) {a : V ≃ₗ[F] V}
    (hLa : ∀ A : SL(2, F), a * fr.La A = fr.La A * a) :
    ∃ h : Matrix (Fin 2) (Fin 2) F, ∀ X, a (fr.incl X) = fr.incl (X * h) := by
  have hz : ∀ x, a (fr.La (-1) x) = fr.La (-1) (a x) := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) (hLa (-1))
    simpa using this
  have hspan : ∀ x ∈ fr.span, a x ∈ fr.span := by
    intro x hx
    obtain ⟨hdec, hr⟩ := decomp_span_perp fr (a x)
    set s := fr.incl (fr.coords (a x)) with hs
    set r := a x - s with hr'
    have h1 : fr.La (-1) (a x) = -(a x) := by
      rw [← hz, La_neg_one_of_mem_span fr hx, map_neg]
    have h2' : fr.La (-1) (a x) = -s + r := by
      conv_lhs => rw [hdec]
      rw [map_add, La_neg_one_of_mem_span fr ⟨_, rfl⟩, La_neg_one_of_mem_perp fr hr]
    have h3 : r = 0 := by
      have : r + r = 0 := by
        have e : -(a x) = -s + r := h1.symm.trans h2'
        have e2 : a x = s + r := by rw [hr']; abel
        rw [e2] at e
        have e3 : -(s + r) = -s - r := by abel
        rw [e3] at e
        have : r + r = (-s + r) - (-s - r) := by abel
        rw [this, e]; abel
      have h4 : (2 : F) • r = 0 := by rw [two_smul]; exact this
      exact (smul_eq_zero.mp h4).resolve_left h2
    rw [hdec, h3, add_zero]
    exact ⟨_, rfl⟩
  let T : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F :=
    fr.coords ∘ₗ (a : V →ₗ[F] V) ∘ₗ fr.incl
  have hT : ∀ X, a (fr.incl X) = fr.incl (T X) := by
    intro X
    exact (Frame.mem_span_iff fr).mp (hspan _ ⟨X, rfl⟩)
  have hinj : ∀ X Y, fr.incl X = fr.incl Y → X = Y := fun X Y h => by
    have := congrArg fr.coords h
    rwa [Frame.coords_incl, Frame.coords_incl] at this
  have hL : ∀ (A : SL(2, F)) X, T ((A : Matrix (Fin 2) (Fin 2) F) * X) =
      (A : Matrix (Fin 2) (Fin 2) F) * T X := by
    intro A X
    apply hinj
    have h := congrArg (fun g : V ≃ₗ[F] V => g (fr.incl X)) (hLa A)
    simp only [LinearEquiv.mul_apply] at h
    rw [Frame.La_apply_incl, hT, hT, Frame.La_apply_incl] at h
    exact h
  have e12 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1 + !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e21 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) = 1 + !![0, 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hL₁ : ∀ X, T (!![0, 1; 0, 0] * X) = !![0, 1; 0, 0] * T X := by
    intro X
    have h := hL (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1) X
    rw [Frame.coe_transvection_zero_one, e12, add_mul, add_mul, one_mul, one_mul, map_add] at h
    exact add_left_cancel h
  have hL₂ : ∀ X, T (!![0, 0; 1, 0] * X) = !![0, 0; 1, 0] * T X := by
    intro X
    have h := hL (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1) X
    rw [Frame.coe_transvection_one_zero, e21, add_mul, add_mul, one_mul, one_mul, map_add] at h
    exact add_left_cancel h
  set C := T 1 with hC
  have hdec : ∀ X : Matrix (Fin 2) (Fin 2) F, X = X 0 0 • !![1, 0; 0, 0] + X 0 1 • !![0, 1; 0, 0] +
      X 1 0 • !![0, 0; 1, 0] + X 1 1 • !![0, 0; 0, 1] := by
    intro X
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have t12 : T !![0, 1; 0, 0] = !![0, 1; 0, 0] * C := by
    have := hL₁ 1
    rwa [mul_one] at this
  have t21 : T !![0, 0; 1, 0] = !![0, 0; 1, 0] * C := by
    have := hL₂ 1
    rwa [mul_one] at this
  have t11 : T !![1, 0; 0, 0] = !![1, 0; 0, 0] * C := by
    have e : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 0, 0] * !![0, 0; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, hL₁, t21, ← mul_assoc]
  have t22 : T !![0, 0; 0, 1] = !![0, 0; 0, 1] * C := by
    have e : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![0, 0; 1, 0] * !![0, 1; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, hL₂, t12, ← mul_assoc]
  have hTX : ∀ X, T X = X * C := by
    intro X
    conv_lhs => rw [hdec X]
    simp only [map_add, map_smul, t11, t12, t21, t22]
    conv_rhs => rw [hdec X]
    simp only [add_mul, smul_mul_assoc]
  exact ⟨C, fun X => by rw [hT, hTX]⟩

end Frame

end CFSG.ClassicalInvolution.Q3.Q3MFOD
