module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightPlus
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMinus

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix CFSG.CGT.PushingUpLit.CGT6.TwoEight

theorem omegaPlusAct_faithful {n : ℕ}
    {g : SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n)}
    (h : ∀ m, omegaPlusAct n g m = m) : g = 1 := by
  apply plusHom_injective n
  rw [map_one]
  ext w : 1
  obtain ⟨m, rfl⟩ := (plusCoord n).surjective w
  rw [plusHom_apply]
  have h2 : plusMat n g m = m := Multiplicative.ofAdd.injective (h (Multiplicative.ofAdd m))
  rw [h2]
  rfl

theorem omegaPlusAct_fixed {n : ℕ} {m : Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))}
    (h : ∀ g, omegaPlusAct n g m = m) : m = 1 := by
  let U : SpecialLinearGroup (Fin 2) (Fq n) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let L : SpecialLinearGroup (Fin 2) (Fq n) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hU := congrArg Multiplicative.toAdd (h (U, 1))
  have hL := congrArg Multiplicative.toAdd (h (L, 1))
  have h1 : ∀ j, (Multiplicative.toAdd m) 1 j = 0 := by
    intro j
    have := congrFun (congrFun hU 0) j
    simp only [omegaPlusAct, Matrix.mul_apply, Fin.sum_univ_two, toAdd_ofAdd] at this
    fin_cases j <;> simp [U] at this ⊢ <;> linear_combination this
  have h0 : ∀ j, (Multiplicative.toAdd m) 0 j = 0 := by
    intro j
    have := congrFun (congrFun hL 1) j
    simp only [omegaPlusAct, Matrix.mul_apply, Fin.sum_univ_two, toAdd_ofAdd] at this
    fin_cases j <;> simp [L] at this ⊢ <;> linear_combination this
  apply Multiplicative.toAdd.injective
  ext i j
  fin_cases i
  · exact h0 j
  · exact h1 j

theorem omegaMinusAct_faithful {n : ℕ} [NeZero n] {A : SpecialLinearGroup (Fin 2) (Fq (2 * n))}
    (h : ∀ m, omegaMinusAct n A m = m) : A = 1 := by
  apply minusHom_injective n
  rw [map_one]
  ext w : 1
  obtain ⟨M, rfl⟩ := (minusCoord n).surjective w
  rw [minusHom_apply]
  have h2 := congrArg (fun z : Multiplicative (hermSub n) => (Multiplicative.toAdd z).1)
    (h (Multiplicative.ofAdd M))
  rw [omegaMinusAct_eq] at h2
  have h3 : (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * M.1 *
      cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) = M.1 := h2
  have : (⟨(A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * M.1 *
      cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))), herm_act_mem n A M⟩ : hermSub n) = M :=
    Subtype.ext h3
  rw [this]
  rfl

theorem omegaMinusAct_fixed {n : ℕ} [NeZero n] {m : Multiplicative (hermSub n)}
    (h : ∀ A, omegaMinusAct n A m = m) : m = 1 := by
  let M : hermSub n := Multiplicative.toAdd m
  have hfix : ∀ A : SpecialLinearGroup (Fin 2) (Fq (2 * n)),
      (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * M.1 *
        cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) = M.1 := by
    intro A
    have h2 := congrArg (fun z : Multiplicative (hermSub n) => (Multiplicative.toAdd z).1) (h A)
    rw [omegaMinusAct_eq] at h2
    exact h2
  have hM10 : M.1 1 0 = sigR n (M.1 0 1) := M.2 1 0
  let U : ∀ t : Fq (2 * n), SpecialLinearGroup (Fin 2) (Fq (2 * n)) := fun t =>
    ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
  let L : ∀ t : Fq (2 * n), SpecialLinearGroup (Fin 2) (Fq (2 * n)) := fun t =>
    ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩
  have hU : ∀ t, ∀ i j, ((U t : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * M.1 *
      cstar n (U t : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) i j = M.1 i j := fun t i j => by
    rw [hfix (U t)]
  have hL : ∀ t, ∀ i j, ((L t : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * M.1 *
      cstar n (L t : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) i j = M.1 i j := fun t i j => by
    rw [hfix (L t)]
  have h11 : M.1 1 1 = 0 := by
    have := hU 1 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, cstar_apply] at this
    simp [U] at this
    linear_combination this
  have h00 : M.1 0 0 = 0 := by
    have := hL 1 1 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, cstar_apply] at this
    simp [L] at this
    linear_combination this
  have h01 : M.1 0 1 = 0 := by
    have hall : ∀ t : Fq (2 * n), t * sigR n (M.1 0 1) + M.1 0 1 * sigR n t = 0 := by
      intro t
      have := hU t 0 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, cstar_apply] at this
      simp [U, h00, h11, hM10] at this
      linear_combination this
    obtain ⟨w, hw⟩ := exists_sigR_ne n
    have h1 := hall 1
    have h2 := hall w
    simp only [one_mul, map_one, mul_one] at h1
    have hs : sigR n (M.1 0 1) = M.1 0 1 := by
      have : sigR n (M.1 0 1) = -M.1 0 1 := by linear_combination h1
      rw [this, CharTwo.neg_eq]
    rw [hs] at h2
    have hw' : w + sigR n w ≠ 0 := fun hh => hw (by
      have : sigR n w = -w := by linear_combination hh
      rw [this, CharTwo.neg_eq])
    have : M.1 0 1 * (w + sigR n w) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hw'
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · show M.1 1 0 = 0
    rw [hM10, h01, map_zero]
  · exact h11

end CFSG.CGT.PushingUpLit.CGT6
