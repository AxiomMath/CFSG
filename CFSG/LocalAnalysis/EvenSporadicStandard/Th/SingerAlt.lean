module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Singer
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap

public section

namespace CFSG.EvenSporadicStandard.ThStd

namespace SingerAlt

open Matrix

abbrev F2Vec4 : Type := Fin 4 → ZMod 2

@[expose] def pairFst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

@[expose] def pairSnd : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

@[expose] def ei (i : Fin 4) : F2Vec4 := fun k => if i = k then 1 else 0

@[expose] def wedge (x y : F2Vec4) : Fin 6 → ZMod 2 :=
  fun p => x (pairFst p) * y (pairSnd p) + x (pairSnd p) * y (pairFst p)

@[expose] def compound (S : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun a p => wedge (fun m => S m (pairFst p)) (fun m => S m (pairSnd p)) a

theorem zmod_two_cases' (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem neg_eq_self_f2Vec4 (v : F2Vec4) : -v = v := by
  funext m
  simp only [Pi.neg_apply]
  exact ZMod.neg_eq_self_mod_two _

theorem biadd_eq_mulVec (β : F2Vec4 → F2Vec4 → F2Vec4)
    (h₁ : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (h₂ : ∀ x y y', β x (y + y') = β x y + β x y') (hal : ∀ x, β x x = 0) (x y : F2Vec4) :
    β x y = (Matrix.of fun m p => β (ei (pairFst p)) (ei (pairSnd p)) m) *ᵥ wedge x y := by
  have hz1 : ∀ y, β 0 y = 0 := fun y => by
    have := h₁ 0 0 y
    simpa using this
  have hz2 : ∀ x, β x 0 = 0 := fun x => by
    have := h₂ x 0 0
    simpa using this
  have hs1 : ∀ (c : ZMod 2) x y, β (c • x) y = c • β x y := by
    intro c x y
    rcases zmod_two_cases' c with rfl | rfl <;> simp [hz1]
  have hs2 : ∀ (c : ZMod 2) x y, β x (c • y) = c • β x y := by
    intro c x y
    rcases zmod_two_cases' c with rfl | rfl <;> simp [hz2]
  let βL : F2Vec4 →ₗ[ZMod 2] F2Vec4 →ₗ[ZMod 2] F2Vec4 := LinearMap.mk₂ (ZMod 2) β h₁ hs1 h₂ hs2
  have key : β x y = ∑ j, ∑ i, (y j * x i) • β (ei i) (ei j) := by
    have hx : x = ∑ i, x i • ei i := pi_eq_sum_univ x
    have hy : y = ∑ i, y i • ei i := pi_eq_sum_univ y
    calc β x y = βL x y := rfl
      _ = βL (∑ i, x i • ei i) (∑ j, y j • ei j) := by
        rw [← hx, ← hy]
      _ = _ := by
        simp [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum,
          smul_smul, βL, LinearMap.mk₂_apply]
  have hsym : ∀ i j, β (ei j) (ei i) = β (ei i) (ei j) := by
    intro i j
    have h := hal (ei i + ei j)
    rw [h₁, h₂, h₂, hal, hal] at h
    simp only [zero_add, add_zero] at h
    rw [eq_neg_of_add_eq_zero_right h, neg_eq_self_f2Vec4]
  have hdiag : ∀ i, β (ei i) (ei i) = 0 := fun i => hal _
  funext m
  rw [key]
  simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdiag, Pi.zero_apply,
    mul_zero, add_zero, zero_add]
  rw [hsym 0 1, hsym 0 2, hsym 0 3, hsym 1 2, hsym 1 3, hsym 2 3]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, wedge, pairFst, pairSnd]
  ring

theorem eq_zero_of_equivariant (S : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (Y : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hS : S ^ 4 + S + 1 = 0)
    (hY : (compound S ^ 4 + compound S + 1) * Y = 1) (β : F2Vec4 → F2Vec4 → F2Vec4)
    (h₁ : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (h₂ : ∀ x y y', β x (y + y') = β x y + β x y') (hal : ∀ x, β x x = 0)
    (heq : ∀ x y, β (S *ᵥ x) (S *ᵥ y) = S *ᵥ β x y) : ∀ x y, β x y = 0 := by
  have hrep := biadd_eq_mulVec β h₁ h₂ hal
  set X : Matrix (Fin 4) (Fin 6) (ZMod 2) :=
    Matrix.of fun m p => β (ei (pairFst p)) (ei (pairSnd p)) m with hX
  have hmulei : ∀ k : Fin 4, S *ᵥ ei k = fun m => S m k := by
    intro k
    funext m
    simp [ei, Matrix.mulVec, dotProduct]
  have hXW : X * compound S = S * X := by
    ext m p
    have hcol : (fun q => compound S q p) =
        wedge (S *ᵥ ei (pairFst p)) (S *ᵥ ei (pairSnd p)) := by
      funext q
      rw [hmulei, hmulei]
      rfl
    calc (X * compound S) m p = (X *ᵥ fun q => compound S q p) m := by
          simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      _ = (X *ᵥ wedge (S *ᵥ ei (pairFst p)) (S *ᵥ ei (pairSnd p))) m := by rw [hcol]
      _ = β (S *ᵥ ei (pairFst p)) (S *ᵥ ei (pairSnd p)) m := by rw [← hrep]
      _ = (S *ᵥ β (ei (pairFst p)) (ei (pairSnd p))) m := by rw [heq]
      _ = (S * X) m p := by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
  have hpow : ∀ n : ℕ, X * compound S ^ n = S ^ n * X := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hXW, ← Matrix.mul_assoc, pow_succ]
  have hX0 : X * (compound S ^ 4 + compound S + 1) = 0 := by
    rw [Matrix.mul_add, Matrix.mul_add, hpow, Matrix.mul_one]
    rw [← pow_one (compound S), hpow 1]
    have h4 : S ^ 4 * X + S * X + X = (S ^ 4 + S + 1) * X := by
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
    rw [pow_one, h4, hS, Matrix.zero_mul]
  have hXzero : X = 0 := by
    calc X = X * 1 := (Matrix.mul_one X).symm
      _ = X * ((compound S ^ 4 + compound S + 1) * Y) := by rw [hY]
      _ = (X * (compound S ^ 4 + compound S + 1)) * Y := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [hX0, Matrix.zero_mul]
  intro x y
  rw [hrep x y, hXzero, Matrix.zero_mulVec]

@[expose] def Y14 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1;
    0, 0, 1, 1, 0, 0]

@[expose] def Y28 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 1, 0]

set_option maxRecDepth 100000 in
theorem singer_alt_eq_zero (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 8)
    (β : F2Vec4 → F2Vec4 → F2Vec4) (h₁ : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (h₂ : ∀ x y y', β x (y + y') = β x y + β x y') (hal : ∀ x, β x x = 0)
    (heq : ∀ x y, β ((singerMat ^ j) *ᵥ x) ((singerMat ^ j) *ᵥ y) = (singerMat ^ j) *ᵥ β x y) :
    ∀ x y, β x y = 0 := by
  rcases hj with rfl | rfl | rfl | rfl
  · exact eq_zero_of_equivariant _ Y14 (by decide) (by decide) β h₁ h₂ hal heq
  · exact eq_zero_of_equivariant _ Y28 (by decide) (by decide) β h₁ h₂ hal heq
  · exact eq_zero_of_equivariant _ Y14 (by decide) (by decide) β h₁ h₂ hal heq
  · exact eq_zero_of_equivariant _ Y28 (by decide) (by decide) β h₁ h₂ hal heq

end SingerAlt

end CFSG.EvenSporadicStandard.ThStd
