module

public import CFSG.LieType.Universal.Spin.Chevalley.Frame
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {Q : QuadraticForm K (σ → K)} {n : ℕ}

variable (Q) in
noncomputable def spinMat : spinGroup Q →* Matrix σ σ K :=
  (Units.coeHom (Matrix σ σ K)).comp (spinMatrix Q)

theorem spinMat_apply (x : spinGroup Q) (a b : σ) :
    spinMat Q x a b = spinAction Q x (Pi.single b 1) a := by
  change (spinMatrix Q x : Matrix σ σ K) a b = _
  rw [coe_spinMatrix, LinearMap.toMatrix'_apply]
  rfl

theorem spinAction_eq_one_of_spinMat_eq_one {x : spinGroup Q} (h : spinMat Q x = 1) :
    spinAction Q x = 1 := by
  refine LinearEquiv.ext fun v => ?_
  change spinAction Q x v = v
  rw [← spinMatrix_mulVec]
  change Matrix.mulVec (spinMat Q x) v = v
  rw [h, Matrix.one_mulVec]

theorem spinMat_apply_of_eq_smul {x : spinGroup Q} {b : σ} {e : K}
    (h : spinAction Q x (Pi.single b 1) = e • Pi.single b 1) (a : σ) :
    spinMat Q x a b = if a = b then e else 0 := by
  rw [spinMat_apply, h]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab]

theorem isDiag_spinMat {x : spinGroup Q}
    (h : ∀ b : σ, ∃ e : K, spinAction Q x (Pi.single b 1) = e • Pi.single b 1) :
    (spinMat Q x).IsDiag := by
  intro a b hab
  obtain ⟨e, he⟩ := h b
  rw [spinMat_apply_of_eq_smul he, ite_eq_right hab]

structure HypFrame.IsCoord (F : HypFrame Q n) (idx : Fin n → Bool → σ) : Prop where
  idx_inj : ∀ {m r m' r'}, idx m r = idx m' r' → m = m' ∧ r = r'
  vec_eq : ∀ m r, F.vec m r = Pi.single (idx m r) 1
  polar_vec : ∀ (v : σ → K) m r, polar Q v (F.vec m r) = v (idx m (!r))

structure OddFrame.IsCoord (F : OddFrame Q n) (idx : Fin n → Bool → σ) (zi : σ) : Prop
    extends F.toHypFrame.IsCoord idx where
  idx_ne : ∀ m r, idx m r ≠ zi
  z_eq : F.z = Pi.single zi 1
  polar_z : ∀ v : σ → K, polar Q v F.z = 2 * v zi

omit [Fintype σ] in
private theorem mul_single_mul_single (c : K) (a b p q : σ) :
    c * (Pi.single b (1 : K) : σ → K) q * (Pi.single p (1 : K) : σ → K) a =
      if a = p ∧ b = q then c else 0 := by
  rcases eq_or_ne a p with h1 | h1 <;> rcases eq_or_ne b q with h2 | h2
  · simp [h1, h2]
  · simp [h1, h2, h2.symm]
  · simp [h1, h2]
  · simp [h1, h2, h2.symm]

theorem HypFrame.IsCoord.spinMat_longRoot {F : HypFrame Q n} {idx : Fin n → Bool → σ}
    (hF : F.IsCoord idx) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) (a b : σ) :
    spinMat Q (F.longRoot hij s t (.ofAdd c)) a b =
      (1 : Matrix σ σ K) a b + (if a = idx i s ∧ b = idx j (!t) then c else 0) -
        (if a = idx j t ∧ b = idx i (!s) then c else 0) := by
  rw [spinMat_apply, F.spinAction_longRoot, hF.polar_vec, hF.polar_vec, hF.vec_eq, hF.vec_eq]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_single_mul_single, mul_single_mul_single]
  simp only [Pi.single_apply, Matrix.one_apply]

theorem OddFrame.IsCoord.spinMat_shortRoot {F : OddFrame Q n} {idx : Fin n → Bool → σ} {zi : σ}
    (hF : F.IsCoord idx zi) (i : Fin n) (s : Bool) (c : K) (a b : σ) :
    spinMat Q (F.shortRoot i s (.ofAdd c)) a b =
      (1 : Matrix σ σ K) a b + (if a = zi ∧ b = idx i (!s) then c else 0) -
        (if a = idx i s ∧ b = zi then 2 * c else 0) -
        (if a = idx i s ∧ b = idx i (!s) then c ^ 2 else 0) := by
  rw [spinMat_apply, F.spinAction_shortRoot, hF.polar_vec, hF.polar_z, hF.vec_eq, hF.z_eq]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_single_mul_single, add_mul,
    show c * (2 * (Pi.single b (1 : K) : σ → K) zi) = 2 * c * (Pi.single b (1 : K) : σ → K) zi
      by ring,
    mul_single_mul_single, mul_single_mul_single]
  simp only [Pi.single_apply, Matrix.one_apply]
  ring

end CFSG.LieType.Universal.Spin
