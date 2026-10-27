module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Eig

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix Polynomial

section FrameN

variable {K : Type} [Field K] {r n : ℕ} {ω : K}

theorem mulVec_pow_eigen_n {A : Matrix (Fin n) (Fin n) K} {v : Fin n → K} {κ : K}
    (h : A *ᵥ v = κ • v) (m : ℕ) : (A ^ m) *ᵥ v = κ ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]

theorem exists_eigenvector_pow_one (hn0 : 0 < n) (hr : 0 < r) (hω : IsPrimitiveRoot ω r)
    (x : Matrix (Fin n) (Fin n) K) (hx : x ^ r = 1) :
    ∃ (μ : K) (v : Fin n → K), v ≠ 0 ∧ x *ᵥ v = μ • v := by
  classical
  set s : Finset K := nthRootsFinset r (1 : K) with hs
  have hsne : s.Nonempty := ⟨1, by rw [hs, mem_nthRootsFinset hr]; exact one_pow r⟩
  have hxa := aeval_nodal_of_pow_eq_one hr hω hx
  have hsum : ∀ w : Fin n → K, w = ∑ ζ ∈ s, eigProj s x ζ *ᵥ w := by
    intro w
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ w) (sum_eigProj hsne x)
    simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at h
    exact h.symm
  by_contra hcon
  push Not at hcon
  have hz : ∀ ζ ∈ s, eigProj s x ζ *ᵥ (Pi.single ⟨0, hn0⟩ 1 : Fin n → K) = 0 := by
    intro ζ hζ
    by_contra hne
    apply hcon ζ _ hne
    rw [Matrix.mulVec_mulVec, eigProj_eigen hxa hζ, Matrix.smul_mulVec]
  have h0 := hsum (Pi.single ⟨0, hn0⟩ 1)
  rw [Finset.sum_eq_zero hz] at h0
  have := congrFun h0 ⟨0, hn0⟩
  simp at this

theorem heis_frame_r (hr : 1 < r) (ξ : K) (hξ : IsPrimitiveRoot ξ r)
    (x y : Matrix (Fin r) (Fin r) K) (hx : x ^ r = 1) (hyu : IsUnit y)
    (hxy : x * y = ξ • (y * x)) :
    ∃ (B : Matrix (Fin r) (Fin r) K) (lam : K), IsUnit B ∧ lam ≠ 0 ∧
      x * B = B * diagonal (fun i : Fin r => ξ ^ (i : ℕ) * lam) := by
  have hr0 : 0 < r := by omega
  obtain ⟨μ, v₀, hv₀, hxv₀⟩ := exists_eigenvector_pow_one hr0 hr0 hξ x hx
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have h1 := mulVec_pow_eigen_n hxv₀ r
    rw [hx, Matrix.one_mulVec, zero_pow hr0.ne', zero_smul] at h1
    exact hv₀ h1
  have hxyi : ∀ i : ℕ, x * y ^ i = ξ ^ i • (y ^ i * x) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc x * y ^ (i + 1) = (x * y ^ i) * y := by rw [pow_succ, ← mul_assoc]
        _ = (ξ ^ i • (y ^ i * x)) * y := by rw [ih]
        _ = ξ ^ i • (y ^ i * (x * y)) := by rw [smul_mul_assoc, mul_assoc]
        _ = ξ ^ i • (y ^ i * (ξ • (y * x))) := by rw [hxy]
        _ = ξ ^ (i + 1) • (y ^ (i + 1) * x) := by
          rw [mul_smul_comm, smul_smul, ← mul_assoc, ← pow_succ y i, ← pow_succ ξ i]
  have hyui : ∀ i : ℕ, IsUnit (y ^ i) := fun i => hyu.pow i
  let μs : Fin r → K := fun i => ξ ^ (i : ℕ) * μ
  let vs : Fin r → (Fin r → K) := fun i => (y ^ (i : ℕ)) *ᵥ v₀
  have hxv : ∀ i : Fin r, x *ᵥ vs i = μs i • vs i := by
    intro i
    show x *ᵥ ((y ^ (i : ℕ)) *ᵥ v₀) = (ξ ^ (i : ℕ) * μ) • ((y ^ (i : ℕ)) *ᵥ v₀)
    rw [mulVec_mulVec, hxyi, smul_mulVec, ← mulVec_mulVec, hxv₀, mulVec_smul, smul_smul]
  have hv0 : ∀ i : Fin r, vs i ≠ 0 := by
    intro i h
    apply hv₀
    exact (Matrix.mulVec_injective_iff_isUnit.mpr (hyui i)) (by rw [mulVec_zero]; exact h)
  have hμs : Function.Injective μs := by
    intro i j h
    have h' : ξ ^ (i : ℕ) = ξ ^ (j : ℕ) := mul_right_cancel₀ hμ0 h
    exact Fin.ext (hξ.pow_inj i.2 j.2 h')
  have hli : LinearIndependent K vs := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.mulVecLin x) μs hμs vs ?_
    intro i
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨by simpa using hxv i, hv0 i⟩
  set B : Matrix (Fin r) (Fin r) K := (Matrix.of vs).transpose with hB
  have hBu : IsUnit B := by
    have hcol : B.col = vs := by
      funext j i
      simp [hB, Matrix.col_apply]
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact hli
  refine ⟨B, μ, hBu, hμ0, ?_⟩
  ext i j
  have h1 := congrFun (hxv j) i
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
  simp only [hB, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [h1]
  simp [μs, mul_comm]

end FrameN

end CFSG.GH74.GLS.Stage2.OddAut
