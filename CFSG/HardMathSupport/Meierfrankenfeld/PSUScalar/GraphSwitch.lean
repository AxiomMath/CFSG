module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.KroneckerFixed
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Matrix Module CFSG.LieType.Universal.Unitary

theorem antidiag_mul_mul_antidiag {F : Type*} [Field F] {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    antidiag n * M * antidiag n = M.submatrix Fin.rev Fin.rev := by
  ext i j
  simp only [Matrix.mul_apply, antidiag, of_apply, submatrix_apply]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · rw [if_pos (Fin.rev_rev j).symm, mul_one, Finset.sum_eq_single (Fin.rev i)]
    · rw [if_pos rfl, one_mul]
    · intro a _ ha
      rw [if_neg ha, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    have hjb : j ≠ Fin.rev b := fun h => hb (by rw [h, Fin.rev_rev])
    rw [if_neg hjb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem inv_transpose_eq_submatrix_rev_of_mem_SU {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}
    {A : GL (Fin n) F} (hA : A ∈ SU σ n) :
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ =
      ((A : Matrix (Fin n) (Fin n) F).map σ).submatrix Fin.rev Fin.rev := by
  set J : Matrix (Fin n) (Fin n) F := antidiag n with hJ
  set M : Matrix (Fin n) (Fin n) F := (A : Matrix (Fin n) (Fin n) F) with hM
  set N : Matrix (Fin n) (Fin n) F := ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hN
  have hJJ : J * J = 1 := antidiag_mul_self n
  have hJt : Jᵀ = J := by
    ext i j
    simp only [hJ, antidiag, transpose_apply, of_apply]
    by_cases h : j = Fin.rev i
    · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
    · rw [if_neg h, if_neg (fun h' => h (by rw [h', Fin.rev_rev]))]
  have hMN : M * N = 1 := by
    rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (M.map σ)ᵀ * J * M = J := (mem_SU.mp hA).2
  have h2 : (M.map σ)ᵀ = J * N * J := by
    calc (M.map σ)ᵀ = (M.map σ)ᵀ * J * (M * N) * J := by
          rw [hMN, Matrix.mul_one, Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = ((M.map σ)ᵀ * J * M) * N * J := by simp only [Matrix.mul_assoc]
      _ = J * N * J := by rw [h1]
  have h3 : M.map σ = J * Nᵀ * J := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul, hJt,
      ← Matrix.mul_assoc] at this
  have h4 : Nᵀ = J * M.map σ * J := by
    rw [h3]
    calc Nᵀ = (J * J) * Nᵀ * (J * J) := by rw [hJJ, Matrix.one_mul, Matrix.mul_one]
      _ = J * (J * Nᵀ * J) * J := by simp only [Matrix.mul_assoc]
  rw [h4, hJ, antidiag_mul_mul_antidiag]

theorem finrank_matFix_submatrix {k I I' : Type*} [Field k] [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] {r : ℕ} (e : I ≃ I') (T : Fin r → Matrix I' I' k) :
    finrank k (matFix fun i => (T i).submatrix e e) = finrank k (matFix T) := by
  let L : (I' → k) ≃ₗ[k] (I → k) := LinearEquiv.funCongrLeft k k e
  have hL : ∀ v : I' → k, L v = v ∘ e := fun _ => rfl
  have hmap : (matFix T).map (L : (I' → k) →ₗ[k] (I → k)) =
      matFix fun i => (T i).submatrix e e := by
    ext w
    rw [Submodule.mem_map, mem_matFix]
    have hcomp : ∀ u : I' → k, (u ∘ e) ∘ e.symm = u := fun u => funext fun b => by simp
    constructor
    · rintro ⟨v, hv, rfl⟩ i
      rw [LinearEquiv.coe_coe, hL, submatrix_mulVec_equiv, hcomp, (mem_matFix T v).mp hv i]
    · intro h
      refine ⟨w ∘ e.symm, (mem_matFix T _).mpr fun i => ?_, ?_⟩
      · have h' := h i
        rw [submatrix_mulVec_equiv] at h'
        funext b
        have := congrFun h' (e.symm b)
        simpa using this
      · rw [LinearEquiv.coe_coe, hL]
        funext a
        simp
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem finrank_matFix_inv_transpose_map_of_mem_SU {K k : Type*} [Field K] [Field k]
    {σ : K ≃+* K} {n r : ℕ} (φ : K →+* k) (g : Fin r → GL (Fin n) K)
    (hg : ∀ i, g i ∈ SU σ n) :
    finrank k (matFix fun i =>
        ((((g i)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) =
      finrank K (matFix fun i => ((g i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have h : (fun i => ((((g i)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) =
      fun i => (((g i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map
        (φ.comp σ.toRingHom)).submatrix Fin.revPerm Fin.revPerm := by
    funext i
    rw [inv_transpose_eq_submatrix_rev_of_mem_SU (hg i), Matrix.submatrix_map, Matrix.map_map]
    rfl
  rw [h, finrank_matFix_submatrix Fin.revPerm, finrank_matFix_map]

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
