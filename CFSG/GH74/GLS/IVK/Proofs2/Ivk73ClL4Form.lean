module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowSData

public section

namespace CFSG.GH74.GLS.IVK

open CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag

section VForm

variable {k E : Type} [Field k] [CommRing E] [Algebra k E]

theorem rowSForm_vanishes (h2 : (2 : k) ≠ 0)
    (F : (Fin 2 → E) →ₗ[k] (Fin 2 → E) →ₗ[k] k)
    (hsymm : ∀ u v, F u v = F v u)
    (h12 : ∀ (x : E) (u v : Fin 2 → E),
      F ![x * u 1, 0] v + F u ![x * v 1, 0] = 0)
    (h21 : ∀ (x : E) (u v : Fin 2 → E),
      F ![0, x * u 0] v + F u ![0, x * v 0] = 0) :
    F = 0 := by
  have hz : (![0, 0] : Fin 2 → E) = 0 := by
    ext i
    fin_cases i <;> simp
  have hΦ : ∀ x y z : E, F ![x * y, 0] ![0, z] + F ![x * z, 0] ![0, y] = 0 := by
    intro x y z
    have := h12 x ![0, y] ![0, z]
    simpa [hsymm ![0, y] ![x * z, 0]] using this
  have hskew : ∀ y z : E, F ![y, 0] ![0, z] + F ![z, 0] ![0, y] = 0 := by
    intro y z
    simpa using hΦ 1 y z
  have hcomm : ∀ x z : E, F ![x, 0] ![0, z] = F ![1, 0] ![0, x * z] := by
    intro x z
    have h1 := hΦ x 1 z
    have h2' := hskew (x * z) 1
    simp only [mul_one] at h1
    linear_combination h1 - h2'
  have hzero : ∀ a b : E, F ![a, 0] ![0, b] = 0 := by
    intro a b
    have h1 := hskew a b
    rw [hcomm a b, hcomm b a, mul_comm b a] at h1
    have h3 : (2 : k) * F ![1, 0] ![0, a * b] = 0 := by linear_combination h1
    have h4 := (mul_eq_zero.mp h3).resolve_left h2
    rw [hcomm a b, h4]
  have h11 : ∀ a b : E, F ![a, 0] ![b, 0] = 0 := by
    intro a b
    have := h12 1 ![0, a] ![b, 0]
    simpa [hz] using this
  have h22 : ∀ a b : E, F ![0, a] ![0, b] = 0 := by
    intro a b
    have := h21 1 ![a, 0] ![0, b]
    simpa [hz] using this
  have h21' : ∀ a b : E, F ![0, a] ![b, 0] = 0 := by
    intro a b
    rw [hsymm]
    exact hzero b a
  have hdecomp : ∀ u : Fin 2 → E, u = ![u 0, 0] + ![0, u 1] := by
    intro u
    ext i
    fin_cases i <;> simp
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply, hdecomp u, hdecomp v]
  simp only [map_add, LinearMap.add_apply, h11, h22, h21', hzero, add_zero]

end VForm

section MatrixStep

variable {k : Type} [Field k]

theorem rowSForm_matrix_relation (h2 : (2 : k) ≠ 0)
    (B G : GL (Fin 4) k) (N : Matrix (Fin 4) (Fin 4) k)
    (hG : (G : Matrix (Fin 4) (Fin 4) k) = 1 + N) (hNN : N * N = 0) (c : kˣ)
    (h : B * (GeneralLinearGroup.inverseTranspose : MulAut (GL (Fin 4) k)) G * B⁻¹ =
        GeneralLinearGroup.scalar (Fin 4) c * G) :
    Nᵀ * ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) +
      ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) * N = 0 := by
  have hBM : (B : Matrix (Fin 4) (Fin 4) k) * ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) =
      1 := B.mul_inv
  have hMB : ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) * (B : Matrix (Fin 4) (Fin 4) k) =
      1 := B.inv_mul
  have hGinv : ((G⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) = 1 - N := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hG]
    calc (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
      _ = 1 := by rw [hNN, sub_zero]
  have hmat := congrArg (fun X : GL (Fin 4) k => (X : Matrix (Fin 4) (Fin 4) k)) h
  simp only [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, hGinv,
    GeneralLinearGroup.coe_scalar, hG, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_mul_assoc, one_mul] at hmat
  generalize ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) = M at hBM hMB hmat ⊢
  generalize (B : Matrix (Fin 4) (Fin 4) k) = B' at hBM hMB hmat
  have hnil : IsNilpotent N := ⟨2, by rw [pow_two]; exact hNN⟩
  have htrN : Matrix.trace N = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have htr := congrArg Matrix.trace hmat
  have hconj : ∀ X : Matrix (Fin 4) (Fin 4) k, Matrix.trace (B' * X * M) = Matrix.trace X := by
    intro X
    rw [Matrix.trace_mul_comm, ← mul_assoc, hMB, one_mul]
  rw [hconj, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_transpose, htrN,
    Matrix.trace_one] at htr
  have h4 : (4 : k) ≠ 0 := by
    have h22 : (4 : k) = 2 * 2 := by norm_num
    rw [h22]
    exact mul_ne_zero h2 h2
  have hc : (c : k) = 1 := by
    have h5 : (c : k) * 4 = 1 * 4 := by
      simpa [eq_comm] using htr
    exact mul_right_cancel₀ h4 h5
  rw [hc, one_smul] at hmat
  have e1 : B' * Nᵀ * M = -N := by
    calc B' * Nᵀ * M = B' * M - B' * (1 - Nᵀ) * M := by noncomm_ring
      _ = 1 - (1 + N) := by rw [hBM, hmat]
      _ = -N := by abel
  calc Nᵀ * M + M * N = M * (B' * Nᵀ * M) + M * N := by
        rw [← mul_assoc, ← mul_assoc, hMB, one_mul]
    _ = 0 := by rw [e1, mul_neg]; abel

end MatrixStep

section Glue

variable {k : Type} [Field k] (ν : kˣ)
  (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 4 → k))

theorem rowSForm_infinitesimal (h2 : (2 : k) ≠ 0) (B : GL (Fin 4) k)
    (g : SpecialLinearGroup (Fin 2) (extension (ν : k)))
    (n : (Fin 2 → extension (ν : k)) → (Fin 2 → extension (ν : k)))
    (hn : ∀ v, (g : Matrix (Fin 2) (Fin 2) (extension (ν : k))) *ᵥ v = v + n v)
    (hnn : ∀ v, n (n v) = 0)
    (hg : ∃ c : kˣ, B * (GeneralLinearGroup.inverseTranspose : MulAut (GL (Fin 4) k))
          (rowSPi ν Ψ (SpecialLinearGroup.toGL g)) * B⁻¹ =
        GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g))
    (u v : Fin 2 → extension (ν : k)) :
    Ψ (n u) ⬝ᵥ (((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ Ψ v) +
      Ψ u ⬝ᵥ (((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ Ψ (n v)) = 0 := by
  obtain ⟨c, hc⟩ := hg
  set G := rowSPi ν Ψ (SpecialLinearGroup.toGL g) with hGdef
  set Nm : Matrix (Fin 4) (Fin 4) k := (G : Matrix (Fin 4) (Fin 4) k) - 1 with hNm
  have hNvec : ∀ w, Nm *ᵥ w = Ψ (n (Ψ.symm w)) := by
    intro w
    rw [hNm, Matrix.sub_mulVec, Matrix.one_mulVec, hGdef, rowSPi_mulVec,
      SpecialLinearGroup.coe_GL_coe_matrix, hn, map_add, LinearEquiv.apply_symm_apply]
    abel
  have hNN : Nm * Nm = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro w
    rw [← Matrix.mulVec_mulVec, hNvec, hNvec, LinearEquiv.symm_apply_apply, hnn, map_zero,
      Matrix.zero_mulVec]
  have hrel := rowSForm_matrix_relation h2 B G Nm (by rw [hNm]; abel) hNN c hc
  have key := congrArg (fun X : Matrix (Fin 4) (Fin 4) k => (Ψ u) ⬝ᵥ (X *ᵥ Ψ v)) hrel
  simp only [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, Matrix.zero_mulVec,
    dotProduct_zero] at key
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hNvec, hNvec,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at key
  exact key

theorem rowS_no_symmetric_invariant (hν : ¬ IsSquare (ν : k)) (h2 : (2 : k) ≠ 0)
    (B : GL (Fin 4) k) (hBs : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = (B : Matrix (Fin 4) (Fin 4) k))
    (hB : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)), ∃ c : kˣ,
      B * (GeneralLinearGroup.inverseTranspose : MulAut (GL (Fin 4) k))
          (rowSPi ν Ψ (SpecialLinearGroup.toGL g)) * B⁻¹ =
        GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g)) :
    False := by
  have _ := hν
  classical
  set M : Matrix (Fin 4) (Fin 4) k := ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) with hM
  have hMB : M * (B : Matrix (Fin 4) (Fin 4) k) = 1 := B.inv_mul
  have hMt : Mᵀ = M := by
    have h1 : (B : Matrix (Fin 4) (Fin 4) k) * Mᵀ = 1 := by
      have := congrArg Matrix.transpose hMB
      rwa [Matrix.transpose_mul, hBs, Matrix.transpose_one] at this
    calc Mᵀ = (M * (B : Matrix (Fin 4) (Fin 4) k)) * Mᵀ := by rw [hMB, one_mul]
      _ = M * ((B : Matrix (Fin 4) (Fin 4) k) * Mᵀ) := by rw [mul_assoc]
      _ = M := by rw [h1, mul_one]
  let F : (Fin 2 → extension (ν : k)) →ₗ[k] (Fin 2 → extension (ν : k)) →ₗ[k] k :=
    (Matrix.toLinearMap₂' k M).compl₁₂ (Ψ : (Fin 2 → extension (ν : k)) →ₗ[k] (Fin 4 → k))
      (Ψ : (Fin 2 → extension (ν : k)) →ₗ[k] (Fin 4 → k))
  have hF : ∀ u v, F u v = Ψ u ⬝ᵥ (M *ᵥ Ψ v) := fun u v => by
    simp only [F, LinearMap.compl₁₂_apply, Matrix.toLinearMap₂'_apply']
    rfl
  have hsymm : ∀ u v, F u v = F v u := by
    intro u v
    rw [hF, hF, Matrix.dotProduct_mulVec, dotProduct_comm]
    conv_lhs => rw [← hMt, Matrix.vecMul_transpose]
  have h12 : ∀ (x : extension (ν : k)) (u v : Fin 2 → extension (ν : k)),
      F ![x * u 1, 0] v + F u ![x * v 1, 0] = 0 := by
    intro x u v
    obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin 2) (extension (ν : k)),
        ∀ v, (g : Matrix (Fin 2) (Fin 2) (extension (ν : k))) *ᵥ v = v + ![x * v 1, 0] :=
      ⟨⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩, fun v => by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]⟩
    have := rowSForm_infinitesimal ν Ψ h2 B g (fun v => ![x * v 1, 0]) hg
      (fun v => by
        ext i
        fin_cases i <;> simp) (hB g) u v
    rw [hF, hF]
    exact this
  have h21 : ∀ (x : extension (ν : k)) (u v : Fin 2 → extension (ν : k)),
      F ![0, x * u 0] v + F u ![0, x * v 0] = 0 := by
    intro x u v
    obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin 2) (extension (ν : k)),
        ∀ v, (g : Matrix (Fin 2) (Fin 2) (extension (ν : k))) *ᵥ v = v + ![0, x * v 0] :=
      ⟨⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩, fun v => by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm]⟩
    have := rowSForm_infinitesimal ν Ψ h2 B g (fun v => ![0, x * v 0]) hg
      (fun v => by
        ext i
        fin_cases i <;> simp) (hB g) u v
    rw [hF, hF]
    exact this
  have hF0 := rowSForm_vanishes h2 F hsymm h12 h21
  have hM0 : M = 0 := by
    ext i j
    have h1 : F (Ψ.symm (Pi.single i 1)) (Ψ.symm (Pi.single j 1)) = M i j := by
      rw [hF, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      simp
    rw [← h1, hF0]
    rfl
  rw [hM0, zero_mul] at hMB
  have := congrFun (congrFun hMB 0) 0
  simp at this

end Glue

end CFSG.GH74.GLS.IVK
