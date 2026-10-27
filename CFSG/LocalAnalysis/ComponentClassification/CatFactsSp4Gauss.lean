module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Kron

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher

variable {K : Type} [Field K]

abbrev Gauss (K : Type) [Field K] : Type := QuadraticAlgebra K (-1) 0

theorem J₁_mul_J₁ : (J₁ : Matrix (Fin 2) (Fin 2) K) * J₁ = (-1 : K) • 1 + (0 : K) • J₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁]

@[expose] def gaussEmb : Gauss K →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  QuadraticAlgebra.lift ⟨J₁, J₁_mul_J₁⟩

theorem gaussEmb_apply (z : Gauss K) :
    gaussEmb z = z.re • (1 : Matrix (Fin 2) (Fin 2) K) + z.im • J₁ :=
  rfl

theorem gaussEmb_eq (z : Gauss K) : gaussEmb z = !![z.re, z.im; -z.im, z.re] := by
  rw [gaussEmb_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁]

theorem gaussEmb_injective : Function.Injective (gaussEmb (K := K)) := by
  intro z w h
  rw [gaussEmb_eq, gaussEmb_eq] at h
  have h1 := congrFun (congrFun h 0) 0
  have h2 := congrFun (congrFun h 0) 1
  simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one]
    at h1 h2
  exact QuadraticAlgebra.ext h1 h2

theorem gaussEmb_star (z : Gauss K) : gaussEmb (star z) = (gaussEmb z)ᵀ := by
  rw [gaussEmb_eq, gaussEmb_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem gaussEmb_algebraMap (c : K) :
    gaussEmb (algebraMap K (Gauss K) c) = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

theorem gaussEmb_of_commute {x : Matrix (Fin 2) (Fin 2) K} (hx : x * J₁ = J₁ * x) :
    gaussEmb (⟨x 0 0, x 0 1⟩ : Gauss K) = x := by
  have e : ∀ i j, (x * J₁ : Matrix (Fin 2) (Fin 2) K) i j =
      (J₁ * x : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by rw [hx]
  have e00 := e 0 0
  have e01 := e 0 1
  simp [J₁, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have h10 : x 1 0 = - x 0 1 := by linear_combination -e00
  have h11 : x 1 1 = x 0 0 := by linear_combination -e01
  rw [gaussEmb_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h11]

@[expose] def J₁E : Matrix (Fin 2) (Fin 2) (Gauss K) := !![0, 1; -1, 0]

@[expose] def gaussBlock (Z : Matrix (Fin 2) (Fin 2) (Gauss K)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (gaussEmb (Z 0 0)) (gaussEmb (Z 0 1)) (gaussEmb (Z 1 0)) (gaussEmb (Z 1 1))

theorem gaussBlock_mul (Z W : Matrix (Fin 2) (Fin 2) (Gauss K)) :
    gaussBlock (Z * W) = gaussBlock Z * gaussBlock W := by
  simp only [gaussBlock, fromBlocks_multiply, Matrix.mul_apply, Fin.sum_univ_two, map_add,
    map_mul]

theorem gaussBlock_one : gaussBlock (1 : Matrix (Fin 2) (Fin 2) (Gauss K)) = 1 := by
  rw [← fromBlocks_one]
  simp [gaussBlock]

theorem gaussBlock_injective : Function.Injective (gaussBlock (K := K)) := by
  intro Z W h
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp h
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  exacts [gaussEmb_injective h1, gaussEmb_injective h2, gaussEmb_injective h3,
    gaussEmb_injective h4]

theorem gaussBlock_transpose (Z : Matrix (Fin 2) (Fin 2) (Gauss K)) :
    (gaussBlock Z)ᵀ = gaussBlock Zᴴ := by
  simp only [gaussBlock, fromBlocks_transpose, conjTranspose_apply, gaussEmb_star]

theorem formJ_eq_gaussBlock : formJ 2 K = gaussBlock (J₁E (K := K)) := by
  simp [formJ, gaussBlock, J₁E]

theorem kron_one_J₁_eq_gaussBlock :
    kron 1 (J₁ : Matrix (Fin 2) (Fin 2) K) =
      gaussBlock ((QuadraticAlgebra.omega : Gauss K) • (1 : Matrix (Fin 2) (Fin 2) (Gauss K))) := by
  have hω : gaussEmb (QuadraticAlgebra.omega : Gauss K) = J₁ := by
    rw [gaussEmb_apply, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_smul, one_smul,
      zero_add]
  simp [kron, gaussBlock, hω]

theorem gaussBlock_map (g : Matrix (Fin 2) (Fin 2) K) :
    gaussBlock (g.map (algebraMap K (Gauss K))) = kron g 1 := by
  simp only [gaussBlock, kron, map_apply, gaussEmb_algebraMap]

theorem gaussBlock_smul_map (z : Gauss K) (g : Matrix (Fin 2) (Fin 2) K) :
    gaussBlock (z • g.map (algebraMap K (Gauss K))) = kron g (gaussEmb z) := by
  simp only [gaussBlock, kron, Matrix.smul_apply, map_apply, smul_eq_mul, map_mul,
    gaussEmb_algebraMap, Matrix.mul_smul, Matrix.mul_one]

theorem exists_gaussBlock_of_commute {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : A * kron 1 J₁ = kron 1 J₁ * A) : ∃ Z, gaussBlock Z = A := by
  have hT : kron 1 (J₁ : Matrix (Fin 2) (Fin 2) K) = fromBlocks J₁ 0 0 J₁ := by
    simp [kron]
  rw [hT, ← fromBlocks_toBlocks A, fromBlocks_multiply, fromBlocks_multiply] at hA
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp hA
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at h1 h2 h3 h4
  refine ⟨!![⟨A.toBlocks₁₁ 0 0, A.toBlocks₁₁ 0 1⟩, ⟨A.toBlocks₁₂ 0 0, A.toBlocks₁₂ 0 1⟩;
    ⟨A.toBlocks₂₁ 0 0, A.toBlocks₂₁ 0 1⟩, ⟨A.toBlocks₂₂ 0 0, A.toBlocks₂₂ 0 1⟩], ?_⟩
  conv_rhs => rw [← fromBlocks_toBlocks A]
  simp only [gaussBlock, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    cons_val_one]
  rw [gaussEmb_of_commute h1, gaussEmb_of_commute h2, gaussEmb_of_commute h3,
    gaussEmb_of_commute h4]

theorem gaussBlock_symplectic_iff (Z : Matrix (Fin 2) (Fin 2) (Gauss K)) :
    (gaussBlock Z)ᵀ * formJ 2 K * gaussBlock Z = formJ 2 K ↔ Zᴴ * J₁E * Z = J₁E := by
  rw [formJ_eq_gaussBlock, gaussBlock_transpose, ← gaussBlock_mul, ← gaussBlock_mul]
  exact gaussBlock_injective.eq_iff

theorem exists_map_of_det_eq_one (h2 : (2 : K) ≠ 0) {Z : Matrix (Fin 2) (Fin 2) (Gauss K)}
    (hsym : Zᴴ * J₁E * Z = J₁E) (hdet : Z.det = 1) :
    ∃ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧ Z = g.map (algebraMap K (Gauss K)) := by
  have hT : Zᵀ * J₁E * Z = J₁E := by
    rw [J₁E, transpose_mul_J₁_mul, hdet, one_smul]
  have hu : IsUnit (J₁E * Z) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_mul, hdet, mul_one]
    simp [J₁E, det_fin_two]
  have hHT : Zᴴ = Zᵀ := by
    apply hu.mul_right_cancel
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hsym, hT]
  have hstar : ∀ i j, star (Z i j) = Z i j := fun i j => by
    have := congrFun (congrFun hHT j) i
    simpa using this
  have him : ∀ i j, (Z i j).im = 0 := fun i j => by
    have h := congrArg QuadraticAlgebra.im (hstar i j)
    rw [QuadraticAlgebra.im_star] at h
    have h' : (2 : K) * (Z i j).im = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2
  refine ⟨Matrix.of fun i j => (Z i j).re, ?_, ?_⟩
  · have hZ : Z = (Matrix.of fun i j => (Z i j).re).map (algebraMap K (Gauss K)) := by
      ext i j
      · simp
      · simp [him i j]
    have h1 : algebraMap K (Gauss K) (Matrix.of fun i j => (Z i j).re).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hZ, hdet]
    exact (algebraMap K (Gauss K)).injective (by rw [h1, map_one])
  · ext i j
    · simp
    · simp [him i j]

end CFSG.ComponentClassification.CatFactsSp4
