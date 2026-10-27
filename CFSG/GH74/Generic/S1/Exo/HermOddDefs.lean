module

public import CFSG.GH74.Generic.S1.Exo.OddNormPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenNormTail

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module Matrix CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups

section Space

variable {K E : Type} [Field K] [Field E] [Algebra K E]

@[expose] def hermOddSpace (σ : E ≃ₐ[K] E) : Submodule K (Matrix (Fin 2) (Fin 2) E) where
  carrier := {X | ∀ i j, σ (X j i) = X i j}
  add_mem' := fun {X Y} hX hY i j => by
    simp only [Matrix.add_apply, map_add, hX i j, hY i j]
  zero_mem' := fun i j => by simp
  smul_mem' := fun c X hX i j => by
    simp only [Matrix.smul_apply, map_smul, hX i j]

@[expose] def hermOddMat (σ : E ≃ₐ[K] E) (a b : K) (z : E) : Matrix (Fin 2) (Fin 2) E :=
  !![algebraMap K E a, z; σ z, algebraMap K E b]

@[expose] def hermOddMatLin (σ : E ≃ₐ[K] E) :
    (((Fin 1 → K) × (Fin 1 → K)) × E) →ₗ[K] Matrix (Fin 2) (Fin 2) E where
  toFun v := hermOddMat σ (v.1.1 0) (v.1.2 0) v.2
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermOddMat]
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermOddMat, Algebra.smul_def]

end Space

section Coord

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] (D : OddNormPlane K E)

theorem hermOddMat_mem (a b : K) (z : E) : hermOddMat D.σ a b z ∈ hermOddSpace D.σ := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hermOddMat, D.sigma_sigma]

@[expose] noncomputable def hermOddCoordLin :
    (((Fin 1 → K) × (Fin 1 → K)) × E) →ₗ[K] hermOddSpace D.σ :=
  (hermOddMatLin D.σ).codRestrict (hermOddSpace D.σ) fun v =>
    hermOddMat_mem D (v.1.1 0) (v.1.2 0) v.2

theorem coe_hermOddCoordLin (v : ((Fin 1 → K) × (Fin 1 → K)) × E) :
    ((hermOddCoordLin D v : hermOddSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      hermOddMat D.σ (v.1.1 0) (v.1.2 0) v.2 :=
  rfl

theorem hermOddCoordLin_injective : Function.Injective (hermOddCoordLin D) := by
  intro u v h
  have h' := congrArg Subtype.val h
  rw [coe_hermOddCoordLin, coe_hermOddCoordLin] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h11 := congrFun (congrFun h' 1) 1
  have h01 := congrFun (congrFun h' 0) 1
  simp only [hermOddMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h11 h01
  have e1 := (algebraMap K E).injective h00
  have e2 := (algebraMap K E).injective h11
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) h01
  · rw [Subsingleton.elim i 0]
    exact e1
  · rw [Subsingleton.elim i 0]
    exact e2

theorem hermOddCoordLin_surjective : Function.Surjective (hermOddCoordLin D) := by
  rintro ⟨X, hX⟩
  obtain ⟨a, ha⟩ := (D.sigma_eq_self_iff (X 0 0)).mp (hX 0 0)
  obtain ⟨b, hb⟩ := (D.sigma_eq_self_iff (X 1 1)).mp (hX 1 1)
  refine ⟨((fun _ => a, fun _ => b), X 0 1), Subtype.ext ?_⟩
  rw [coe_hermOddCoordLin]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOddMat, ha, hb, ← hX 1 0]

@[expose] noncomputable def hermOddCoord :
    (((Fin 1 → K) × (Fin 1 → K)) × E) ≃ₗ[K] hermOddSpace D.σ :=
  LinearEquiv.ofBijective (hermOddCoordLin D)
    ⟨hermOddCoordLin_injective D, hermOddCoordLin_surjective D⟩

theorem coe_hermOddCoord (v : ((Fin 1 → K) × (Fin 1 → K)) × E) :
    ((hermOddCoord D v : hermOddSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      hermOddMat D.σ (v.1.1 0) (v.1.2 0) v.2 :=
  rfl

@[expose] noncomputable def hermOddForm : QuadraticForm K (hermOddSpace D.σ) :=
  (evenNormTailForm (-D.N) 1).comp (hermOddCoord D).symm.toLinearMap

end Coord

section Act

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] (D : OddNormPlane K E)

@[expose] def hermOddCongr (σ : E ≃ₐ[K] E) (g : Matrix (Fin 2) (Fin 2) E) :
    Matrix (Fin 2) (Fin 2) E →ₗ[K] Matrix (Fin 2) (Fin 2) E :=
  (LinearMap.mulRight K (g.map σ)ᵀ) ∘ₗ (LinearMap.mulLeft K g)

omit [Finite K] in
theorem hermOddCongr_apply (σ : E ≃ₐ[K] E) (g X : Matrix (Fin 2) (Fin 2) E) :
    hermOddCongr σ g X = g * X * (g.map σ)ᵀ :=
  rfl

theorem hermOddCongr_mem (g : Matrix (Fin 2) (Fin 2) E) {X : Matrix (Fin 2) (Fin 2) E}
    (hX : X ∈ hermOddSpace D.σ) : hermOddCongr D.σ g X ∈ hermOddSpace D.σ := by
  intro i j
  have e00 := hX 0 0
  have e01 := hX 0 1
  have e10 := hX 1 0
  have e11 := hX 1 1
  simp only [hermOddCongr_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Fin.sum_univ_two, map_add, map_mul, D.sigma_sigma, e00, e01, e10, e11]
  fin_cases i <;> fin_cases j <;> simp <;> ring

@[expose] noncomputable def hermOddAct (g : Matrix (Fin 2) (Fin 2) E) :
    hermOddSpace D.σ →ₗ[K] hermOddSpace D.σ :=
  (hermOddCongr D.σ g).restrict fun _ hX => hermOddCongr_mem D g hX

@[simp] theorem coe_hermOddAct (g : Matrix (Fin 2) (Fin 2) E) (X : hermOddSpace D.σ) :
    ((hermOddAct D g X : hermOddSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      g * (X : Matrix (Fin 2) (Fin 2) E) * (g.map D.σ)ᵀ :=
  rfl

theorem hermOddAct_one : hermOddAct D 1 = 1 := by
  ext X : 2
  simp [Matrix.map_one]

theorem hermOddAct_mul (g h : Matrix (Fin 2) (Fin 2) E) :
    hermOddAct D (g * h) = hermOddAct D g * hermOddAct D h := by
  ext X : 2
  simp only [coe_hermOddAct, Module.End.mul_apply]
  have : (g * h).map D.σ = g.map D.σ * h.map D.σ := Matrix.map_mul (f := (D.σ : E →+* E))
  rw [this, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

@[expose] noncomputable def hermOddEnd : SL(2, E) →* Module.End K (hermOddSpace D.σ) where
  toFun g := hermOddAct D g.1
  map_one' := hermOddAct_one D
  map_mul' g h := hermOddAct_mul D g.1 h.1

@[expose] noncomputable def hermOddRho : SL(2, E) →* (hermOddSpace D.σ ≃ₗ[K] hermOddSpace D.σ) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (hermOddSpace D.σ)).toMonoidHom.comp
    (hermOddEnd D).toHomUnits

theorem coe_hermOddRho (g : SL(2, E)) (X : hermOddSpace D.σ) :
    ((hermOddRho D g X : hermOddSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      g.1 * (X : Matrix (Fin 2) (Fin 2) E) * (g.1.map D.σ)ᵀ :=
  rfl

end Act

end CFSG.GH74.Generic.S1.Exo
