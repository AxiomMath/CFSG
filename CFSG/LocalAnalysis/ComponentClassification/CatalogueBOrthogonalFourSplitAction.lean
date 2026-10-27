module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitCoordinates
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

open Matrix

variable {K : Type*} [Field K]

@[expose] def leftRight (A B : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  (Units.mulLeftLinearEquiv K _ A).trans (Units.mulRightLinearEquiv K B⁻¹)

theorem leftRight_apply (A B : Matrix.GeneralLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    leftRight A B X = A.val * X * (B⁻¹).val := rfl

theorem leftRight_one : leftRight (1 : Matrix.GeneralLinearGroup (Fin 2) K) 1 = 1 := by
  apply LinearEquiv.ext
  intro X
  simp [leftRight_apply]

theorem leftRight_mul (A B C E : Matrix.GeneralLinearGroup (Fin 2) K) :
    leftRight (A * C) (B * E) = leftRight A B * leftRight C E := by
  apply LinearEquiv.ext
  intro X
  simp only [LinearEquiv.mul_apply, leftRight_apply, Units.val_mul, _root_.mul_inv_rev]
  simp [Matrix.mul_assoc]

theorem leftRight_det (A B : Matrix.GeneralLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    (leftRight A B X).det = A.val.det * X.det * (B⁻¹).val.det := by
  simp only [leftRight_apply, Matrix.det_mul]

@[expose] def equalDeterminants (K : Type*) [Field K] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) K × Matrix.GeneralLinearGroup (Fin 2) K) where
  carrier := {z | Matrix.GeneralLinearGroup.det z.1 = Matrix.GeneralLinearGroup.det z.2}
  one_mem' := rfl
  mul_mem' {a} {b} ha hb := by
    change Matrix.GeneralLinearGroup.det a.1 = Matrix.GeneralLinearGroup.det a.2 at ha
    change Matrix.GeneralLinearGroup.det b.1 = Matrix.GeneralLinearGroup.det b.2 at hb
    change Matrix.GeneralLinearGroup.det (a.1 * b.1) = Matrix.GeneralLinearGroup.det (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  inv_mem' {a} ha := by
    change Matrix.GeneralLinearGroup.det a.1 = Matrix.GeneralLinearGroup.det a.2 at ha
    change Matrix.GeneralLinearGroup.det a.1⁻¹ = Matrix.GeneralLinearGroup.det a.2⁻¹
    rw [map_inv, map_inv, ha]

theorem mem_equalDeterminants (A B : Matrix.GeneralLinearGroup (Fin 2) K) :
    (A, B) ∈ equalDeterminants K ↔ A.val.det = B.val.det := by
  change Matrix.GeneralLinearGroup.det A = Matrix.GeneralLinearGroup.det B ↔ _
  exact Units.ext_iff

abbrev DeterminantIsometries (K : Type*) [Field K] :=
  TauCeti.QuadraticMap.orthogonalGroup (determinantForm K)

@[expose] def rho : equalDeterminants K →* DeterminantIsometries K where
  toFun z := ⟨leftRight z.val.1 z.val.2, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (fun X => by
    rw [determinantForm_apply, determinantForm_apply, leftRight_det]
    have h := (mem_equalDeterminants z.val.1 z.val.2).mp z.property
    rw [h, mul_comm z.val.2.val.det X.det, mul_assoc,
      ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, mul_one])⟩
  map_one' := Subtype.ext leftRight_one
  map_mul' z w := Subtype.ext (leftRight_mul _ _ _ _)

theorem rho_apply (z : equalDeterminants K) (X : Matrix (Fin 2) (Fin 2) K) :
    (rho z).val X = z.val.1.val * X * (z.val.2⁻¹).val := rfl

@[expose] def tau : DeterminantIsometries K :=
  ⟨Matrix.transposeLinearEquiv (Fin 2) (Fin 2) K K, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (fun X => by
    change determinantForm K X.transpose = determinantForm K X
    rw [determinantForm_apply, determinantForm_apply, Matrix.det_transpose])⟩

theorem tau_apply (X : Matrix (Fin 2) (Fin 2) K) : (tau (K := K)).val X = X.transpose := rfl

theorem tau_mul_tau : (tau (K := K)) * tau = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  exact Matrix.transpose_transpose X

theorem tau_inv : (tau (K := K))⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_mul_tau

@[expose] def specialPairs :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      equalDeterminants K where
  toFun z := ⟨(Matrix.SpecialLinearGroup.toGL z.1, Matrix.SpecialLinearGroup.toGL z.2), by
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL z.1) =
      Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL z.2)
    simp⟩
  map_one' := Subtype.ext (Prod.ext (map_one _) (map_one _))
  map_mul' z w := Subtype.ext (Prod.ext (map_mul _ _ _) (map_mul _ _ _))

@[expose] def specialRho :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      DeterminantIsometries K := rho.comp specialPairs

theorem specialRho_apply
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (specialRho z).val X = z.1.val * X *
      (z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val := by
  change (Matrix.SpecialLinearGroup.toGL z.1).val * X *
    ((Matrix.SpecialLinearGroup.toGL z.2)⁻¹).val = _
  rw [← map_inv]
  rfl

@[expose] def specialImage (K : Type*) [Field K] : Subgroup (DeterminantIsometries K) :=
  (specialRho (K := K)).range

@[expose] def leftRightImage (K : Type*) [Field K] : Subgroup (DeterminantIsometries K) :=
  (rho (K := K)).range

@[expose] def scalarPair (c : Kˣ) : equalDeterminants K :=
  ⟨(Matrix.GeneralLinearGroup.scalar (Fin 2) c,
    Matrix.GeneralLinearGroup.scalar (Fin 2) c), rfl⟩

theorem rho_scalarPair (c : Kˣ) : rho (scalarPair c) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  simp only [rho_apply, scalarPair, Matrix.GeneralLinearGroup.coe_scalar,
    ← map_inv]
  ext i j
  simp [Matrix.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
  rw [mul_left_comm, mul_inv_cancel₀ c.ne_zero, mul_one]

theorem rho_eq_one_iff (z : equalDeterminants K) :
    rho z = 1 ↔ ∃ c : Kˣ, z = scalarPair c := by
  constructor
  · intro hz
    have hAX : ∀ X : Matrix (Fin 2) (Fin 2) K,
        z.val.1.val * X * (z.val.2⁻¹).val = X := fun X => by
      have h := congrArg (fun g : DeterminantIsometries K => g.val X) hz
      exact h
    have hAB : z.val.1 = z.val.2 := by
      apply Units.ext
      have h := congrArg (fun X => X * z.val.2.val) (hAX 1)
      simpa [Matrix.mul_assoc, Units.inv_mul] using h
    have hcomm : ∀ C : Matrix.GeneralLinearGroup (Fin 2) K, z.val.1 * C = C * z.val.1 := by
      intro C
      apply Units.ext
      have h := congrArg (fun X => X * z.val.1.val) (hAX C.val)
      simpa [hAB, Matrix.mul_assoc, Units.inv_mul] using h
    have hcenter : z.val.1 ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro C
      exact (hcomm C).symm
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
    obtain ⟨c, hc⟩ := hcenter
    refine ⟨c, Subtype.ext (Prod.ext hc.symm ?_)⟩
    exact hAB.symm.trans hc.symm
  · rintro ⟨c, rfl⟩
    exact rho_scalarPair c

theorem rho_kernel : (rho (K := K)).ker =
    { carrier := {z | ∃ c : Kˣ, z = scalarPair c}
      one_mem' := ⟨1, by apply Subtype.ext; exact (Prod.ext (map_one _) (map_one _)).symm⟩
      mul_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
        exact ⟨c * d, Subtype.ext (by simp [scalarPair])⟩
      inv_mem' := by
        rintro _ ⟨c, rfl⟩
        exact ⟨c⁻¹, Subtype.ext (by simp [scalarPair])⟩ } := by
  ext z
  exact rho_eq_one_iff z

theorem specialRho_eq_one_iff
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    specialRho z = 1 ↔ ∃ c : Kˣ, c ^ 2 = 1 ∧
      Matrix.SpecialLinearGroup.toGL z.1 = Matrix.GeneralLinearGroup.scalar (Fin 2) c ∧
      Matrix.SpecialLinearGroup.toGL z.2 = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [specialRho, MonoidHom.comp_apply, rho_eq_one_iff]
  constructor
  · rintro ⟨c, hc⟩
    have h := congrArg (fun w : equalDeterminants K => w.val) hc
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    refine ⟨c, ?_, ha, hb⟩
    have hd := congrArg Matrix.GeneralLinearGroup.det ha
    simpa [scalarPair, specialPairs] using hd.symm
  · rintro ⟨c, _, ha, hb⟩
    exact ⟨c, Subtype.ext (Prod.ext ha hb)⟩

theorem specialRho_kernel_le_center : (specialRho (K := K)).ker ≤
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro z hz
  obtain ⟨c, _, ha, hb⟩ := (specialRho_eq_one_iff z).mp hz
  apply Subgroup.mem_center_iff.mpr
  intro w
  apply Prod.ext
  · apply Matrix.SpecialLinearGroup.toGL_injective
    simp only [Prod.fst_mul, map_mul, ha]
    exact (Matrix.GeneralLinearGroup.scalar_commute c _).symm
  · apply Matrix.SpecialLinearGroup.toGL_injective
    simp only [Prod.snd_mul, map_mul, hb]
    exact (Matrix.GeneralLinearGroup.scalar_commute c _).symm

end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
