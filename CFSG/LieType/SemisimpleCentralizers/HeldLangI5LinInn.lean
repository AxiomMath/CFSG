module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification

variable {n : ℕ} {K : Type} [Field K]

theorem conjAut_toGL_eq (g : Matrix.SpecialLinearGroup (Fin n) K) :
    conjAut n K (Matrix.SpecialLinearGroup.toGL g) = MulAut.conj (proj n K g) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  simp [Matrix.SpecialLinearGroup.toGL]

theorem det_inverseTranspose (A : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.inverseTranspose A) =
      (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_inverseTranspose,
    Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem conjAut_mem_innAutDerived [Finite K] (A : GL (Fin n) K) (hA3 : (conjAut n K A) ^ 3 = 1) :
    conjAut n K A ∈ innAutDerived (projectiveSL n K) := by
  set X := conjAut n K A with hXdef
  set δ := dualAut n K with hδdef
  set B := Matrix.GeneralLinearGroup.inverseTranspose A with hBdef
  have hδX : δ * X = conjAut n K B * δ := dualAut_mul_conjAut A
  have hC : ⁅X, δ⁆ = conjAut n K (A * B⁻¹) := by
    rw [commutatorElement_def, map_mul, map_inv]
    have h1 : δ * X * δ⁻¹ = conjAut n K B := by rw [hδX, mul_assoc, mul_inv_cancel, mul_one]
    calc X * δ * X⁻¹ * δ⁻¹ = X * (δ * X * δ⁻¹)⁻¹ := by group
      _ = X * (conjAut n K B)⁻¹ := by rw [h1]
  set s : GL (Fin n) K := A * B⁻¹ * A⁻¹ * A⁻¹ with hsdef
  have hdets : Matrix.GeneralLinearGroup.det s = 1 := by
    rw [hsdef]
    simp only [map_mul, map_inv]
    rw [hBdef, det_inverseTranspose]
    group
  set g : Matrix.SpecialLinearGroup (Fin n) K := ⟨(s : Matrix (Fin n) (Fin n) K), by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdets, Units.val_one]⟩ with hgdef
  have hsg : Matrix.SpecialLinearGroup.toGL g = s := Units.ext rfl
  have hS : conjAut n K s ∈ inner (projectiveSL n K) :=
    ⟨proj n K g, by rw [← conjAut_toGL_eq, hsg]⟩
  have hB : A * B⁻¹ = s * A * A := by rw [hsdef]; group
  have hC' : ⁅X, δ⁆ = conjAut n K s * X * X := by
    rw [hC, hB, map_mul, map_mul]
  have hX3 : X * X * X = 1 := by
    rw [← pow_three']
    exact hA3
  have hXeq : X = ⁅X, δ⁆⁻¹ * conjAut n K s := by
    calc X = (X * X)⁻¹ := (inv_eq_of_mul_eq_one_right hX3).symm
      _ = (conjAut n K s * X * X)⁻¹ * conjAut n K s := by group
      _ = ⁅X, δ⁆⁻¹ * conjAut n K s := by rw [hC']
  have hcomm : ⁅X, δ⁆ ∈ innAutDerived (projectiveSL n K) :=
    commutator_le_innAutDerived _ (by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  rw [hXeq]
  exact mul_mem (inv_mem hcomm) (inner_le_innAutDerived _ hS)

end CFSG.LieType.SemisimpleCentralizers.HeldLang
