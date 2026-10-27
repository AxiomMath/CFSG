module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearInner

noncomputable section

open Matrix CatalogueBHigherLinearAction

universe u

theorem sl_perfect (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) := by
  apply CatalogueBGeneralLinear.specialLinear_perfect n K hn
  · rcases hparameter with hn3 | hq5
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hparameter with hn3 | hq5
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

theorem slConjugation_eq_one_of_innerDiagonalAction_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hA : innerDiagonalAction n K A = 1) : slConjugation n K A = 1 := by
  apply CFSG.GorensteinWalter.perfect_central_automorphism_eq
    (sl_perfect n K hn hparameter) (slConjugation n K A)
    (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin n) K))
  intro g
  let q := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
  have hproj : q (slConjugation n K A g) = q g := by
    rw [← innerDiagonalAction_mk n K A g, hA]
    rfl
  have hdelta : q (slConjugation n K A g * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hproj, mul_inv_cancel]
  have hmem : slConjugation n K A g * g⁻¹ ∈ q.ker := hdelta
  rwa [QuotientGroup.ker_mk'] at hmem

theorem commute_sl_of_innerDiagonalAction_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hA : innerDiagonalAction n K A = 1)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    Commute A (Matrix.SpecialLinearGroup.toGL g) := by
  have hconj := slConjugation_eq_one_of_innerDiagonalAction_eq_one n K hn hparameter A hA
  have heq : A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ = Matrix.SpecialLinearGroup.toGL g := by
    rw [← toGL_slConjugation, hconj]
    rfl
  change A * Matrix.SpecialLinearGroup.toGL g = Matrix.SpecialLinearGroup.toGL g * A
  exact (mul_inv_eq_iff_eq_mul.mp heq)

theorem matrix_scalar_of_innerDiagonalAction_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hA : innerDiagonalAction n K A = 1) :
    A.val ∈ Set.range (Matrix.scalar (Fin n)) := by
  apply Matrix.mem_range_scalar_of_commute_transvectionStruct
  intro t
  have hcomm := (commute_sl_of_innerDiagonalAction_eq_one n K hn hparameter A hA
    t.toSpecialLinearGroup).symm
  exact congrArg Units.val hcomm.eq

theorem unit_scalar_of_innerDiagonalAction_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hA : innerDiagonalAction n K A = 1) :
    ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c = A := by
  have hcenter := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    (matrix_scalar_of_innerDiagonalAction_eq_one n K hn hparameter A hA)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  exact hcenter

theorem innerDiagonalAction_eq_one_iff_projective_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    innerDiagonalAction n K A = 1 ↔ Matrix.ProjGenLinGroup.mk A = 1 := by
  constructor
  · intro hA
    obtain ⟨c, rfl⟩ := unit_scalar_of_innerDiagonalAction_eq_one n K hn hparameter A hA
    exact Matrix.ProjGenLinGroup.mk_scalar c
  · intro hA
    rw [innerDiagonalAction_eq_pglAction, hA, map_one]

theorem pglAction_eq_one_iff
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (a : Matrix.ProjGenLinGroup (Fin n) K) : pglAction n K a = 1 ↔ a = 1 := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
  exact innerDiagonalAction_eq_one_iff_projective_eq_one n K hn hparameter A

theorem pglAction_injective
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K) :
    Function.Injective (pglAction n K) := by
  intro a b hab
  have h : pglAction n K (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  exact mul_inv_eq_one.mp ((pglAction_eq_one_iff n K hn hparameter _).mp h)

theorem projective_sq_eq_one_of_innerDiagonalAction_sq_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hA : innerDiagonalAction n K A ^ 2 = 1) :
    Matrix.ProjGenLinGroup.mk A ^ 2 = 1 := by
  apply (pglAction_eq_one_iff n K hn hparameter _).mp
  rw [map_pow, ← innerDiagonalAction_eq_pglAction]
  exact hA

theorem unit_scalar_sq_of_innerDiagonalAction_sq_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hA : innerDiagonalAction n K A ^ 2 = 1) :
    ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c = A ^ 2 := by
  apply unit_scalar_of_innerDiagonalAction_eq_one n K hn hparameter (A ^ 2)
  rw [map_pow]
  exact hA

theorem projective_ne_one_of_innerDiagonalAction_ne_one
    (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hA : innerDiagonalAction n K A ≠ 1) : Matrix.ProjGenLinGroup.mk A ≠ 1 := by
  intro h
  apply hA
  rw [innerDiagonalAction_eq_pglAction, h, map_one]

theorem not_scalar_of_innerDiagonalAction_ne_one
    (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hA : innerDiagonalAction n K A ≠ 1) :
    ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c ≠ A := by
  intro c hc
  apply hA
  rw [← hc, innerDiagonalAction_scalar]

end

end CFSG.ComponentClassification.CatalogueBHigherLinearInner
