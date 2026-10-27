module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism

public section

namespace CFSG.ComponentClassification.CatalogueBLinearSemilinear

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField

universe u

theorem specialLinear_perfect (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 4 ≤ Nat.card K) :
    Group.IsPerfect (SpecialLinearGroup (Fin n) K) := by
  apply CatalogueBGeneralLinear.specialLinear_perfect n K hn
  · rcases hparameter with hn3 | hq4
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hparameter with hn3 | hq4
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

theorem slSemilinearAction_eq_one_of_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 4 ≤ Nat.card K)
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K)
    (hidentity : semilinearAction n K A sigma = 1) :
    slSemilinearAction n K A sigma = 1 := by
  apply CFSG.GorensteinWalter.perfect_central_automorphism_eq
    (specialLinear_perfect n K hn hparameter) (slSemilinearAction n K A sigma)
    (MulEquiv.refl (SpecialLinearGroup (Fin n) K))
  intro g
  let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K))
  have hproj : q (slSemilinearAction n K A sigma g) = q g := by
    rw [← semilinearAction_mk, hidentity]
    rfl
  have hdelta : q (slSemilinearAction n K A sigma g * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hproj, mul_inv_cancel]
  have hmem : slSemilinearAction n K A sigma g * g⁻¹ ∈ q.ker := hdelta
  rwa [QuotientGroup.ker_mk'] at hmem

theorem semilinear_commutation_of_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 4 ≤ Nat.card K)
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K)
    (hidentity : semilinearAction n K A sigma = 1)
    (g : SpecialLinearGroup (Fin n) K) :
    A * glFieldAut (Fin n) K sigma (SpecialLinearGroup.toGL g) =
      SpecialLinearGroup.toGL g * A := by
  have hsl := slSemilinearAction_eq_one_of_eq_one n K hn hparameter A sigma hidentity
  have heq : A * glFieldAut (Fin n) K sigma (SpecialLinearGroup.toGL g) * A⁻¹ =
      SpecialLinearGroup.toGL g := by
    rw [← slSemilinearAction_toGL, hsl]
    rfl
  exact mul_inv_eq_iff_eq_mul.mp heq

theorem unit_scalar_of_semilinearAction_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 4 ≤ Nat.card K)
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K)
    (hidentity : semilinearAction n K A sigma = 1) :
    ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = A := by
  have hscalar : A.val ∈ Set.range (Matrix.scalar (Fin n)) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro i j hij
    let g : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hij 1
    have hfield : glFieldAut (Fin n) K sigma (SpecialLinearGroup.toGL g) =
        SpecialLinearGroup.toGL g := by
      apply GeneralLinearGroup.ext
      intro k l
      change sigma (Matrix.transvection i j 1 k l) = Matrix.transvection i j 1 k l
      simp [Matrix.transvection, Matrix.single, Matrix.one_apply]
    have hcomm := semilinear_commutation_of_eq_one n K hn hparameter A sigma hidentity g
    rw [hfield] at hcomm
    have hmatrix := congrArg Units.val hcomm.symm
    change Matrix.transvection i j 1 * A.val = A.val * Matrix.transvection i j 1 at hmatrix
    change Matrix.single i j 1 * A.val = A.val * Matrix.single i j 1
    simpa only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, add_left_cancel_iff] using hmatrix
  have hcenter := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hscalar
  rw [GeneralLinearGroup.center_eq_range_scalar] at hcenter
  exact hcenter

theorem field_eq_one_of_semilinearAction_eq_one
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 4 ≤ Nat.card K)
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K)
    (hidentity : semilinearAction n K A sigma = 1) : sigma = 1 := by
  obtain ⟨c, hscalar⟩ := unit_scalar_of_semilinearAction_eq_one n K hn hparameter
    A sigma hidentity
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  apply RingEquiv.ext
  intro a
  let g : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hij a
  have hcomm := semilinear_commutation_of_eq_one n K hn hparameter A sigma hidentity g
  rw [← hscalar, GeneralLinearGroup.scalar_commute] at hcomm
  have hfixed : glFieldAut (Fin n) K sigma (SpecialLinearGroup.toGL g) =
      SpecialLinearGroup.toGL g := mul_right_cancel hcomm
  have hentry := congrArg (fun M : GeneralLinearGroup (Fin n) K => M i j) hfixed
  change sigma (Matrix.transvection i j a i j) = Matrix.transvection i j a i j at hentry
  simpa [Matrix.transvection, Matrix.single, Matrix.one_apply, hij] using hentry

theorem semilinearAction_eq_one_iff
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 4 ≤ Nat.card K)
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K) :
    semilinearAction n K A sigma = 1 ↔
      sigma = 1 ∧ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = A := by
  constructor
  · intro hidentity
    exact ⟨field_eq_one_of_semilinearAction_eq_one n K hn hparameter A sigma hidentity,
      unit_scalar_of_semilinearAction_eq_one n K hn hparameter A sigma hidentity⟩
  · rintro ⟨rfl, c, rfl⟩
    rw [semilinearAction_scalar, map_one]

theorem involution_scalar_cocycle
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 4 ≤ Nat.card K)
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K)
    (hsquare : semilinearAction n K A sigma ^ 2 = 1) :
    sigma ^ 2 = 1 ∧ ∃ c : Kˣ,
      GeneralLinearGroup.scalar (Fin n) c = A * glFieldAut (Fin n) K sigma A := by
  rw [semilinearAction_sq] at hsquare
  exact (semilinearAction_eq_one_iff n K hn hparameter _ _).mp hsquare

end

end CFSG.ComponentClassification.CatalogueBLinearSemilinear
