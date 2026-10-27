module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFaithfulness

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearInner

noncomputable section

open CatalogueBHigherLinearAction

universe u

theorem ringChar_ne_two_of_odd_card (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  let : Fintype K := Fintype.ofFinite K
  have hmod : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  intro hchar
  have heven := FiniteField.even_card_of_char_two hchar
  omega

theorem sl_quasisimple (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin n) K) := by
  apply CatalogueBGeneralLinear.specialLinear_quasisimple n K hn
  · rcases hparameter with hn3 | hq5
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hparameter with hn3 | hq5
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

theorem inner_involution_projective_data
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hne : innerDiagonalAction n K A ≠ 1)
    (hsq : innerDiagonalAction n K A ^ 2 = 1) :
    Matrix.ProjGenLinGroup.mk A ≠ 1 ∧
      Matrix.ProjGenLinGroup.mk A ^ 2 = 1 ∧
        ∃ c : Kˣ, A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  refine ⟨projective_ne_one_of_innerDiagonalAction_ne_one n K A hne,
    projective_sq_eq_one_of_innerDiagonalAction_sq_eq_one n K hn hparameter A hsq, ?_⟩
  obtain ⟨c, hc⟩ := unit_scalar_sq_of_innerDiagonalAction_sq_eq_one n K hn hparameter A hsq
  exact ⟨c, hc.symm⟩

theorem sl_center_scalar_iff (n : ℕ) (K : Type u) [Field K] (hn : 1 ≤ n)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) ↔
      ∃ c : K, c ^ n = 1 ∧ Matrix.scalar (Fin n) c = g := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  simpa only [Fintype.card_fin] using
    (Matrix.SpecialLinearGroup.mem_center_iff (A := g))

@[expose] def slScalarCenter (n : ℕ) (K : Type u) [Field K] :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) K) where
  carrier := {g | ∃ c : Kˣ, c ^ n = 1 ∧
    Matrix.SpecialLinearGroup.toGL g = Matrix.GeneralLinearGroup.scalar (Fin n) c}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc, hcg⟩ ⟨d, hd, hdh⟩
    refine ⟨c * d, by simp [mul_pow, hc, hd], ?_⟩
    rw [map_mul, hcg, hdh, map_mul]
  inv_mem' := by
    rintro g ⟨c, hc, hcg⟩
    refine ⟨c⁻¹, by simp [inv_pow, hc], ?_⟩
    rw [map_inv, hcg, map_inv]

theorem slScalarCenter_eq_center (n : ℕ) (K : Type u) [Field K] :
    slScalarCenter n K = Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  ext g
  change (∃ c : Kˣ, c ^ n = 1 ∧
    Matrix.SpecialLinearGroup.toGL g = Matrix.GeneralLinearGroup.scalar (Fin n) c) ↔ _
  constructor
  · rintro ⟨c, _hc, hcg⟩
    apply (Matrix.SpecialLinearGroup.toGL_mem_center_iff g).mp
    rw [hcg, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  · intro hg
    have hGL := (Matrix.SpecialLinearGroup.toGL_mem_center_iff g).mpr hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hGL
    obtain ⟨c, hc⟩ := hGL
    refine ⟨c, ?_, hc.symm⟩
    have hdet := congrArg Matrix.GeneralLinearGroup.det hc
    simpa only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
      Matrix.SpecialLinearGroup.coeToGL_det] using hdet

instance slScalarCenterNormal (n : ℕ) (K : Type u) [Field K] :
    (slScalarCenter n K).Normal := by
  rw [slScalarCenter_eq_center]
  infer_instance

abbrev ScalarProjectiveSpecialLinear (n : ℕ) (K : Type u) [Field K] :=
  Matrix.SpecialLinearGroup (Fin n) K ⧸ slScalarCenter n K

@[expose] def scalarProjectiveSpecialLinearEquiv (n : ℕ) (K : Type u) [Field K] :
    ScalarProjectiveSpecialLinear n K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
  QuotientGroup.quotientMulEquivOfEq (slScalarCenter_eq_center n K)

theorem scalarProjectiveSpecialLinearEquiv_mk (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    scalarProjectiveSpecialLinearEquiv n K ((QuotientGroup.mk' (slScalarCenter n K)) g) =
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))) g :=
  QuotientGroup.quotientMulEquivOfEq_mk (slScalarCenter_eq_center n K) g

end

end CFSG.ComponentClassification.CatalogueBHigherLinearInner
