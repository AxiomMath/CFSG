module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticMatrix

public section

namespace CFSG.ComponentClassification.CatFC.PSLSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution

section Inner

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem inner_proj_data (hn : 2 ≤ n) (hpar : 3 ≤ n ∨ 5 ≤ Nat.card K) {A : GL (Fin n) K}
    (hσ : orderOf (innerDiagonalAction n K A) = 2) :
    ProjGenLinGroup.mk A ≠ 1 ∧ ProjGenLinGroup.mk A ^ 2 = 1 := by
  have hne : innerDiagonalAction n K A ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hsq : innerDiagonalAction n K A ^ 2 = 1 := by
    rw [← hσ]; exact pow_orderOf_eq_one _
  obtain ⟨h1, h2, -⟩ :=
    CatalogueBHigherLinearInner.inner_involution_projective_data n K hn hpar A hne hsq
  exact ⟨h1, h2⟩

theorem card_fixed_dvd (A : GL (Fin n) K) :
    Nat.card (fixedSubgroup (innerDiagonalAction n K A)) ∣
      Nat.card (Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin n) K))) := by
  rw [Nat.card_congr (CatalogueBHigherLinearInner.innerFixedCentralizerEquiv n K A).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_pglCentralizer (A : GL (Fin n) K) :
    Nat.card (Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin n) K))) =
      Nat.card (ordinaryCentralizerProjection A).range *
        (ordinaryCentralizerProjection A).range.index :=
  (Subgroup.card_mul_index _).symm

theorem isSolvable_fixed_of_solvable_centralizer [Nonempty (Fin n)] (A : GL (Fin n) K)
    [Group.IsSolvable (Subgroup.centralizer ({A} : Set (GL (Fin n) K)))] :
    Group.IsSolvable (fixedSubgroup (innerDiagonalAction n K A)) := by
  haveI : Group.IsSolvable (ordinaryCentralizerProjection A).range :=
    solvable_of_surjective (ordinaryCentralizerProjection A).rangeRestrict_surjective
  haveI : Group.IsSolvable (Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (ProjGenLinGroup (Fin n) K))) :=
    solvable_of_ker_le_range (ordinaryCentralizerProjection A).range.subtype
      (projectiveScalarCharacter A) (by
        rw [projectiveScalarCharacter_kernel_eq, Subgroup.range_subtype])
  exact solvable_of_solvable_injective
    (f := ((CatalogueBHigherLinearInner.localPSLRange n K (ProjGenLinGroup.mk A)).subtype.comp
      (CatalogueBHigherLinearInner.innerFixedCentralizerEquiv n K A).toMonoidHom))
    (Subtype.val_injective.comp (CatalogueBHigherLinearInner.innerFixedCentralizerEquiv n K A).injective)

theorem gl_comm_of_le_one {R : Type*} [CommRing R] {r : ℕ} (hr : r ≤ 1) (a b : GL (Fin r) R) :
    a * b = b * a := by
  apply Units.ext
  ext i j
  haveI : Subsingleton (Fin r) := ⟨fun x y => by ext; omega⟩
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply,
    Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i]
  have hj : j = i := Subsingleton.elim _ _
  subst hj
  exact mul_comm _ _

theorem inner_two_false (hpar : 5 ≤ Nat.card K) (htwo : (2 : K) ≠ 0) {A : GL (Fin 2) K}
    (hσ : orderOf (innerDiagonalAction 2 K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction 2 K A))}
    (h : A6Hyp (innerDiagonalAction 2 K A) D) : False := by
  obtain ⟨hne, hinv⟩ := inner_proj_data (le_refl 2) (Or.inr hpar) hσ
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  apply h.not_solvable
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, hb, hr, hs, hrs, e, q, hesc, -, -⟩ :=
      square_projective_centralizer_structure 2 le_rfl A lambda htwo hne hsq hsquare
    generalize positiveMatrixDimension A b.val = r at *
    generalize negativeMatrixDimension A b.val = s at *
    have hr1 : r ≤ 1 := by omega
    have hs1 : s ≤ 1 := by omega
    haveI : Group.IsSolvable (GL (Fin r) K × GL (Fin s) K) :=
      isSolvable_of_comm fun a b => Prod.ext (gl_comm_of_le_one hr1 _ _) (gl_comm_of_le_one hs1 _ _)
    haveI : Group.IsSolvable (Subgroup.centralizer ({A} : Set (GL (Fin 2) K))) :=
      solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
    exact isSolvable_fixed_of_solvable_centralizer A
  · haveI : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    have hdim := CatalogueBProjectiveQuadratic.matrixDimension_twice A lambda hsq
    simp only [Fintype.card_fin] at hdim
    have hm1 : CatalogueBProjectiveQuadratic.matrixDimension A lambda hsq ≤ 1 := by omega
    haveI : Group.IsSolvable (GL (Fin (CatalogueBProjectiveQuadratic.matrixDimension A lambda hsq))
        (CatalogueBProjectiveQuadratic.extension lambda.val)) :=
      isSolvable_of_comm fun a b => gl_comm_of_le_one hm1 _ _
    haveI : Group.IsSolvable (Subgroup.centralizer ({A} : Set (GL (Fin 2) K))) :=
      solvable_of_solvable_injective
        (f := (CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq).toMonoidHom)
        (CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq).injective
    exact isSolvable_fixed_of_solvable_centralizer A

theorem inner_three_false (hK : Nat.card K = 9) (htwo : (2 : K) ≠ 0) {A : GL (Fin 3) K}
    (hσ : orderOf (innerDiagonalAction 3 K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction 3 K A))}
    (h : A6Hyp (innerDiagonalAction 3 K A) D) : False := by
  obtain ⟨hne, hinv⟩ := inner_proj_data (by norm_num) (Or.inl le_rfl) hσ
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, hb, hr, hs, hrs, e, q, hesc, -, -⟩ :=
      square_projective_centralizer_structure 3 (by norm_num) A lambda htwo hne hsq hsquare
    generalize positiveMatrixDimension A b.val = r at *
    generalize negativeMatrixDimension A b.val = s at *
    have hperf2 : commutator (SpecialLinearGroup (Fin 2) K) = ⊤ :=
      Group.isPerfect_def.mp (CatalogueBHigherLinearInner.sl_perfect 2 K le_rfl
        (Or.inr (by omega)))
    have h720 : 360 < Nat.card (SpecialLinearGroup (Fin 2) K) := by
      rw [card_SL_two, hK]; norm_num
    rcases (by omega : r = 2 ∨ s = 2) with hr2 | hs2
    · subst hr2
      have := inner_factor_card_le h hs e hesc hperf2
      omega
    · subst hs2
      let e' := e.trans MulEquiv.prodComm
      have := inner_factor_card_le h hr e' (fun c => by simp [e', hesc c]) hperf2
      omega
  · haveI : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    have hdim := CatalogueBProjectiveQuadratic.matrixDimension_twice A lambda hsq
    simp only [Fintype.card_fin] at hdim
    omega

end Inner

end CFSG.ComponentClassification.CatFC.PSLSmall
