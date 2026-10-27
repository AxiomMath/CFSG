module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.RankThree.PartOne.KFCL.BlockSL
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open Matrix
open scoped commutatorElement

variable (β : Type*) [Fintype β] [DecidableEq β] (K : Type*) [Field K]

abbrev PGL : Type _ := GL β K ⧸ Subgroup.center (GL β K)

@[expose] noncomputable def slImage : Subgroup (PGL β K) :=
  ((QuotientGroup.mk' (Subgroup.center (GL β K))).comp SpecialLinearGroup.toGL).range

variable {β K} in
theorem nonempty_projectiveSpecialLinearGroup_equiv {γ : Type*} [Fintype γ] [DecidableEq γ]
    (e : β ≃ γ) :
    Nonempty (ProjectiveSpecialLinearGroup β K ≃* ProjectiveSpecialLinearGroup γ K) :=
  ⟨QuotientGroup.congr _ _ (CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL e)
    (Subgroup.map_center_eq (CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL e))⟩

private theorem ker_slImage_mk :
    (Subgroup.center (SpecialLinearGroup β K)) =
      ((QuotientGroup.mk' (Subgroup.center (GL β K))).comp
        SpecialLinearGroup.toGL).ker := by
  ext A
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range,
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hscalar⟩
    have hcoe : ((SpecialLinearGroup.toGL A : GL β K) : Matrix β β K) =
        (A : Matrix β β K) := rfl
    by_cases hr0 : r = 0
    · rw [hr0] at hscalar
      rcases isEmpty_or_nonempty β with hβ | hβ
      · haveI : IsEmpty β := hβ
        exact ⟨1, by
          apply Units.ext
          rw [GeneralLinearGroup.coe_scalar]
          exact Subsingleton.elim _ _⟩
      · have hpos : 0 < Fintype.card β := Fintype.card_pos_iff.mpr hβ
        rw [hr0, zero_pow hpos.ne'] at hr
        exact absurd hr zero_ne_one
    · refine ⟨Units.mk0 r hr0, ?_⟩
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, hscalar, hcoe]
  · rintro ⟨c, hc⟩
    have hcoe : ((SpecialLinearGroup.toGL A : GL β K) : Matrix β β K) =
        (A : Matrix β β K) := rfl
    have hA : ((GeneralLinearGroup.scalar β c : GL β K) : Matrix β β K) =
        (A : Matrix β β K) := by
      rw [hc, hcoe]
    have hA' : Matrix.scalar β ((c : K)) = (A : Matrix β β K) := by
      rw [← GeneralLinearGroup.coe_scalar]
      exact hA
    refine ⟨(c : K), ?_, hA'⟩
    have hdet : (A : Matrix β β K).det = 1 := A.prop
    rw [← hA', Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ] at hdet
    exact hdet

theorem nonempty_slImage_equiv :
    Nonempty (slImage β K ≃* ProjectiveSpecialLinearGroup β K) := by
  let φ : SpecialLinearGroup β K →* PGL β K :=
    (QuotientGroup.mk' (Subgroup.center (GL β K))).comp SpecialLinearGroup.toGL
  have hrange : φ.range = slImage β K := rfl
  have hker : φ.ker = Subgroup.center (SpecialLinearGroup β K) := ker_slImage_mk β K |>.symm
  refine ⟨?h⟩
  rw [← hrange]
  exact (QuotientGroup.quotientKerEquivRange φ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)

theorem commutator_le_slImage : commutator (PGL β K) ≤ slImage β K := by
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center (GL β K))) :=
    QuotientGroup.mk'_surjective _
  have hcomm : commutator (PGL β K) =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (GL β K))) (commutator (GL β K)) := by
    change ⁅(⊤ : Subgroup (PGL β K)), ⊤⁆ =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (GL β K)))
        ⁅(⊤ : Subgroup (GL β K)), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj]
  have hgen : commutator (GL β K) ≤ SpecialLinearGroup.toGL.range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    change ⁅(⊤ : Subgroup (GL β K)), ⊤⁆ ≤ GeneralLinearGroup.det.ker
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  calc commutator (PGL β K)
      = Subgroup.map (QuotientGroup.mk' (Subgroup.center (GL β K)))
          (commutator (GL β K)) := hcomm
    _ ≤ Subgroup.map (QuotientGroup.mk' (Subgroup.center (GL β K)))
          SpecialLinearGroup.toGL.range := Subgroup.map_mono hgen
    _ = slImage β K :=
        (MonoidHom.range_comp (QuotientGroup.mk' (Subgroup.center (GL β K)))
          SpecialLinearGroup.toGL).symm

theorem isSimpleGroup_slImage [Finite K] (h2 : 2 ≤ Fintype.card β)
    (h22 : ¬ (Fintype.card β = 2 ∧ Nat.card K ≤ 3)) : IsSimpleGroup (slImage β K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcond : 3 ≤ Fintype.card β ∨ ∃ s : Finset K, s.card = 4 := by
    rcases Nat.lt_or_ge (Fintype.card β) 3 with h3 | h3
    · right
      have h2' : Fintype.card β = 2 := by omega
      have hK : 4 ≤ Nat.card K := by
        by_contra hle
        exact h22 ⟨h2', by omega⟩
      have hcard : 4 ≤ (Finset.univ : Finset K).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact hK
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) hcard
      exact ⟨s, hs⟩
    · exact Or.inl h3
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K)
    (n := Fintype.card β) h2 hcond
  obtain ⟨e⟩ := nonempty_projectiveSpecialLinearGroup_equiv (K := K) (Fintype.equivFin β)
  haveI : IsSimpleGroup (ProjectiveSpecialLinearGroup β K) := e.isSimpleGroup_congr.mpr hsimple
  obtain ⟨e2⟩ := nonempty_slImage_equiv β K
  exact e2.isSimpleGroup

theorem isSolvable_pgl_of_card_eq_one (h : Fintype.card β = 1) : IsSolvable (PGL β K) := by
  have hcomm : ∀ a b : GL β K, a * b = b * a := by
    intro a b
    obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 h
    letI := hu
    apply Units.ext
    ext i j
    simp only [Units.val_mul, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    exact mul_comm _ _
  refine Group.isSolvable_of_comm fun a b => ?_
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (GL β K)) a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (GL β K)) b
  rw [← map_mul, ← map_mul, hcomm a b]

theorem isSolvable_pgl_of_card_eq_two [Finite K] (h : Fintype.card β = 2) (hK : Nat.card K = 2) :
    IsSolvable (PGL β K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hcardGL : Nat.card (GL β K) = 6 := by
    have e : GL β K ≃* GL (Fin 2) K := Equiv.reindexGL (Fintype.equivFinOfCardEq h) K
    rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field (𝔽 := K) 2, hcardK]
    norm_num [Fin.prod_univ_two]
  haveI : Group.IsSolvable (GL β K) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcardGL]; norm_num)
  have hq : Group.IsSolvable (GL β K ⧸ Subgroup.center (GL β K)) := inferInstance
  exact hq

end CFSG.LieType.BorelTits.RadicalLinear
