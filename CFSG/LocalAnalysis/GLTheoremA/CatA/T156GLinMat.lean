module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearMat
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Lin

open CFSG.Assembly CFSG.StandardType

abbrev SLOK (d : ℕ) (F : Type) : Prop :=
  3 ≤ d ∨ ∃ s : Finset F, s.card = 4

theorem slOK_of_card {d : ℕ} {F : Type} [Finite F] (h : 4 ≤ Nat.card F) : SLOK d F := by
  have := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
  exact Or.inr ⟨s, hs⟩

theorem slOK_of_two_pow {d : ℕ} {F : Type} [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ^ m) : SLOK d F := by
  refine slOK_of_card ?_
  rw [hF]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

variable {d : ℕ}

theorem commutator_slGroup' {F : Type} [Field F] (hd : 2 ≤ d) (h : SLOK d F) :
    ⁅LargeEvenSLGroup (Fin d) F, LargeEvenSLGroup (Fin d) F⁆ = LargeEvenSLGroup (Fin d) F := by
  haveI hP : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin d) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := d) hd h
  have hP' : Group.IsPerfect (↥(LargeEvenSLGroup (Fin d) F)) :=
    Group.IsPerfect.ofSurjective (f := (TypeA.slKerEquiv d F).symm.toMonoidHom)
      (TypeA.slKerEquiv d F).symm.surjective
  exact (Subgroup.isPerfect_iff (H := LargeEvenSLGroup (Fin d) F)).1 hP'

theorem isSimpleGroup_proj' (hd : 2 ≤ d) (F : Type) [Field F] (h : SLOK d F) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin d) F) :=
    (CFSG.LinearGroups.linear_projective_simple (K := F) (n := d) hd h).2.1
  exact MulEquiv.isSimpleGroup
    ((TypeA.recipeEquiv d F).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        d F).symm)

theorem exists_noncomm_proj' (hd : 2 ≤ d) (F : Type) [Field F] (h : SLOK d F) :
    ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin d) F), a * b ≠ b * a := by
  let e : LargeEvenProj (LargeEvenSLGroup (Fin d) F) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin d) F :=
    (TypeA.recipeEquiv d F).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        d F).symm
  haveI : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin d) F) :=
    CFSG.LinearGroups.linear_projective_perfect (K := F) (n := d) hd h
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Nontrivial (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) :=
    (isSimpleGroup_proj' hd F h).toNontrivial
  by_contra hc
  push Not at hc
  haveI : IsMulCommutative (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) :=
    IsMulCommutative.of_comm hc
  exact Group.IsPerfect.not_isMulCommutative (LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    inferInstance

end CFSG.LocalAnalysis.GLTheoremA.T156.Lin

end
