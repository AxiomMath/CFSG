module

public import CFSG.GH74.QTGen4.Recog.G23.Native
public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.GH74.QTGen4.Recog.G23

section Simplicity

theorem ghat_simple : IsSimpleGroup Ghat := by
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, one_pos⟩
  have hq : q.card = 3 := by rw [TauCeti.PrimePower.card_def]; rfl
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
      exact hq.symm.le
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  exact CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_G2 q hv (ZMod 3)
    (by rw [hq, Nat.card_zmod])

end Simplicity

set_option maxHeartbeats 400000 in
theorem not_isSolvable_SL32 : ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  intro hs
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let f : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    e.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
  have hf : Function.Surjective f :=
    e.surjective.comp CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two.2
  have hsolv : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :=
    Group.isSolvable_of_surjective hf
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h4 : 4 ≤ (Finset.univ : Finset (ZMod 7)).card := by
    rw [Finset.card_univ, ZMod.card]
    norm_num
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
  have hperf : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :=
    CFSG.LinearGroups.linear_projective_perfect (by norm_num) (Or.inr ⟨t, ht⟩)
  have hnt : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :=
    CFSG.LinearGroups.linear_projective_nontrivial (by norm_num)
  exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect hsolv

end CFSG.GH74.QTGen4.Recog.G23
