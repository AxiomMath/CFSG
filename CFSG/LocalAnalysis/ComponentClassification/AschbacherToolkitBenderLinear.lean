module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

open CFSG.Open
open scoped MatrixGroups

theorem le_sylowCenter_of_card {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    (hcard : Nat.card (sylowCenter T) = Nat.card T) : T ≤ sylowCenter T := by
  have heq : sylowCenter T = T :=
    Subgroup.eq_of_le_of_card_ge (sylowCenter_le T) hcard.ge
  exact heq.ge

theorem nestedAt_of_benderBorel_rank_one {X : Type*} [Group X] [Finite X] {q : ℕ}
    (h : fusionBenderBorel X q 1) (T : Sylow 2 X) : NestedAt (T : Subgroup X) := by
  obtain ⟨hSE, hZ2, hZcard, hTcard⟩ := benderBorel_sylowCenter h T
  exact nestedAt_of_abelian hSE hZ2
    (le_sylowCenter_of_card (by rw [hZcard, hTcard, pow_one]))

theorem nestedAt_of_mulEquiv_psl2 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSL(2, GaloisField 2 f)) (T : Sylow 2 X) : NestedAt (T : Subgroup X) := by
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
  exact nestedAt_of_mulEquiv e (nestedAt_of_benderBorel_rank_one
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f hf)) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
