module

public import CFSG.LieType.Simplicity.Classical
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.CGT.PushingUp.Defs
public import CFSG.CGT.Timmesfeld75.SLTransvection
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.CGT.PushingUpLit.STT

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)

section ListNonabelian

variable {G : Type} [Group G]

theorem not_forall_comm_of_psl {m s : ℕ} (hm : 2 ≤ m) (h : StatedClassicalModel G .PSL m 2 s) :
    ¬ ∀ a b : G, a * b = b * a := by
  intro hcomm
  obtain ⟨hnt, -⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity G m 2 s h
  obtain ⟨⟨hp, hf, hn, h22, h23⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) K) := by
    by_cases h3 : 3 ≤ m
    · exact CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le h3
    · have hm2 : m = 2 := by omega
      subst hm2
      refine CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K ?_
      by_contra hlt
      have h2s : 2 ^ s ≤ 3 := by omega
      have hs : 1 ≤ s := hf
      have : s = 1 := by
        by_contra hne
        have : 2 ≤ s := by omega
        have : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) this
        omega
      subst this
      exact h22 (by norm_num)
  let ePSL : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin m) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj m K).symm
  have hPSL : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin m) K) := by
    unfold Matrix.ProjectiveSpecialLinearGroup
    infer_instance
  have hG : Group.IsPerfect G :=
    Group.IsPerfect.ofSurjective (f := ePSL.symm.toMonoidHom) ePSL.symm.surjective
  exact Group.IsPerfect.not_isMulCommutative (G := G) ⟨⟨hcomm⟩⟩

theorem not_forall_comm_of_equiv {H : Type} [Group H] (e : G ≃* H)
    (hH : ∃ x y : H, x * y ≠ y * x) : ¬ ∀ a b : G, a * b = b * a := by
  intro hcomm
  obtain ⟨x, y, hxy⟩ := hH
  apply hxy
  have h2 := congrArg e (hcomm (e.symm x) (e.symm y))
  simpa using h2

theorem m22_noncomm : ∃ x y : ↥CFSG.Blueprint.NativeSporadic.M22, x * y ≠ y * x := by
  unfold CFSG.Blueprint.NativeSporadic.M22
  refine ⟨⟨_, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
    ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  revert this
  decide +kernel

theorem m23_noncomm : ∃ x y : ↥CFSG.Blueprint.NativeSporadic.M23, x * y ≠ y * x := by
  unfold CFSG.Blueprint.NativeSporadic.M23
  refine ⟨⟨_, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
    ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  revert this
  decide +kernel

theorem m24_noncomm : ∃ x y : ↥CFSG.Blueprint.NativeSporadic.M24, x * y ≠ y * x := by
  unfold CFSG.Blueprint.NativeSporadic.M24
  refine ⟨⟨_, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
    ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  revert this
  decide +kernel

end ListNonabelian

end CFSG.CGT.PushingUpLit.STT
