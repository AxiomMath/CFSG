module

public import CFSG.GH74.Uniqueness.Section4Prop44
public import CFSG.GH74.Uniqueness.Bender.OuterFinal

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem benderOuterInvolution :
    BenderOuterInvolution :=
  fun _ _ _ hK α hα hout => Bender.bender_outer_involution hK α hα hout

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.theorem1 (hB : BenderFacts) (S : ZDSetup X Z M) :
    IsSimpleGroup X ∧ IsStronglyZEmbedded Z M ∧ (∃ z ∈ Z, Z = {y : X | IsConj z y}) ∧
      ∀ z ∈ Z, IsCentralInvolution z := by
  have h45 := S.no_solvable_normal hB
  have h44 : ∀ H : Subgroup X, H ≠ ⊤ → ¬ H ≤ M → (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty →
      IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H)) :=
    fun H hH hHM hne => S.prop44 hB h45 hH hHM hne
  obtain ⟨z, hz, -⟩ := S.exists_mem_inter
  refine ⟨S.isSimpleGroup h45 h44, ⟨S.prodDisc.1, S.prodDisc.2.1,
    fun z hz hzM => S.prodDisc.centralizer_le_of_mem hz hzM, S.exists_controlsFusion,
    fun H hH hne hHM => h44 H hH hHM hne⟩, ⟨z, hz, S.eq_conjClass hz⟩,
    fun z hz => S.isCentralInvolution hz⟩

theorem ZDSetup.theorem1_of_cover
    (hCover : BenderCoverRigid) (S : ZDSetup X Z M) :
    IsSimpleGroup X ∧ IsStronglyZEmbedded Z M ∧ (∃ z ∈ Z, Z = {y : X | IsConj z y}) ∧
      ∀ z ∈ Z, IsCentralInvolution z :=
  S.theorem1 ⟨hCover, benderOuterInvolution⟩

end CFSG.GH74.Uniqueness
