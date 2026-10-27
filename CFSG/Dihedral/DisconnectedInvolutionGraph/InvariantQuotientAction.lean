module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

theorem invariant_subgroup_le_action_comap (subgroup : Subgroup G)
    (hinvariant : InvariantSubgroup (A := A) subgroup) (actor : A) :
    subgroup ≤ subgroup.comap (MulDistribMulAction.toMonoidHom G actor) := by
  intro element hmem
  exact hinvariant actor element hmem

@[expose, instance_reducible]
def invariantQuotientAction (subgroup : Subgroup G) [subgroup.Normal]
    (hinvariant : InvariantSubgroup (A := A) subgroup) :
    MulDistribMulAction A (G ⧸ subgroup) where
  smul actor := QuotientGroup.map subgroup subgroup
    (MulDistribMulAction.toMonoidHom G actor)
    (invariant_subgroup_le_action_comap subgroup hinvariant actor)
  one_smul quotient := by
    obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective subgroup quotient
    change (QuotientGroup.map subgroup subgroup
      (MulDistribMulAction.toMonoidHom G (1 : A)) _) ((QuotientGroup.mk' subgroup) element) = _
    rw [QuotientGroup.map_mk']
    change (QuotientGroup.mk' subgroup) ((1 : A) • element) = _
    rw [one_smul]
  mul_smul first second quotient := by
    obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective subgroup quotient
    change (QuotientGroup.map subgroup subgroup
      (MulDistribMulAction.toMonoidHom G (first * second)) _) _ =
      (QuotientGroup.map subgroup subgroup (MulDistribMulAction.toMonoidHom G first) _)
        ((QuotientGroup.map subgroup subgroup
          (MulDistribMulAction.toMonoidHom G second) _) _)
    simp only [QuotientGroup.map_mk', QuotientGroup.map_mk,
      MulDistribMulAction.toMonoidHom_apply, mul_smul]
  smul_mul actor first second := map_mul _ first second
  smul_one actor := map_one _

theorem invariant_quotient_mk_smul (subgroup : Subgroup G) [subgroup.Normal]
    (hinvariant : InvariantSubgroup (A := A) subgroup) (actor : A) (element : G) :
    let _ := invariantQuotientAction subgroup hinvariant
    actor • (QuotientGroup.mk' subgroup element) = QuotientGroup.mk' subgroup (actor • element) :=
  QuotientGroup.map_mk' subgroup subgroup _ _ element

end CFSG.DisconnectedInvolutionGraph.Helpers
