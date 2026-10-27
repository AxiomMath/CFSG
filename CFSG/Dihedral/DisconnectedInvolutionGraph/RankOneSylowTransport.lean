module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneInvolutions
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CommutingInvolutionClosure

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G K : Type*} [Group G] [Group K]

theorem no_commuting_distinct_involutions_of_injective
    (hom : G →* K) (hinjective : Function.Injective hom)
    (hrank : NoCommutingDistinctInvolutions K) : NoCommutingDistinctInvolutions G := by
  intro first second hcommute
  let firstImage : Involution K := ⟨hom first, (orderOf_injective hom hinjective first).trans
    first.property⟩
  let secondImage : Involution K := ⟨hom second, (orderOf_injective hom hinjective second).trans
    second.property⟩
  have himagesCommute : (firstImage : K) * secondImage = (secondImage : K) * firstImage := by
    exact (hom.map_mul first second).symm.trans
      ((congrArg hom hcommute).trans (hom.map_mul second first))
  have hequal := hrank firstImage secondImage himagesCommute
  exact Subtype.ext (hinjective (congrArg Subtype.val hequal))

theorem no_commuting_distinct_involutions_sylow_iff [Finite G]
    (sylow : Sylow 2 G) : NoCommutingDistinctInvolutions G ↔
      NoCommutingDistinctInvolutions (sylow : Subgroup G) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · exact subgroup_no_commuting_distinct_involutions (sylow : Subgroup G)
  · intro hrank first second hcommute
    let closure := Subgroup.closure ({(first : G), (second : G)} : Set G)
    have hpgroup : IsPGroup 2 closure := commuting_involution_closure_isPGroup first second hcommute
    obtain ⟨larger, hle⟩ := hpgroup.exists_le_sylow
    let embedding : closure →* (sylow : Subgroup G) :=
      (Sylow.equiv larger sylow).toMonoidHom.comp (Subgroup.inclusion hle)
    have hinjective : Function.Injective embedding :=
      (Sylow.equiv larger sylow).injective.comp (Subgroup.inclusion_injective hle)
    have hclosureRank := no_commuting_distinct_involutions_of_injective embedding hinjective hrank
    let firstInside : Involution closure :=
      ⟨⟨first, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
        (Subgroup.orderOf_coe _).symm.trans first.property⟩
    let secondInside : Involution closure :=
      ⟨⟨second, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩,
        (Subgroup.orderOf_coe _).symm.trans second.property⟩
    have hequal := hclosureRank firstInside secondInside (Subtype.ext hcommute)
    exact Subtype.ext (congrArg (fun involution : Involution closure => involution.val.val) hequal)

end CFSG.DisconnectedInvolutionGraph.Helpers
