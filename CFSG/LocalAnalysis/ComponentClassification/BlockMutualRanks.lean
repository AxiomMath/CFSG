module

public import CFSG.LocalAnalysis.ComponentClassification.BlockFactorContainment
public import CFSG.LocalAnalysis.ComponentClassification.TwoRankTransport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockMutualRanks

theorem image_factor_normalizer_le {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component) (actor : G) :
    Subgroup.normalizer (UniversalOrbitBlock.conjugate factor actor : Set G) ≤
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom := by
  have hmap := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
    (UniversalOrbitBlock.factor_normalizer_le component heven huniversal hquasisimple factor hfactor)
  rw [Subgroup.map_normalizer_eq_of_bijective factor (MulAut.conj actor).bijective] at hmap
  exact hmap

theorem involution_normalizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (member : G)
    (hmember : member ∈ first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
    (horder : orderOf member = 2) :
    member ∈ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G) := by
  exact BlockFactorContainment.reverse_normalizes component hcontrol actor hactor second hsecond member
    (BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard first hfirst member hmember.1 horder)
    hmember.2

theorem left {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component) :
    pRank 2 (first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G)) =
      pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
  apply le_antisymm
  · exact TwoRankTransport.mono (inf_le_inf_left first
      (image_factor_normalizer_le component heven huniversal hquasisimple second hsecond actor))
  · obtain ⟨elementary, hle, helementary, hcardinal⟩ := TwoRankTransport.witness
      (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
    apply TwoRankTransport.rank_le _ elementary _ helementary _ hcardinal
    intro member hmember
    refine ⟨(hle hmember).1, ?_⟩
    by_cases hone : member = 1
    · rw [hone]
      exact (Subgroup.normalizer _).one_mem
    · exact involution_normalizes component heven huniversal hcard hcontrol first second hfirst hsecond actor hactor
        member (hle hmember) (orderOf_eq_prime (helementary.2 member hmember) hone)

theorem right {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component) :
    pRank 2 (UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)) =
      pRank 2 (UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component) := by
  apply le_antisymm
  · exact TwoRankTransport.mono (inf_le_inf_left _
      (UniversalOrbitBlock.factor_normalizer_le component heven huniversal hquasisimple first hfirst))
  · obtain ⟨elementary, hle, helementary, hcardinal⟩ := TwoRankTransport.witness
      (UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)
    apply TwoRankTransport.rank_le _ elementary _ helementary _ hcardinal
    intro member hmember
    refine ⟨(hle hmember).1, ?_⟩
    by_cases hone : member = 1
    · rw [hone]
      exact (Subgroup.normalizer _).one_mem
    · obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp (hle hmember).1
      have horder : orderOf member = 2 := orderOf_eq_prime (helementary.2 member hmember) hone
      have horiginalOrder : orderOf original = 2 :=
        (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
          ((congrArg orderOf heq).trans horder)
      have horiginalFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard second hsecond
        original horiginal horiginalOrder
      have heq' : (MulAut.conj actor) original = member := heq
      have himageNormalizer : (MulAut.conj actor) original ∈ UniversalOrbitBlock.normalizer component := by
        rw [heq']
        exact (hle hmember).2
      have hfixed := hcontrol original horiginalFusion actor hactor himageNormalizer first hfirst
      rw [heq'] at hfixed
      exact (CommutingComponentFamily.normalizer_iff_conjugate_eq first member).mpr hfixed

theorem image_involution_normalizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (member : G)
    (hmember : member ∈ UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)
    (horder : orderOf member = 2) : member ∈ Subgroup.normalizer (first : Set G) := by
  obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hmember.1
  have horiginalOrder : orderOf original = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
      ((congrArg orderOf heq).trans horder)
  have horiginalFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard second hsecond
    original horiginal horiginalOrder
  have heq' : (MulAut.conj actor) original = member := heq
  have himageNormalizer : (MulAut.conj actor) original ∈ UniversalOrbitBlock.normalizer component := by
    rw [heq']
    exact hmember.2
  have hfixed := hcontrol original horiginalFusion actor hactor himageNormalizer first hfirst
  rw [heq'] at hfixed
  exact (CommutingComponentFamily.normalizer_iff_conjugate_eq first member).mpr hfixed

end CFSG.ComponentClassification.BlockMutualRanks
