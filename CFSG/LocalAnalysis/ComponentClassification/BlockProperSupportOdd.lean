module

public import CFSG.LocalAnalysis.ComponentClassification.BlockFactorInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.MappedCenter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockProperSupportOdd

@[expose] noncomputable def subgroup {G : Type*} [Group G] (component : Subgroup G) (subset : Set (Subgroup G)) : Subgroup G :=
  sSup subset ⊔ (Subgroup.center (UniversalOrbitBlock.generated component)).map
    (UniversalOrbitBlock.generated component).subtype

theorem centralizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (subset : Set (Subgroup G)) (hsubset : subset ⊆ UniversalOrbitBlock.block component)
    (unused : Subgroup G) (hunused : unused ∈ UniversalOrbitBlock.block component) (hnot : unused ∉ subset) :
    subgroup component subset ≤ Subgroup.centralizer (unused : Set G) := by
  apply sup_le
  · apply sSup_le
    intro factor hfactor
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (UniversalOrbitBlock.block_commutes component heven huniversal factor (hsubset hfactor) unused hunused
        (by intro heq; subst factor; exact hnot hfactor))
  · exact (MappedCenter.centralizes (UniversalOrbitBlock.generated component)).trans
      (Subgroup.centralizer_le (CommutingComponentFamily.factor_le _ unused hunused))

theorem odd {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (subset : Set (Subgroup G))
    (hsubset : subset ⊆ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor))
    (unused : Subgroup G) (hunused : unused ∈ UniversalOrbitBlock.block component)
    (hnot : UniversalOrbitBlock.conjugate unused actor ∉ subset) :
    Odd (Nat.card ↥(first ⊓ subgroup (UniversalOrbitBlock.conjugate component actor) subset)) := by
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hcentralizes := centralizes (UniversalOrbitBlock.conjugate component actor)
    (UniversalOrbitBlock.orbit_even component heven _ horbit) (UniversalOrbitBlock.orbit_universal component huniversal _ horbit)
      subset hsubset (UniversalOrbitBlock.conjugate unused actor) ((OrbitBlockConjugation.block component unused actor).mpr hunused) hnot
  apply Nat.not_even_iff_odd.mp
  intro hevenIntersection
  let intersection := first ⊓ subgroup (UniversalOrbitBlock.conjugate component actor) subset
  obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' (G := intersection) 2 (even_iff_two_dvd.mp hevenIntersection)
  have horderAmbient : orderOf member.val = 2 :=
    (orderOf_injective intersection.subtype intersection.subtype_injective member).trans horder
  obtain ⟨_, factor, hfactor, hcentral⟩ := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard
    first hfirst member.val member.property.1 horderAmbient
  exact hactor (BlockFusion.common_involution_forces_normalizer component heven huniversal hquasisimple
    unused factor hunused hfactor actor member.val horderAmbient (hcentralizes member.property.2) hcentral)

end CFSG.ComponentClassification.BlockProperSupportOdd
