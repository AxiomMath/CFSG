module

public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoOddDisplacement
public import CFSG.LocalAnalysis.ComponentClassification.BlockFactorCenter

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCentralSylowCommutation

theorem centralizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (first second acting : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (htwo : IsPGroup 2 acting) (hcontained : acting ≤ first)
    (hcentral : acting ≤ (Subgroup.center first).map first.subtype)
    (hnormalizes : acting ≤ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G)) :
    UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component ≤
      Subgroup.centralizer (acting : Set G) := by
  intro moving hmoving
  have hmovingNormalizes := (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple
    moving).mp hmoving.2
  have hfactorMoved := hmovingNormalizes first hfirst
  have hodd : Odd (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓
      (first ⊔ first.map (MulAut.conj moving).toMonoidHom))) := by
    have hintersection := BlockProductFusion.intersection_odd component heven huniversal hquasisimple hcard
      first (UniversalOrbitBlock.conjugate first moving) second second hfirst hfactorMoved hsecond hsecond actor hactor
    change Odd (Nat.card ↥((first ⊔ first.map (MulAut.conj moving).toMonoidHom) ⊓
      (UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate second actor))) at hintersection
    simpa only [sup_idem, inf_comm] using hintersection
  exact CentralTwoOddDisplacement.centralizes (UniversalOrbitBlock.generated component) first
    (UniversalOrbitBlock.conjugate second actor) acting htwo hcontained
      (hcentral.trans (BlockFactorCenter.generated component heven huniversal first hfirst)) hnormalizes moving hmoving.1
        hmoving.2 hodd

end CFSG.ComponentClassification.BlockCentralSylowCommutation
