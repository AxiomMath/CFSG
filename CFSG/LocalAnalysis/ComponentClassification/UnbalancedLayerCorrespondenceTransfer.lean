module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG Subgroup

theorem unbalancing_triple_correspondence_transfer {G : Type*} [Group G] [Finite G]
    {a x b : G} {J L : Subgroup G} (hU : GSUnbalancingTriple a x J)
    (hC : UnbalancedGS.GSCorr a J b L) (hbx : b * x = x * b) :
    GSUnbalancingTriple b x L := by
  obtain ⟨-, hbo, hab, -, -, hLb, hL, hbN, hcomm, hfix⟩ := hC
  have hTK : UnbalancedGS.gsFixedLayer J b ≤ L ⊔ conjugate L a := by
    rw [hfix]
    exact (UnbalancedGS.gsFixedLayer_le_inf _ a).trans inf_le_left
  exact unbalancing_orbit_containment_transfer hU hbo hab hbx hbN hcomm hLb hL hTK

end CFSG.ComponentClassification.UnbalancedLayer
