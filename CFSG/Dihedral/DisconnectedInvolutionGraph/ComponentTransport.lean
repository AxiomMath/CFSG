module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.ComponentAction
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CrossingInvolutions

public section

open CFSG.Open

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

abbrev ComponentInvolutions (component : InvolutionComponent G) :=
  {involution : Involution G // involutionComponent involution = component}

abbrev TransportingInvolutions (source target : InvolutionComponent G) :=
  {involution : Involution G // (involution : G) • source = target}

noncomputable def componentInvolutionsConjugationEquiv (g : G)
    (component : InvolutionComponent G) :
    ComponentInvolutions component ≃ ComponentInvolutions (g • component) where
  toFun involution := ⟨conjugateInvolution g involution.val, by
    rw [← smul_involutionComponent, involution.property]⟩
  invFun involution := ⟨conjugateInvolution g⁻¹ involution.val, by
    rw [← smul_involutionComponent, involution.property, inv_smul_smul]⟩
  left_inv involution := by
    apply Subtype.ext
    change conjugateInvolution g⁻¹ (conjugateInvolution g involution.val) = involution.val
    rw [← conjugateInvolution_mul, inv_mul_cancel, conjugateInvolution_one]
  right_inv involution := by
    apply Subtype.ext
    change conjugateInvolution g (conjugateInvolution g⁻¹ involution.val) = involution.val
    rw [← conjugateInvolution_mul, mul_inv_cancel, conjugateInvolution_one]

theorem component_involution_card_eq [Finite G] (source target : InvolutionComponent G) :
    Nat.card (ComponentInvolutions source) = Nat.card (ComponentInvolutions target) := by
  obtain ⟨g, htransport⟩ := MulAction.exists_smul_eq G source target
  rw [← htransport]
  exact Nat.card_congr (componentInvolutionsConjugationEquiv g source)

theorem transporting_involution_outside (base : Involution G)
    (target : InvolutionComponent G) (hne : target ≠ involutionComponent base)
    (involution : Involution G)
    (htransport : (involution : G) • involutionComponent base = target) :
    (involution : G) ∉ componentStabilizer base := by
  intro hmem
  rw [componentStabilizer_eq_stabilizer, MulAction.mem_stabilizer_iff] at hmem
  exact hne (htransport.symm.trans hmem)

def componentTransportMap (base : Involution G) (target : InvolutionComponent G) :
    TransportingInvolutions (involutionComponent base) target → ComponentInvolutions target :=
  fun involution => ⟨conjugateInvolution (involution.val : G) base, by
    rw [← smul_involutionComponent]
    exact involution.property⟩

theorem componentTransportMap_bijective [Finite G] (base : Involution G)
    (target : InvolutionComponent G) (hne : target ≠ involutionComponent base)
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    Function.Bijective (componentTransportMap base target) := by
  have hstrong := componentStabilizer_stronglyEmbedded base hdisc
  constructor
  · intro first second heq
    have hfirst := transporting_involution_outside base target hne first.val first.property
    have hsecond := transporting_involution_outside base target hne second.val second.property
    have hvalue : conjugateInvolution (first.val : G) base =
        conjugateInvolution (second.val : G) base :=
      congrArg (fun involution : ComponentInvolutions target => involution.val) heq
    have hconj : outsideInvolutionConjugation (componentStabilizer base) hstrong base
        (componentStabilizer_base_mem base) ⟨first.val, hfirst⟩ =
        outsideInvolutionConjugation (componentStabilizer base) hstrong base
        (componentStabilizer_base_mem base) ⟨second.val, hsecond⟩ :=
      Subtype.ext hvalue
    exact Subtype.ext (congrArg (fun involution : OutsideInvolution
      (componentStabilizer base) => involution.val)
      ((outsideInvolutionConjugation_bijective (componentStabilizer base) hstrong base
        (componentStabilizer_base_mem base)).1 hconj))
  · intro involution
    have houtside : (involution.val : G) ∉ componentStabilizer base := by
      intro hmem
      have hcomponent : involutionComponent base = involutionComponent involution.val :=
        SimpleGraph.ConnectedComponent.sound ((componentStabilizer_involution_iff
          base involution.val).mp hmem)
      exact hne (involution.property.symm.trans hcomponent.symm)
    obtain ⟨conjugator, _, _, hconj⟩ := stronglyEmbedded_crossing_involution_conjugates
      (componentStabilizer base) hstrong base involution.val (componentStabilizer_base_mem base)
      houtside
    have htransport : (conjugator : G) • involutionComponent base = target := by
      rw [smul_involutionComponent, hconj]
      exact involution.property
    exact ⟨⟨conjugator, htransport⟩, Subtype.ext hconj⟩

noncomputable def componentFixedInvolutionsEquiv [Finite G] (base : Involution G) :
    TransportingInvolutions (involutionComponent base) (involutionComponent base) ≃
      ComponentInvolutions (involutionComponent base) where
  toFun involution := ⟨involution.val,
    (involution_fixes_component_iff involution.val base).mp involution.property⟩
  invFun involution := ⟨involution.val,
    (involution_fixes_component_iff involution.val base).mpr involution.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem component_transport_involution_card [Finite G] (source target : InvolutionComponent G)
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    Nat.card (TransportingInvolutions source target) = Nat.card (ComponentInvolutions source) := by
  classical
  obtain ⟨base, rfl⟩ := involutionComponent_surjective source
  by_cases heq : target = involutionComponent base
  · rw [heq]
    exact Nat.card_congr (componentFixedInvolutionsEquiv base)
  · rw [Nat.card_congr (Equiv.ofBijective (componentTransportMap base target)
      (componentTransportMap_bijective base target heq hdisc))]
    exact component_involution_card_eq target (involutionComponent base)

theorem exists_involution_transports_component [Finite G] (source target : InvolutionComponent G)
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    ∃ involution : Involution G, (involution : G) • source = target := by
  classical
  obtain ⟨base, rfl⟩ := involutionComponent_surjective source
  by_cases heq : target = involutionComponent base
  · exact ⟨base, heq ▸ (involution_fixes_component_iff base base).mpr rfl⟩
  · obtain ⟨other, hother⟩ := involutionComponent_surjective target
    obtain ⟨preimage, hpreimage⟩ := (componentTransportMap_bijective base target heq hdisc).2
      ⟨other, hother⟩
    exact ⟨preimage.val, preimage.property⟩

end CFSG.DisconnectedInvolutionGraph.Helpers
