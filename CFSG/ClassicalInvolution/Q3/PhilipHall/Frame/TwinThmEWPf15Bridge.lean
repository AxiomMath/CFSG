module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEApply
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpClass

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinThmEW

section Consumers


open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

@[expose] def WFreeToAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), EStandQ8 Ω K S R W → EHyp Ω K W H → EHypAll Ω K (S : Subgroup G) W H

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

theorem twinThmE_of_thmEQ8W (hE : ThmEQ8) (hX : WFreeToAll) {n : ℕ} (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) : TwinDisc.TwinThmE n := by
  intro Y _ _ R S t h K H hK hH
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := h.hyp
  have hKΩ : K ∈ Ω := hK
  obtain ⟨K₀', hK₀', hne₀⟩ := h.twin
  obtain ⟨g, rfl⟩ := hK
  have hK'Ω : conjSub g K₀' ∈ Ω := hΩ.conjInvariant g K₀' hK₀'.1
  have htw : conjSub g K₀' ∈ twinSet Ω (conjSub g (tightCore R)) := by
    obtain ⟨-, z, hz, hz'⟩ := hK₀'
    exact ⟨hK'Ω, g * z * g⁻¹, hz.conj g, hz'.conj g⟩
  have hne : conjSub g K₀' ≠ conjSub g (tightCore R) := by
    intro he
    apply hne₀
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hq8 : ∀ L ∈ Ω, ∃ P : Subgroup Y, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
    rintro _ ⟨g', rfl⟩
    obtain ⟨P, hP', ⟨e⟩⟩ := h.datum.exists_sylow_q8 h.q8
    exact ⟨conjSub g' P, hP'.conj g', ⟨(Subgroup.equivMapOfInjective P (MulAut.conj g').toMonoidHom
      (MulAut.conj g').injective).symm.trans e⟩⟩
  have h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) := by
    rintro _ ⟨g', rfl⟩
    have h0 := TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) h.datum.twoGroup
    let φ : ↥(tightCore R) ≃* ↥(conjSub g' (tightCore R)) :=
      Subgroup.equivMapOfInjective _ (MulAut.conj g').toMonoidHom (MulAut.conj g').injective
    exact h0.of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ))
  have hih : EIH (Nat.card Y) := by
    rw [h.card]
    exact ⟨hcit, hP⟩
  obtain ⟨S', R', W', hst⟩ := exists_estandQ8 hΩ (TwinPerp.partIHypG h).cls hq8 h2 hih hKΩ
    (TwinPerp.aEmpty_all h _ hKΩ) htw hne
  exact hE Y Ω _ S' R' W' H hst (hX Y Ω _ S' R' W' H hst ⟨hH.trans, hH.cent⟩)

theorem twinThmEP_of_thmEQ8W (hE : ThmEQ8) (hX : WFreeToAll) (n : ℕ) : TwinThmEP n :=
  fun hcit hP => twinThmE_of_thmEQ8W hE hX hcit hP

end Consumers

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
