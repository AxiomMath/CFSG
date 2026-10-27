module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
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

section Bridge

@[expose] def PrintedWT {G : Type} [Group G] (Ω : Set (Subgroup G)) (K W : Subgroup G) : Prop :=
  ∃ (S : Sylow 2 G) (R : Subgroup G), IsSylow2In R K ∧ R ≤ (S : Subgroup G) ∧ W ∈ WSet Ω ∧
    W ≤ (S : Subgroup G) ∧ (∀ s ∈ (S : Subgroup G), conjSub s W = W) ∧
    ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)

@[expose] def PrintedWTAt {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (W : Subgroup G) : Prop :=
  ∃ R : Subgroup G, IsSylow2In R K ∧ R ≤ (S : Subgroup G) ∧ W ∈ WSet Ω ∧
    W ≤ (S : Subgroup G) ∧ (∀ s ∈ (S : Subgroup G), conjSub s W = W) ∧
    ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)

theorem PrintedWT.exists_at {G : Type} [Group G] {Ω : Set (Subgroup G)} {K W : Subgroup G}
    (h : PrintedWT Ω K W) : ∃ S : Sylow 2 G, PrintedWTAt Ω K S W :=
  h

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

theorem twinThmEPrintedAllT_of_thmEQ8 (hE : ThmEQ8) {n : ℕ} (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TwinCoreHyp n Y R S t → ∀ (K H W : Subgroup Y) (S₀ : Sylow 2 Y),
        K ∈ CoreAssembly.conjClass (tightCore R) →
        PrintedWTAt (CoreAssembly.conjClass (tightCore R)) K S₀ W →
        EHypAll (CoreAssembly.conjClass (tightCore R)) K (S₀ : Subgroup Y) W H → H = ⊤ := by
  intro Y _ _ R S t h K H W S₀ hK hW hH
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := h.hyp
  have hKΩ : K ∈ Ω := hK
  obtain ⟨R₀, hR₀, hR₀S, hWΩ, hWS, hWn, hT⟩ := hW
  obtain ⟨g, rfl⟩ := hK
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
  have hst : EStandQ8 Ω (conjSub g (tightCore R)) S₀ R₀ W :=
    { hyp := hΩ
      cls := (TwinPerp.partIHypG h).cls
      q8 := hq8
      two := h2
      ih := hih
      mem := hKΩ
      aEmpty := TwinPerp.aEmpty_all h _ hKΩ
      twin := hT
      hR := ⟨mem_RSet_of_isSylow2In hKΩ hR₀, hR₀.1, hR₀S⟩
      hW := ⟨hWΩ, hWS, hWn⟩ }
  exact hE Y Ω _ S₀ R₀ W H hst hH

end Bridge

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
