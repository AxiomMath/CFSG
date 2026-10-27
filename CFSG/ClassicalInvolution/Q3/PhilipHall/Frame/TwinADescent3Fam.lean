module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Quot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescentSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section SylCent

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_tq_of_sylCent (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) {c : G} {M : Subgroup G}
    (hM : M ∈ Ω) (hT : ∃ T : Subgroup G, IsSylow2In T M ∧ T ≤ Subgroup.centralizer ({c} : Set G)) :
    c ∈ trivialOnQuot M := by
  obtain ⟨T, hTs, hTc⟩ := hT
  have h8 : 8 ≤ Nat.card T :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM hTs)
  have hcT : conjSub c T = T := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp (hTc hx)
      have e : c * x * c⁻¹ = x := by rw [← this]; group
      show c * x * c⁻¹ ∈ T
      rw [e]; exact hx
    · intro x hx
      have := Subgroup.mem_centralizer_singleton_iff.mp (hTc hx)
      refine ⟨x, hx, ?_⟩
      show c * x * c⁻¹ = x
      rw [← this]; group
  have hTMc : T ≤ conjSub c M := by
    have := conjSub_mono (n := c) hTs.1
    rwa [hcT] at this
  have hMM : M = conjSub c M :=
    Sec6Gen.eq_of_le_of_le hΩ hM (hΩ.conjInvariant c M hM) hTs.2.1 (by omega) hTs.1 hTMc
  have hcN : c ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_of_conjSub_eq hMM.symm
  refine ⟨hcN, fun x hx => ?_⟩
  obtain ⟨r, hr, o, ho, rfl⟩ := TwinExact.mem_mul_oddCore_of_sylow (h2 M hM) hTs x hx
  have hcr : c * r * c⁻¹ = r := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hTc hr)
    rw [← this]; group
  have ho' : c * o * c⁻¹ ∈ oddCoreOf M := by
    have := conj_mem_oddCoreIn_of_mem_normalizer hcN (y := o) ho
    exact this
  have hrM : r ∈ M := hTs.1 hr
  have e : ⁅c, r * o⁆ = r * ((c * o * c⁻¹) * o⁻¹) * r⁻¹ := by
    simp only [commutatorElement_def]
    have : c * (r * o) * c⁻¹ = r * (c * o * c⁻¹) := by
      calc c * (r * o) * c⁻¹ = (c * r * c⁻¹) * (c * o * c⁻¹) := by group
        _ = r * (c * o * c⁻¹) := by rw [hcr]
    rw [this]; group
  rw [e]
  have h3 : (c * o * c⁻¹) * o⁻¹ ∈ oddCoreOf M := (oddCoreOf M).mul_mem ho' ((oddCoreOf M).inv_mem ho)
  have h4 := conj_mem_oddCoreOf hrM h3
  have e2 : r * ((c * o * c⁻¹) * o⁻¹) * r⁻¹ = r * ((c * o * c⁻¹) * o⁻¹) * r⁻¹ := rfl
  exact h4

end SylCent

section Conj

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_two_quotient_conjClass {K₀ : Subgroup G}
    (h : IsPGroup 2 (↥K₀ ⧸ classicalInvolutionOddCore ↥K₀)) :
    ∀ M ∈ CoreAssembly.conjClass K₀, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) := by
  rintro _ ⟨g, rfl⟩
  let e : ↥K₀ ≃* ↥(conjSub g K₀) :=
    Subgroup.equivMapOfInjective K₀ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hO : (classicalInvolutionOddCore ↥K₀).map e.toMonoidHom =
      classicalInvolutionOddCore ↥(conjSub g K₀) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  exact h.of_equiv (QuotientGroup.congr _ _ e hO)

end Conj

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem aEmpty_restrict_coreFamily (hΩ : HypOmegaGen Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    ∀ L ∈ restrictFamily (restrictFamily (TwinADescent.coreFamily Ω c)
        (Subgroup.centralizer ({c} : Set G))) X,
      AEmpty (restrictFamily (restrictFamily (TwinADescent.coreFamily Ω c)
        (Subgroup.centralizer ({c} : Set G))) X) L := by
  have hΛ := TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  rintro _ ⟨L₀, hL₀, hL₀X, rfl⟩
  exact Thm4Twin.aEmpty_restrict hΛ (subset_refl _) hL₀X
    (TwinADescent.aEmpty_coreFamily hΩ hΛ hA hc2 L₀ hL₀)

theorem aEmpty_quot_coreFamily (hΩ : HypOmegaGen Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    ∀ M ∈ quotFamily (restrictFamily (restrictFamily (TwinADescent.coreFamily Ω c)
        (Subgroup.centralizer ({c} : Set G))) X) (classicalInvolutionOddCore ↥X),
      AEmpty (quotFamily (restrictFamily (restrictFamily (TwinADescent.coreFamily Ω c)
        (Subgroup.centralizer ({c} : Set G))) X) (classicalInvolutionOddCore ↥X)) M := by
  have hΛ := TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  have hΛX := hypOmegaGen_restrict hΛ X
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  exact TwinADescent2.aEmpty_quotFamily_gen hΛX (TwinEdge.hypOmegaGen_quotFamily_odd hΛX hodd)
    hodd (aEmpty_restrict_coreFamily hΩ hA hc2 X)

end Fam

section SylFam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

@[expose] def sylCoreFamily (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) :=
  {L | ∃ M, (M ∈ Ω ∧ ∃ T : Subgroup G, IsSylow2In T M ∧ T ≤ Subgroup.centralizer ({c} : Set G)) ∧
    L = TwinADescent.coreAt c M}

theorem sylCoreFamily_eq (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    sylCoreFamily Ω c = TwinADescent.coreFamily Ω c := by
  ext L
  constructor
  · rintro ⟨M, ⟨hM, hT⟩, rfl⟩
    exact ⟨M, ⟨hM, mem_tq_of_sylCent hΩ h2 hM hT⟩, rfl⟩
  · rintro ⟨M, ⟨hM, hcM⟩, rfl⟩
    exact ⟨M, ⟨hM, TwinADescent.exists_sylow_centralizer_of_tq hc2 hcM⟩, rfl⟩

end SylFam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3
