module

public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocPlus
public import CFSG.LargeExtraspecial.S14W4LocE8
public import CFSG.LargeExtraspecial.S12InspUse

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G]

namespace W4Hyp

variable {S : Setting G} {g : G} {t : S.O} {c : Config} (h : W4Hyp S g t c)
include h

theorem false_of_minus [IsSimpleGroup G] (hM8 : W4Loc.WeaklyClosedE8Stmt)
    (hRI : RootInvolutionComponentsInput.{0}) (hARS : CFSG.Timmesfeld.ARSInput)
    (hTri : FischerTrialityInput) (hFischer : S12FischerStatement)
    (hInsp : Insp4Input) (h36 : Timmesfeld36Input)
    (hSL : S12SL4ModuleInput) (hTI : WeaklyClosedTITransitive.{0}) (hNQ : NQIrredStmt)
    (hNQ6 : NQPlus6Stmt) (hm : c = .omegaMinus6) {g₀ : ↥(Mbar0 S)}
    (ha : g₀ * h.S₀.z * g₀⁻¹ ∈ h.S₀.QG) (hne : g₀ * h.S₀.z * g₀⁻¹ ≠ h.S₀.z) : False := by
  have : IsSimpleGroup ↥(Mbar0 S) := h.simple
  have : FiniteDimensional (ZMod 2) (Vt S g t) := Module.Finite.of_finite
  exact W4Loc.false_of_minus_of_insp4 hM8 hRI hARS hTri hFischer hInsp h36 hSL hTI h.act
    h.card_Qt (h.irr hNQ hm) h.finrank_Vt h.qf_nondeg h.πR_eq h.π_mem_O (h.not_isPlus hm)
    (fun P hP => h.card_le_of_isPGroup hNQ hNQ6 P hP) h.width_S₀ ha hne

theorem not_omegaPlusEight [IsSimpleGroup G] (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt) :
    ¬ h.S₀.S12OmegaPlusEight := fun h8 =>
  W4Loc.false_of_two_pow_dvd (fun P hP => h.card_le_of_isPGroup hNQ hNQ6 P hP)
    (W4Loc.two_pow_dvd_of_omegaPlusEight h.S₀ h8)

theorem not_spSixSpin [IsSimpleGroup G] (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt)
    (g₀ : ↥(Mbar0 S)) : ¬ h.S₀.S12SpSixSpin g₀ := fun hSp =>
  W4Loc.false_of_two_pow_dvd (fun P hP => h.card_le_of_isPGroup hNQ hNQ6 P hP)
    (W4Loc.two_pow_dvd_of_spSixSpin h.S₀ hSp)

theorem false_of_noA2
    [IsSimpleGroup G] (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt)
    (hTI : WeaklyClosedTITransitive.{0}) {g₀ : ↥(Mbar0 S)} (ha : g₀ * h.S₀.z * g₀⁻¹ ∈ h.S₀.QG)
    (hne : g₀ * h.S₀.z * g₀⁻¹ ≠ h.S₀.z) (hno : ¬ h.S₀.HasTypeAInL g₀)
    (hirr : ¬ h.S₀.IsReducible) : False := by
  have : FiniteDimensional (ZMod 2) (Vt S g t) := Module.Finite.of_finite
  have hn : 4 ≤ h.S₀.width := le_of_eq h.width_S₀.symm
  have C := W4Loc.cons311_of_w4 hTI hn ha hne hno hirr
  rcases h.hc with hm | hp
  · exact h.not_isPlus hm (W4Loc.isPlus_of_cons311 W4Loc.weaklyClosedE8Stmt h.act h.card_Qt
      (h.lat hNQ hNQ6) h.finrank_Vt h.qf_nondeg h.πR_eq h.π_mem_O ha C h.width_S₀)
  · have H := W4Loc.hyp4_of_w4 hTI hn ha hne hno hirr
    have hlat := h.lattice hNQ6 hp
    exact hlat.elim fun W₁ hW => hW.elim fun W₂ hW₂ =>
      W4Loc.false_of_cons311_plus W4Loc.weaklyClosedE8Stmt h.act h.card_Qt h.finrank_Vt
        h.qf_nondeg h.πR_eq h.π_mem_O hW₂.1 hW₂.2.1 hW₂.2.2.1 hW₂.2.2.2.1 hW₂.2.2.2.2.1
        hW₂.2.2.2.2.2 H C h.width_S₀

end W4Hyp

end CFSG.LargeExtraspecial.S14
