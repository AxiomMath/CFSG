module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3Odd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77.T3Core

section Quot

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {N : Subgroup Y} [N.Normal]

theorem typeRHyp_oddQuot (h : TypeRHyp Φ) (hN : Odd (Nat.card N)) :
    TypeRHyp (quotFamily Φ N) where
  hyp := TwinEdge.hypOmegaGen_quotFamily_odd h.hyp hN
  twoGroup := TwinThmE.two_quot_odd h.twoGroup hN
  sylow := by
    have hq8 : ∀ L ∈ Φ, ∃ P : Subgroup Y, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
      intro L hL
      obtain ⟨P⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
      have hP : IsSylow2In (P.map L.subtype) L := isSylow2In_map_sylow L P
      exact ⟨_, hP, h.sylow L hL _ hP⟩
    have hq := TwinThmE.q8_quot_odd hN hq8
    intro L hL P hP
    obtain ⟨P₀, hP₀, ⟨e⟩⟩ := hq L hL
    obtain ⟨x, -, hx⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP₀ hP
    let e2 : ↥P₀ ≃* ↥(conjSub x P₀) :=
      P₀.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
    exact ⟨(MulEquiv.subgroupCongr hx.symm |>.trans e2.symm).trans e⟩

end Quot

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
