module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GAssembly
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GCase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIIFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3

section Defs

@[expose] def FrameNbrTwinSG : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G], Thm3A.Thm3RBelowG (Nat.card G) →
    CIT3Below (Nat.card G) → TL4.TightBelowRPlus 3 (Nat.card G) →
    ∀ (K J : Subgroup G) (z t a g : G), FrameIIHyp K J z t a g →
      ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K

end Defs

section Steps

theorem frameCaseIITGSN_of_namedG (hn : FrameNbrTwinSG) (hC : Frame203Cent)
    (hB : FrameHyp51BG) (hCov : FrameXCover) :
    ∀ (T : Type) [Group T] [Finite T] [FrameSimple T], Thm3A.Thm3RBelowG (Nat.card T) →
      (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) → TL4.TightBelowRPlus 3 (Nat.card T) →
      ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
        ∀ (J : Subgroup T) (zK zJ a g : T),
          AViol (CoreAssembly.conjClass R) R J zK zJ →
          a ∈ pairNormalizers R J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ R →
          conjSub g R = conjSub a J → g * zK * g⁻¹ = zK →
          aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R → False := by
  intro T _ _ _ hT hnab hcit hP R t hdat J zK zJ a g hv ha hac hne hg hgK hs
  have h := frameIIHyp_of_datum hnab hdat hv ha hac hne hg hgK hs
  obtain ⟨K', S, R, R', W, V, d⟩ := std20Frame_of_nbrTwin h (hn T hT hcit hP _ J zK zJ a g h)
  have c4 := frameC204 T _ K' J S R R' W V zK zJ d
  have c5 := frameC205CTG_of_steps (frame20ACentX'_of_cent hC) hB hCov T _ K' J S R R' W V zK zJ d
    hT hcit hP c4
  have c7 := concl20_7_of_cent hC d c5
  have c8 := frameC208 T _ K' J S R R' W V zK zJ d c7
  exact frame10b_false d c8

theorem frameCaseIITGS_of_namedG (hn : FrameNbrTwinSG) (hC : Frame203Cent)
    (hB : FrameHyp51BG) (hCov : FrameXCover) : FrameCaseIITGS := by
  intro T _ _ _ hT hnab hcit hP _ R t hdat J zK zJ a g hv ha hac hne hg hgK hs
  exact frameCaseIITGSN_of_namedG hn hC hB hCov T hT hnab hcit hP R t hdat J zK zJ a g hv ha hac
    hne hg hgK hs

theorem frameCaseIITG_of_nbrTwinG (hn : FrameNbrTwinSG) : FrameCaseIITG :=
  frameCaseIITG_of_S (frameCaseIITGS_of_namedG hn frame203Cent_holds
    (frameHyp51BG_holds_of g2ModelInnerOddFree_holds) frameXCover_holds)

theorem frameCaseIITGN_of_nbrTwinG (hn : FrameNbrTwinSG) :
    ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], Thm3A.Thm3RBelowG (Nat.card T) →
      (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) → TL4.TightBelowRPlus 3 (Nat.card T) →
      ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
        ∀ (J : Subgroup T) (zK zJ a g : T),
          AViol (CoreAssembly.conjClass R) R J zK zJ →
          a ∈ pairNormalizers R J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ R →
          conjSub g R = conjSub a J → g * zK * g⁻¹ = zK →
          aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R → False := by
  intro T _ _ _ hT hnab hcit hP R t hdat J zK zJ a g hv ha hac hne hg hgK hs
  exact frameCaseIITGSN_of_namedG hn frame203Cent_holds
    (frameHyp51BG_holds_of g2ModelInnerOddFree_holds) frameXCover_holds T hT hnab hcit hP R t hdat
    J zK zJ a g hv ha hac hne hg hgK hs

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
