module

public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarNormal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameSimple
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51D4A
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Uniform CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D

section Rows

variable {T : Type} [Group T]

abbrev SecQuot (H : Subgroup T) : Type := ↥H ⧸ classicalInvolutionOddCore ↥H

end Rows

section Case

structure FrameCaseIHyps (T : Type) [Group T] [Finite T] (R : Subgroup T) (t : T)
    (J : Subgroup T) (zK zJ : T) : Prop where
  nonabelian : ∃ a b : T, a * b ≠ b * a
  cit : CIT3Below (Nat.card T)
  pkg : TL4.TightBelowRPlus 3 (Nat.card T)
  datum : FrameTightDatum R t
  viol : AViol (CoreAssembly.conjClass R) R J zK zJ
  ne : aStar (CoreAssembly.conjClass R) R ≠ CoreAssembly.conjClass R

end Case

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
