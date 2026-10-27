module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)

open scoped commutatorElement

private theorem i1431_char_prime (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp <;> first | exact ‹TauCeti.PrimePower›.prime_p | exact Nat.prime_two | exact Nat.prime_three

private theorem i1431_catalogIs_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs T Q) : catalogIs S Q :=
  let ⟨i, hi, ⟨f⟩⟩ := h
  ⟨i, hi, ⟨e.trans f⟩⟩

end CFSG.LocalAnalysis.GLTheoremA

end
