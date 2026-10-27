module

public import CFSG.HardMathSupport.Foote.E27.Alt
public import CFSG.HardMathSupport.Foote.E27.Lie
public import CFSG.HardMathSupport.Foote.Proving.E27SporAtTh
public import CFSG.HardMathSupport.Foote.E27.SporCo1

public section

namespace CFSG.HardMathSupport.Foote.E27

set_option linter.unusedSectionVars false

open CFSG.HardMathSupport.Foote.Proving



theorem kFactMSideAlmostSimpleE27_of_open (hIn : E27LieIn) (hOut : E27LieOut)
    (hCo1 : E27SporAt .Co1) (hM : E27SporAt .M) :
    CFSG.AGLEmbedding.KFactMSideAlmostSimpleE27 :=
  kFactMSideAlmostSimpleE27_of_slices e27AltSlice (e27LieSlice_of_in_out hIn hOut)
      (e27SporSlice_of_big
          (e27SporBig_of_open hCo1
              (e27SporAt_th (CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .Th)) hM))

theorem e27SporAt_co1 (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Co1 ≃*
    (TauCeti.CFSGIndex.sporadic .Co1).Group)) : E27SporAt .Co1 :=
  fun _ _ _ _ _ _ _ hc hz e => hc.false_of_sporadic_co1 hz hbr e.some

theorem kFactMSideAlmostSimpleE27_of_lie_monster (hIn : E27LieIn) (hOut : E27LieOut)
    (hM : E27SporAt .M) : CFSG.AGLEmbedding.KFactMSideAlmostSimpleE27 :=
  kFactMSideAlmostSimpleE27_of_open hIn hOut
    (e27SporAt_co1 (CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .Co1)) hM

end CFSG.HardMathSupport.Foote.E27
