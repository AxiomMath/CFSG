module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.AtlasFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3MainL
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Real
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Real2

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

section Literature


structure Fi3LiteratureV3 : Type 1 where
  mult23 : Fi23Mult
  mult24 : Fi24Mult
  atlas : FiAtlas
  hyp12 : Hyp12Fi
  lx : Hyp.Hyp31LitX
  tmem22 : TMemOfNotMax [.Fi22] (fun _ => fiLoc 18393661440)
  selfCent : V3.Fi23SelfCentralizing
  autSolv : V3.Fi23TranspositionAut
  fixed : V3.Fi23InvolutionFixed
  coexistMax : V3.FiCoexistMax
  outerInv : V3.FiOuterInvolution

end Literature

section Final


theorem fiStage3Main_of_literatureV3 (I : Fi3LiteratureV3) : FiStage3Main := by
  have hpf : FiPinned := fiPinned_of_mult I.mult23 I.mult24 I.atlas
  have hv3 : V3.FiV3RowInputs :=
    { basic :=
        { pinned := hpf
          order23 := V3.fi23Order_real
          selfCent := I.selfCent
          outerFixed := V3.fi24OuterFixed_real }
      rows :=
        { thm24 := pinThm24Hex24 lieModelOrders
          transpositions := V3.fi23Transpositions_real
          autSolv := I.autSolv
          fixed := I.fixed }
      lx := I.lx.oddLie
      outerInv := I.outerInv }
  exact fiStage3Main_of_literature
    { mult23 := I.mult23
      mult24 := I.mult24
      atlas := I.atlas
      hyp12 := I.hyp12
      lx := I.lx
      tmem22 := I.tmem22
      variantThree := V3.fiVariantThree_of_rowInputs hv3
      coexist := V3.fiCoexist_of_rowInputs hv3 I.coexistMax }

end Final

end CFSG.EvenSporadicStandard.Induction.Fi
