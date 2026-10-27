module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.AtlasMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Final

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

section Literature

structure Fi3Literature : Type 1 where
  mult23 : Fi23Mult
  mult24 : Fi24Mult
  atlas : FiAtlas
  hyp12 : Hyp12Fi
  lx : Hyp.Hyp31LitX
  tmem22 : TMemOfNotMax [.Fi22] (fun _ => fiLoc 18393661440)
  variantThree : FiVariantThree
  coexist : FiCoexist

end Literature

section Final

theorem fiStage3Main_of_literature (I : Fi3Literature) : FiStage3Main :=
  fiStage3Main_of_atlas
    { mult23 := I.mult23
      mult24 := I.mult24
      atlas := I.atlas
      hyp12 := I.hyp12
      lo := lieModelOrders
      lemma33 := fun IsK IsL H _ _ => lemma33_two IsK IsL H
      hypOne22 := fun _ _ h => HypOne.Fi22.hypothesisOne_of_isSporadic h
      tmem22 := I.tmem22
      lx := I.lx
      variantThree := I.variantThree
      coexist := I.coexist }

end Final

end CFSG.EvenSporadicStandard.Induction.Fi
