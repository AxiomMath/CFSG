module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.EngRowFacts

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem mem_fiTypes_of (s : TauCeti.SporadicName)
    (h : s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime) : s ∈ fiTypes := by
  rcases h with rfl | rfl | rfl <;> simp [fiTypes]

theorem FiHyp31.mono {IsK : GroupClass} {S A A' Up : List TauCeti.SporadicName}
    (hAA' : ∀ s ∈ A, s ∈ A') (h : FiHyp31 IsK S A Up) : FiHyp31 IsK S A' Up :=
  fun lit hrow H _ _ ih => h lit hrow H (BelowSec.mono_types hAA' ih)

structure Fi3RowInputs : Type 1 where
  pinned : FiPinned
  lemma33 : ∀ (IsK IsL : GroupClass) (H : Type) [Group H] [Finite H], Lemma33Two IsK IsL H
  hypOne22 : ∀ (Y : Type) [Group Y], IsSporadic Y .Fi22 → HypothesisOne Y
  tmem22 : TMemOfNotMax [.Fi22] (fun _ => fiLoc 18393661440)
  lx : Hyp.Hyp31LitX
  row22 : Stage3Row [.Fi22] (fun _ => fiLoc 18393661440)
  row23 : Stage3Row [.Fi23] (fun _ => fiLoc (2 * 64561751654400))
  row24 : Stage3Row [.Fi24Prime] (fun _ => fiLoc (2 * 64561751654400))
  facts22 : Eng.FiRowFacts row22.IsK [.Fi22] [.Fi23, .Fi24Prime] []
  facts23 : Eng.FiRowFacts row23.IsK [.Fi23] [.Fi24Prime] [.Fi22]
  facts24 : Eng.FiRowFacts row24.IsK [.Fi24Prime] [.Fi23] [.Fi22]
  variantThree : FiVariantThree
  coexist : FiCoexist

theorem fiStage3Main_of_rowInputs (I : Fi3RowInputs) : FiStage3Main :=
  fiStage3Main_of_inputs
    { pinned := I.pinned
      section_ := fiLink5bSection
      lemma33 := I.lemma33
      hypOne22 := I.hypOne22
      tmem22 := I.tmem22
      row22 := I.row22
      row23 := I.row23
      row24 := I.row24
      hyp31_22 := FiHyp31.mono (fun s hs => mem_fiTypes_of s (by simp at hs; tauto))
        (Eng.fiHyp31_of_rowFacts I.facts22 I.lx)
      hyp31_23 := FiHyp31.mono (fun s hs => mem_fiTypes_of s (by simp at hs; tauto))
        (Eng.fiHyp31_of_rowFacts I.facts23 I.lx)
      hyp31_24 := FiHyp31.mono (fun s hs => mem_fiTypes_of s (by simp at hs; tauto))
        (Eng.fiHyp31_of_rowFacts I.facts24 I.lx)
      variantThree := I.variantThree
      coexist := I.coexist }

end CFSG.EvenSporadicStandard.Induction.Fi
