module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.MainEng
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsC
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Orders

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def Fi23Mult : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .Fi23 →
    center X = ⊥

@[expose] def Fi24Mult : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .Fi24Prime →
    Odd (Nat.card (center X))

section Main

theorem fiPinned_of_mult (m23 : Fi23Mult) (m24 : Fi24Mult) (atl : FiAtlas) : FiPinned := by
  have hmult : OddMultTrivial .Fi23 := fun L _ _ hq _ hcq => m23 L hq hcq
  have hfix23 : Fi23FixesElem := fi23FixesElem_of_atlas hmult atl.fi22Covers
  have hfix24 : Fi24InFixesElem := fi24InFixesElem_of_atlas atl.fi22Covers
  refine
    { orders := fiOrders
      excl24 := pinFi23Excl24
      mult23 := m23
      mult24 := m24
      rank23 := fun X _ _ hq hX => ?_
      rank24 := fun X _ _ hq hX => ?_
      notExc23 := pinNotExc23
      notExc24 := pinNotExc24 }
  · obtain ⟨e⟩ : IsSporadic X .Fi23 := isSporadic_of_center_eq_bot (m23 X hq hX) hX
    rw [pRank_two_eq_of_mulEquiv' e]
    exact fi23_pRank_pinned hfix23
  · exact three_le_pRank_of_isLS fi24_finite
      (fun Y _ hY => by
        obtain ⟨g⟩ := hY
        rw [pRank_two_eq_of_mulEquiv' g]
        exact fi24_pRank_pinned hfix24)
      ⟨.Fi24Prime, List.mem_singleton_self _, hq, m24 X hq hX, hX⟩

end Main

section Inputs

structure Fi3AtlasInputs : Type 1 where
  mult23 : Fi23Mult
  mult24 : Fi24Mult
  atlas : FiAtlas
  hyp12 : Hyp12Fi
  lo : LieModelOrders
  lemma33 : ∀ (IsK IsL : GroupClass) (H : Type) [Group H] [Finite H], Lemma33Two IsK IsL H
  hypOne22 : ∀ (Y : Type) [Group Y], IsSporadic Y .Fi22 → HypothesisOne Y
  tmem22 : TMemOfNotMax [.Fi22] (fun _ => fiLoc 18393661440)
  lx : Hyp.Hyp31LitX
  variantThree : FiVariantThree
  coexist : FiCoexist

end Inputs

section Assembly

noncomputable def fi3RowInputs_of_atlas (I : Fi3AtlasInputs) : Fi3RowInputs :=
  have hmult : OddMultTrivial .Fi23 := fun L _ _ hq _ hcq => I.mult23 L hq hcq
  have hpf : FiPinned := fiPinned_of_mult I.mult23 I.mult24 I.atlas
  { pinned := hpf
    lemma33 := I.lemma33
    hypOne22 := I.hypOne22
    tmem22 := I.tmem22
    lx := I.lx
    row22 := stage3Row_fi22 (fi22FixesElem_of_atlas I.atlas.u62Covers)
    row23 := stage3Row_fi23 hmult (fi23FixesElem_of_atlas hmult I.atlas.fi22Covers)
    row24 := stage3Row_fi24 (fi24InFixesElem_of_atlas I.atlas.fi22Covers)
    facts22 := fiRowFacts_fi22 hpf I.hyp12 I.lo I.atlas
    facts23 := fiRowFacts_fi23 hpf I.hyp12 I.lo I.atlas
    facts24 := fiRowFacts_fi24 hpf I.hyp12 I.lo I.atlas
    variantThree := I.variantThree
    coexist := I.coexist }

theorem fiStage3Main_of_atlas (I : Fi3AtlasInputs) : FiStage3Main :=
  fiStage3Main_of_rowInputs (fi3RowInputs_of_atlas I)

end Assembly

end CFSG.EvenSporadicStandard.Induction.Fi
