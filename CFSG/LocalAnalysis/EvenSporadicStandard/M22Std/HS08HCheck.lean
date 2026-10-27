module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32Check

public section

namespace CFSG.EvenSporadicStandard.M22Std.HS08Check

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check

@[expose] def letterTabs4 : List Tab := [tabA, tabB, tabBi, betaTab]

@[expose] def invWordL (w : List Nat) : List Nat :=
  w.reverse.map fun i => if i = 1 then 2 else if i = 2 then 1 else i

@[expose] def xTab : Tab := wordTab letterTabs4 xWord

@[expose] def dGens : List Tab := s0Gens ++ [xTab]

@[expose] def dReps : List Tab := dRepWords.map (wordTab dGens)

@[expose] def dTabs : List Tab := dReps.flatMap fun r => s0Tabs.map fun s => tmul s r

@[expose] def jInn : List Tab := jTabs.filter fun l => decide (l ∈ s0Inner)

@[expose] def jOut : List Tab := jTabs.filter fun l => decide (l ∈ s0Outer)

@[expose] def jOrb (x : Tab) : List Tab :=
  jOut.filter fun y => dTabs.any fun d => decide (tmul d x = tmul y d)

@[expose] def x4Tab : Tab := (jInn.filter fun l => decide (l ≠ idTab)).headD idTab

@[expose] def x6Tab : Tab := jOut.getD 5 idTab

@[expose] def x10Tab : Tab := jOut.getD 0 idTab

@[expose] def DProp : Prop :=
  dTabs.length = 3840 ∧ dTabs.Nodup ∧ idTab ∈ dTabs ∧
  (∀ l ∈ dTabs, ∀ g ∈ dGens, tmul l g ∈ dTabs) ∧
  ∀ g ∈ dGens, ∀ j ∈ jTabs, ∃ j' ∈ jTabs, tmul g j = tmul j' g

instance : Decidable DProp := by
  unfold DProp
  infer_instance

@[expose] def dCheck : Bool := decide DProp

@[expose] def cPairs : List (Tab × Tab) :=
  cWords.map fun w => (wordTab letterTabs4 w, wordTab letterTabs4 (invWordL w))

@[expose] def ConjProp : Prop :=
  cPairs.length = 231 ∧ (∀ p ∈ cPairs, tmul p.1 p.2 = idTab) ∧
  cPairs.Pairwise fun p q => ∃ x ∈ jTabs, tmul (tmul (tmul p.2 q.1) x) (tmul q.2 p.1) ∉ jTabs

instance : Decidable ConjProp := by
  unfold ConjProp
  infer_instance

@[expose] def conjCheck : Bool := decide ConjProp

@[expose] def NormProp : Prop :=
  jInn.length = 16 ∧ jOut.length = 16 ∧
  (∀ l ∈ dTabs, (∀ j ∈ jTabs, tmul l j = tmul j l) → l ∈ jTabs) ∧
  (∀ y ∈ jInn.filter fun l => decide (l ≠ idTab), ∃ d ∈ dTabs, tmul d x4Tab = tmul y d) ∧
  x4Tab ∈ jTabs ∧ x6Tab ∈ jTabs ∧ x10Tab ∈ jTabs ∧
  (jOrb x6Tab).length = 6 ∧ (jOrb x10Tab).length = 10 ∧
  (∀ y ∈ jOut, y ∈ jOrb x6Tab ∨ y ∈ jOrb x10Tab) ∧ (∀ y ∈ jOrb x6Tab, y ∉ jOrb x10Tab) ∧
  (∀ d ∈ dTabs, ∀ x ∈ jOrb x6Tab, ∃ y ∈ jOrb x6Tab, tmul d x = tmul y d) ∧
  (∀ d ∈ dTabs, ∀ x ∈ jOrb x10Tab, ∃ y ∈ jOrb x10Tab, tmul d x = tmul y d)

instance : Decidable NormProp := by
  unfold NormProp
  infer_instance

@[expose] def normCheck : Bool := decide NormProp

@[expose] def OutInvProp : Prop :=
  ∀ v ∈ s0Outer, tmul v v = idTab → ∃ w ∈ owWords, ∃ j ∈ jTabs,
    tmul (wordTab letterTabs4 w) v = tmul j (wordTab letterTabs4 w)

instance : Decidable OutInvProp := by
  unfold OutInvProp
  infer_instance

@[expose] def outInvCheck : Bool := decide OutInvProp

@[expose] def s0Invs : List Tab := s0Tabs.filter fun t => decide (tmul t t = idTab)

@[expose] def GenInvProp : Prop := genInvWords.map (wordTab s0Invs) = s0Gens

instance : Decidable GenInvProp := by
  unfold GenInvProp
  infer_instance

@[expose] def genInvCheck : Bool := decide GenInvProp

end CFSG.EvenSporadicStandard.M22Std.HS08Check
