module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck

public section

namespace CFSG.EvenSporadicStandard.M22Std.E32Check

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck

@[expose] def tabLE : Tab → Tab → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => if a < b then true else if a = b then tabLE s t else false

@[expose] def sortTabs (L : List Tab) : List Tab := L.mergeSort tabLE

@[expose] def invTabs (T : List Tab) : List Tab := T.filter fun t => decide (tmul t t = idTab)

@[expose] def extCands (I L : List Tab) : List Tab :=
  I.filter fun x => decide (x ∉ L) && L.all (comm x)

@[expose] def elemStep (I : List Tab) (lv : List (List Tab)) : List (List Tab) :=
  (lv.flatMap fun L => (extCands I L).map fun x => sortTabs (ext L x)).dedup

@[expose] def elemLevel (T : List Tab) : Nat → List (List Tab)
  | 0 => [[idTab]]
  | k + 1 => elemStep (invTabs T) (elemLevel T k)

def jTabs : List Tab := (elemLevel s0Tabs 5).headD []

theorem jTabs_eq : jTabs = (elemLevel s0Tabs 5).headD [] := by
  unfold jTabs
  rfl

@[expose] def normB (L : List Tab) : Bool :=
  s0Gens.all fun g => L.all fun l => L.any fun l' => decide (tmul g l = tmul l' g)

@[expose] def CheckProp : Prop :=
  (elemLevel s0Tabs 5).length = 1 ∧ elemLevel s0Tabs 6 = [] ∧
  jTabs.length = 32 ∧ jTabs.Nodup ∧ idTab ∈ jTabs ∧
  (∀ a ∈ jTabs, a ∈ s0Tabs ∧ tmul a a = idTab ∧
    ∀ b ∈ jTabs, tmul a b ∈ jTabs ∧ comm a b = true) ∧
  (∃ l ∈ s0Inner, l ∈ jTabs ∧ l ∉ f1Tabs) ∧
  ∀ L ∈ elemLevel s0Tabs 4, L.Nodup ∧
    (normB L = true → 4 < (L.filter fun l => decide (l ∈ jTabs)).length ∨ ∀ l ∈ L, l ∈ f1Tabs)

instance : Decidable CheckProp := by
  unfold CheckProp
  infer_instance

@[expose] def check : Bool := decide CheckProp

end CFSG.EvenSporadicStandard.M22Std.E32Check
