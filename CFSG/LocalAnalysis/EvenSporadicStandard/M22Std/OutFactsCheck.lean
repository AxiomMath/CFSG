module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.FusionCheck

public section

namespace CFSG.EvenSporadicStandard.M22Std.OutCheck

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck

@[expose] def betaTab : Tab :=
  [0, 1, 2, 12, 5, 4, 11, 7, 21, 19, 14, 6, 3, 13, 10, 20, 16, 17, 18, 9, 15, 8]

@[expose] def betaArr : Array Nat :=
  #[1, 0, 2, 3, 4, 7, 6, 5, 17, 19, 16, 18, 15, 13, 14, 12, 10, 8, 11, 9, 20, 22, 21, 23]

@[expose] def jCatList : List Nat :=
  [2, 3, 4, 16, 21, 22, 17, 13, 12, 5, 9, 8, 10, 23, 19, 11, 14, 6, 20, 7, 18, 15]

@[expose] def s0Gens : List Tab := betaTab :: gensTab

@[expose] def s0Inner : List Tab := span gensTab

@[expose] def s0Outer : List Tab := s0Inner.map (tmul betaTab)

@[expose] def s0Tabs : List Tab := span s0Gens

theorem s0Tabs_eq : s0Tabs = s0Inner ++ s0Outer := rfl

@[expose] def f1Tabs : List Tab := idTab :: elemTabs 1

@[expose] def x8Tab : Tab := (elemTabs 1).getD 0 idTab

@[expose] def orbitTabs (T F : List Tab) (x : Tab) : List Tab :=
  F.filter fun y => T.any fun a => decide (tmul a x = tmul y a)

@[expose] def tinv (t : Tab) : Tab := (List.range 22).map fun i => t.idxOf i

@[expose] def classTabs (T : List Tab) (x : Tab) : List Tab :=
  (T.map fun a => tmul (tmul a x) (tinv a)).dedup

@[expose] def s0Check : Bool :=
  decide (s0Tabs.length = 256 ∧ s0Tabs.Nodup ∧ ∀ l ∈ s0Tabs, ∀ g ∈ s0Gens, tmul l g ∈ s0Tabs) &&
  decide (tmul betaTab betaTab = idTab) &&
  decide ((∀ g ∈ s0Gens, comm tTab g = true) ∧
      ∀ l ∈ s0Tabs, (∀ g ∈ s0Gens, comm l g = true) → l = idTab ∨ l = tTab) &&
  decide (∀ g ∈ s0Gens, normOK (elemTabs 1) g = true) &&
  decide ((orbitTabs s0Tabs f1Tabs x8Tab).length = 8) &&
  decide ((s0Outer.filter fun l => decide (tmul l l = idTab)).length = 36 ∧
    (s0Outer.filter fun l => decide (tmul l l = tTab)).length = 20)

@[expose] def cls8Invs (T : List Tab) : List Tab :=
  (T.filter isInv).filter fun x => (classTabs T x).length == 8

@[expose] def uniqOK (T F : List Tab) : Bool :=
  (cls8Invs T).all fun a =>
    let C := classTabs T a
    !(C.all fun x => C.all fun y => comm x y) ||
    !((T.filter fun l => C.all fun x => comm l x).length == 16) ||
    C.all fun x => decide (x ∈ F)

end CFSG.EvenSporadicStandard.M22Std.OutCheck
