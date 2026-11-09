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

@[expose] def uniqAt (T F : List Tab) (a : Tab) : Bool :=
  !((classTabs T a).length == 8) ||
    let C := classTabs T a
    !(C.all fun x => C.all fun y => comm x y) ||
    !((T.filter fun l => C.all fun x => comm l x).length == 16) ||
    C.all fun x => decide (x ∈ F)

@[expose] def uniqRepOK (T F R : List Tab) : Bool :=
  R.all (fun r => decide (r ∈ T)) &&
    (T.filter isInv).all (fun a => R.any fun r => decide (a ∈ classTabs T r)) &&
    R.all (uniqAt T F)

@[expose] def s0Reps : List Tab :=
  [[14, 1, 2, 20, 17, 7, 6, 5, 19, 12, 18, 11, 9, 13, 0, 21, 16, 4, 10, 8, 3, 15],
    [9, 1, 2, 5, 8, 3, 6, 20, 4, 0, 21, 11, 14, 13, 12, 18, 16, 19, 15, 17, 7, 10],
    [19, 1, 2, 3, 14, 5, 11, 20, 12, 17, 10, 6, 8, 16, 4, 18, 13, 9, 15, 0, 7, 21],
    [17, 1, 2, 21, 14, 10, 6, 18, 12, 19, 5, 11, 8, 13, 4, 20, 16, 0, 7, 9, 15, 3],
    [7, 1, 2, 12, 10, 14, 6, 0, 21, 20, 4, 11, 3, 13, 5, 19, 16, 18, 17, 15, 9, 8],
    [0, 2, 1, 8, 10, 14, 6, 7, 3, 19, 4, 11, 21, 16, 5, 20, 13, 17, 18, 9, 15, 12],
    [0, 16, 13, 12, 14, 10, 6, 7, 21, 15, 5, 11, 3, 2, 4, 9, 1, 17, 18, 20, 19, 8],
    [0, 1, 2, 12, 5, 4, 11, 7, 21, 19, 14, 6, 3, 13, 10, 20, 16, 17, 18, 9, 15, 8],
    [17, 1, 2, 4, 3, 12, 6, 7, 10, 9, 8, 11, 5, 16, 21, 20, 13, 0, 18, 19, 15, 14],
    [9, 2, 1, 10, 12, 21, 11, 20, 14, 0, 3, 6, 4, 16, 8, 18, 13, 19, 15, 17, 7, 5],
    [0, 2, 1, 21, 14, 10, 11, 7, 12, 9, 5, 6, 8, 16, 4, 15, 13, 17, 18, 19, 20, 3],
    [7, 2, 1, 8, 5, 4, 11, 0, 3, 20, 14, 6, 21, 16, 10, 19, 13, 18, 17, 15, 9, 12],
    [0, 16, 13, 3, 10, 14, 11, 7, 8, 20, 4, 6, 12, 2, 5, 19, 1, 17, 18, 15, 9, 21],
    [12, 16, 13, 7, 15, 9, 11, 3, 17, 5, 19, 6, 0, 2, 20, 4, 1, 8, 21, 10, 14, 18],
    [17, 16, 13, 21, 5, 4, 11, 18, 12, 15, 14, 6, 8, 2, 10, 9, 1, 0, 7, 20, 19, 3]]

end CFSG.EvenSporadicStandard.M22Std.OutCheck
