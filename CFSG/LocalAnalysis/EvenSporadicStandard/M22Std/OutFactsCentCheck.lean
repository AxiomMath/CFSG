module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck
public import CFSG.Sporadic.Schreier.M22Data

public section

namespace CFSG.EvenSporadicStandard.M22Std.OutCheck

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.Sporadic.Schreier

@[expose] def centXs : List Tab := (elemTabs 1).take 4

@[expose] def centConj (x : Tab) : Tab := tmul (tmul betaTab x) betaTab

@[expose] def conjAt (y : Equiv.Perm (Fin 22)) (x x' : Tab) : Bool :=
  (List.finRange 22).all fun i =>
    decide ((y (Fin.ofNat 22 (x'.getD i.val 0))).val = x.getD (y i).val 0)

@[expose] def centOuterOK : Bool :=
  (enumeration m22Certificate).all fun y =>
    !(centXs.all fun x => conjAt y x (centConj x))

end CFSG.EvenSporadicStandard.M22Std.OutCheck
