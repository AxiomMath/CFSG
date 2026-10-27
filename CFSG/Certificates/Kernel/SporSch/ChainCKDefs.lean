module

public import CFSG.Sporadic.Schreier.J1Tables
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native

@[expose] def ChainCK (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (kS kO nb BP : Nat)
    (S : Array (Array Nat)) (base : Array Nat) (D : List (List Int)) : Prop :=
  Binds n w PS kS nb BP S base ∧
    headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true ∧
    LevelsOK n w PS PSI LR TR TRI kS nb BP ∧
    Nat.card (Subgroup.closure (Set.range fun j : Fin kO => permOfArr n S[j.val]!)) ≤
      (rawOrbitSizes n S base).prod

@[expose] def levTables (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (nb : Nat) :
    List (List Table) :=
  (List.range nb).map fun i =>
    (List.range ((rawLevels n S base)[i]!).pts.size).map (levTable n (rawLevels n S base)[i]!)

end CFSG.KS.SporSch.MOC

end
