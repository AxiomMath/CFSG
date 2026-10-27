module

public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsDefs

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier

@[expose] def sqOneB (g : Equiv.Perm (Fin 26)) : Bool :=
  (List.finRange 26).all fun i => g (g i) == i

@[expose] def isOneB (g : Equiv.Perm (Fin 26)) : Bool :=
  (List.finRange 26).all fun i => g i == i

@[expose] def innerInvB (g : Equiv.Perm (Fin 26)) : Bool := sqOneB g && !isOneB g && QP.sift g 0

@[expose] def outerInvB (g : Equiv.Perm (Fin 26)) : Bool := sqOneB g && !(QP.sift g 0)

@[expose] def commB (a b : Equiv.Perm (Fin 26)) : Bool :=
  (List.finRange 26).all fun i => a (b i) == b (a i)

@[expose] def kTab : Equiv.Perm (Fin 26) := tab modelK

@[expose] def zTab : Equiv.Perm (Fin 26) := tab modelZ

@[expose] def yTab : Equiv.Perm (Fin 26) := tab modelY

@[expose] def wTab : Equiv.Perm (Fin 26) := tab (modelX ^ 2 * modelY)

@[expose] def zkTab : Equiv.Perm (Fin 26) := tab (modelZ * modelK)

@[expose] def centB (g : Equiv.Perm (Fin 26)) : Bool := commB g kTab

@[expose] def centPB (g : Equiv.Perm (Fin 26)) : Bool := commB g kTab && QP.sift g 0

@[expose] def img (g : Equiv.Perm (Fin 26)) : List (Fin 26) := (List.finRange 26).map g

@[expose] def conjImg (n e : Equiv.Perm (Fin 26)) : List (Fin 26) :=
  (List.finRange 26).map fun i => n (e (n⁻¹ i))

@[expose] def e1Img : List (List (Fin 26)) :=
  [1, zTab, yTab, tab (modelZ * modelY), kTab, zkTab, tab (modelY * modelK),
    tab (modelZ * modelY * modelK)].map img

@[expose] def e2Img : List (List (Fin 26)) :=
  [1, zTab, wTab, tab (modelZ * (modelX ^ 2 * modelY)), kTab, zkTab,
    tab ((modelX ^ 2 * modelY) * modelK), tab (modelZ * (modelX ^ 2 * modelY) * modelK)].map img

@[expose] def norm1B (n : Equiv.Perm (Fin 26)) : Bool :=
  !([zTab, yTab, kTab].all fun e => e1Img.contains (conjImg n e)) || conjImg n kTab == img kTab

@[expose] def norm2B (n : Equiv.Perm (Fin 26)) : Bool :=
  !([zTab, wTab, kTab].all fun e => e2Img.contains (conjImg n e)) || conjImg n zkTab == img zkTab

end CFSG.OddStandard.SmallF3.L33
