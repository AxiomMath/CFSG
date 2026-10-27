module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSubCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSylowHomData

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.EvenSporadicStandard.Fin76b

@[expose] def glueT (T₁ T₂ : Table) : Table :=
  Array.ofFn (n := 28) fun i => if i.val < 16 then T₁[i.val]! else T₂[i.val - 16]! + 16

@[expose] def glueGens (gS g12 : Array Table) : Array Table :=
  (Array.range gS.size).map fun i => glueT gS[i]! g12[i]!

@[expose] def fixes12 (T : Table) : Bool := (List.range 12).all fun j => ap T (16 + j) == 16 + j

@[expose] def evenTab (T : Table) : Bool :=
  decide ((∏ j : Fin 12, ∏ i ∈ Finset.Iio j,
    (if ap T i.val < ap T j.val then (1 : ℤˣ) else -1)) = 1)

@[expose] def sylowHomCheck (gS : Array Table) (cT : Table) (g12 : Array Table) : Bool :=
  let gG := glueGens gS g12
  let EG := mulClosureS 28 16 gG 4000
  let c28 := glueT cT (idT 12)
  gS.size == g12.size && g12.all (fun T => permOK 12 T && evenTab T) &&
    !tblEq 16 cT (idT 16) && enumOK 28 16 gG EG 1024 && memTab 28 EG.1.toList c28 &&
    EG.1.toList.all fun T => !fixes12 T || tblEq 28 T (idT 28) || tblEq 28 T c28

@[expose] def sylowHomData (_ : ℕ) : Array Table :=
  (sylowHomImages.map fun l => (l.map UInt32.ofNat).toArray).toArray

@[expose] def sylowHomCheckAll : Bool :=
  [0, 1].all fun k => sylowHomCheck (wgens 1 k sWords) (nwT 1 k cWord) (sylowHomData k)

end CFSG.EvenSporadicStandard.M12Std.Yosh
