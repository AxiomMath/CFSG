module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.SLPProd

public section

namespace CFSG.KC.KDenseP.NortonSLP

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton CFSG.YGroups.Y443

@[expose] def stepPair (gens : Array (List Native.Gen)) (steps : Array (ProdStep × List Native.Gen))
    (k : ℕ) : Option (List Native.Gen × List Native.Gen) :=
  match steps[k]!.1 with
  | .gen _ => none
  | .prod l => some (steps[k]!.2, prodConcat gens steps l)
  | .inv l => some (steps[k]!.2 ++ prodConcat gens steps l, [])

@[expose] def prodPairs (gens : Array (List Native.Gen)) (steps : Array (ProdStep × List Native.Gen))
    (lo hi : ℕ) : List (List Native.Gen × List Native.Gen) :=
  (List.range' lo (hi - lo)).filterMap (stepPair gens steps)

@[expose] def idxOK (gens : Array (List Native.Gen)) (steps : Array (ProdStep × List Native.Gen))
    (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun k =>
    match steps[k]!.1 with
    | .gen i => decide (i < gens.size)
    | .prod l => l.all fun i => decide (i < k)
    | .inv l => l.all fun i => decide (i < k)

@[expose] def targetPairs (gens : Array (List Native.Gen)) (steps : Array (ProdStep × List Native.Gen))
    (idx : List ℕ) : List (List Native.Gen × List Native.Gen) :=
  (List.range 11).map fun j => (prodWord gens steps idx[j]!, L j)

@[expose] def tgtOK (steps : Array (ProdStep × List Native.Gen)) (n : ℕ) (idx : List ℕ) : Bool :=
  decide (steps.size = n) && (List.range 11).all fun j => decide (idx[j]! < n)

end CFSG.KC.KDenseP.NortonSLP

end
