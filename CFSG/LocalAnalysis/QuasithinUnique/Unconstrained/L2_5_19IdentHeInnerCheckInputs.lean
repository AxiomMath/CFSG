module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerData
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayerCheck
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.CountSpec
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.QuasithinUnique.Id2519.HeInner
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native
open CFSG.QuasithinUnique.Id2519.MathNoLayer

@[expose] def heXp : RawSchreierDatum 105 :=
  certificate (by decide) (heSigmaP.map (permOrId 105)) heXpWords #v[1, 0, 2, 3] (by decide)

@[expose] def heDp : RawSchreierDatum 105 :=
  certificate (by decide) (heDpGens.map (permOrId 105)) heDpWords #v[1, 0, 2] (by decide)

@[expose] def heSigmaPerm (j : ℕ) : Equiv.Perm (Fin 105) := permOrId 105 (heSigmaP.getD j #[])

@[expose] def heDpPerm (k : ℕ) : Equiv.Perm (Fin 105) := permOrId 105 (heDpGens.getD k #[])

@[expose] def heDpTabs : Array Table := ((heDpGens.map (permOrId 105)).map toTable).toArray

@[expose] def heDpTabsInv : Array Table :=
  ((heDpGens.map (permOrId 105)).map fun g => toTable g⁻¹).toArray

@[expose] def heToTabs (l : List (List Nat)) : List Table :=
  l.map fun r => (r.map UInt32.ofNat).toArray

end CFSG.QuasithinUnique.Id2519.HeInner
