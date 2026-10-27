module

public import CFSG.Monster.B.TwoA.Census.PermClassesInputs
public import CFSG.Monster.B.TwoA.Base.CodeCheck
public meta import CFSG.Monster.B.TwoA.Census.PermClassesInputs
public meta import CFSG.Monster.B.TwoA.Census.PermCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.B.TwoA.Census.MonoData
public meta import CFSG.Monster.Code.Bits
public meta import CFSG.Monster.Code.Basis

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census

@[expose] def permWordArr (p : Array ℕ) (w : Fin 24 → ZMod 2) : Fin 24 → ZMod 2 :=
  w ∘ arrFun (ainv p)

@[expose] def sumCount (p : Array ℕ) (d : ℕ) : ℕ :=
  let q := arrFun (ainv p)
  treeSumN (fun a => if bvec 24 a + bvec 24 a ∘ q = bvec 24 d then 1 else 0) Bmask 12 0

@[expose] def sqSum (d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range sylowCert.pts.size,
    if amul sylowCert.pts[i]! sylowCert.pts[i]! = idArr then sumCount sylowCert.pts[i]! d else 0

@[expose] def fixOK (a : ℕ) : Bool :=
  decide ((∀ k : Fin 10, permWordArr sylowGens[(k : ℕ)]! (bvec 24 a) = bvec 24 a) →
    (bvec 24 a = bvec 24 0 ∨ bvec 24 a = bvec 24 255 ∨ bvec 24 a = bvec 24 16776960 ∨
      bvec 24 a = bvec 24 16777215))

@[expose] def fixBad : ℕ := treeSumN (fun a => if fixOK a then 0 else 1) Bmask 12 0

end CFSG.EvenSporadicStandard.TwoCo1
