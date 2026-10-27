module

public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public meta import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

set_option compiler.extract_closed false

@[expose] def eWord24 : List Nat := [0, 2, 0, 3]

@[expose] def eqTab24 (A B : Table) : Bool := (List.range 306936).all fun i => ap A i == ap B i

@[expose] def fixList24 (W : Table) : List Nat := (List.range 306936).filter fun i => ap W i == i

@[expose] def clsWordTab (c : Ctx) (w : List Nat) : Table :=
  w.foldr (fun k P => compT 306936 (clsTab c k) P) (idT 306936)

@[expose] def fivePath24 (c : Ctx) : List Nat :=
  pathSearch (commB c) (fixList24 (wordTab c eWord24))

@[expose] def fiveTab24 (T₀ T₁ : Table) (a b : Nat) : Table :=
  compT 306936 (powT 306936 a T₀) (powT 306936 b T₁)

@[expose] def fi24FiveCore (c : Ctx) (T₀ T₁ : Table) : Bool :=
  eqTab24 (powT 306936 5 T₀) (idT 306936) && !eqTab24 T₀ (idT 306936) &&
    eqTab24 (powT 306936 5 T₁) (idT 306936) &&
    eqTab24 (compT 306936 T₀ T₁) (compT 306936 T₁ T₀) &&
    ((List.range 5).all fun k => !eqTab24 T₁ (powT 306936 k T₀)) &&
    ((List.range 5).all fun a => (List.range 5).all fun b =>
      a + b == 0 || graphOK (commB c) (fixList24 (fiveTab24 T₀ T₁ a b)))

@[expose] def fi24FiveOK (O : Enum) : Bool :=
  let c := mkCtx O
  let P := fivePath24 c
  P.length == 4 && P.all (· < 306936) && fi24FiveCore c (wordTab c eWord24) (clsWordTab c P)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
