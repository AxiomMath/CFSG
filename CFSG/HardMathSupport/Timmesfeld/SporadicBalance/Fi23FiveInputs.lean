module

public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def eLetters : List Int := eWord.map fun x => if x = 0 then 1 else 2

@[expose] def eqTab (A B : Table) : Bool := (List.range 31671).all fun i => ap A i == ap B i

@[expose] def commB (O : WOrbit) (D Bi : Table) (i j : Nat) : Bool :=
  treeAct O.par O.lab O.alpha O.beta D Bi i j == j

@[expose] def fixList (W : Table) : List Nat := (List.range 31671).filter fun i => ap W i == i

@[expose] def graphOK (c : Nat → Nat → Bool) (G : List Nat) : Bool :=
  !G.isEmpty && (G.all fun i => G.any fun j => j != i && c i j) &&
    (G.all fun i => G.all fun j => c i j || G.any fun k => c k i && c k j)

@[expose] def pathSearch (c : Nat → Nat → Bool) (F : List Nat) : List Nat :=
  (F.findSome? fun i₁ => F.findSome? fun i₂ =>
    if i₂ == i₁ || c i₁ i₂ then none else F.findSome? fun i₃ =>
      if i₃ == i₁ || i₃ == i₂ || c i₂ i₃ || !c i₁ i₃ then none else F.findSome? fun i₄ =>
        if i₄ == i₁ || i₄ == i₂ || i₄ == i₃ || c i₃ i₄ || !c i₁ i₄ || !c i₂ i₄ then none
        else some [i₁, i₂, i₃, i₄]).getD []

@[expose] def eTab (O : WOrbit) : Table := wordT 31671 (genTables O) eLetters

@[expose] def fivePathOf (O : WOrbit) : List Nat :=
  pathSearch (commB O (dTable O) (genTables O (-2))) (fixList (eTab O))

@[expose] def fiveTab (T₀ T₁ : Table) (a b : Nat) : Table :=
  compT 31671 (powT 31671 a T₀) (powT 31671 b T₁)

@[expose] def fi23FiveCore (O : WOrbit) (D Bi T₀ T₁ : Table) : Bool :=
  eqTab (powT 31671 5 T₀) (idT 31671) && !eqTab T₀ (idT 31671) &&
    eqTab (powT 31671 5 T₁) (idT 31671) &&
    eqTab (compT 31671 T₀ T₁) (compT 31671 T₁ T₀) &&
    ((List.range 5).all fun k => !eqTab T₁ (powT 31671 k T₀)) &&
    ((List.range 5).all fun a => (List.range 5).all fun b =>
      a + b == 0 || graphOK (commB O D Bi) (fixList (fiveTab T₀ T₁ a b)))

@[expose] def fi23FiveOK (O : WOrbit) : Bool :=
  let P := fivePathOf O
  P.all (· < 31671) &&
    fi23FiveCore O (dTable O) (genTables O (-2)) (eTab O)
      (starWordTab O (dTable O) (genTables O (-2)) P)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
