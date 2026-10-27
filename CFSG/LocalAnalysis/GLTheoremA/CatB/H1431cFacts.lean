module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cTransA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)

@[expose] def isF4two : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .F4 q => q.card = 2
    | _ => False

@[expose] def isSp68 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .B 3 q => q.card = 8
    | _ => False

@[expose] def isSp492 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .B 2 q => q.card = 2 ^ 9
    | _ => False

@[expose] def isL2three18 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .A 1 q => q.card = 3 ^ 18
    | _ => False

@[expose] def i1431LieList (i : TauCeti.CFSGIndex) : Prop :=
  S8.L84.isSp82 i ∨ isF4two i ∨ isSp68 i ∨ isSp492 i ∨ isL2three18 i

@[expose] def RkTau {Y : Type} [Group Y] (τ : MulAut Y) : Prop :=
  ∀ U : Subgroup Y, U ≠ ⊥ → IsPGroup 2 ↥U → U ≤ fixSubgroup τ →
    ∀ E : Subgroup Y, E ≤ fixSubgroup τ → E ≤ Subgroup.normalizer (U : Set Y) →
      IsElemAbelian 3 E → E ⊓ Subgroup.center Y = ⊥ → (∀ a ∈ E, τ ≠ MulAut.conj a) →
        Nat.card E ≤ 3 ^ 2

@[expose] def I1431JType {Y : Type} [Group Y] [Finite Y] (ξ : MulAut Y) (J : Subgroup Y) : Prop :=
  catalogIs (PSimple 3 J) S8.L84.isType1430 ∧
    (catalogIs (PSimple 3 J) S8.L84.isSp48 →
      ∃ τ : MulAut Y, τ ^ 3 = 1 ∧ Commute τ ξ ∧ ¬ InnerOnMod 3 J τ ∧ RkTau τ)

@[expose] def I1431LieS : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    catalogIs (Y ⧸ Subgroup.center Y) (onLie fun _ => True) →
    ∀ ξ : MulAut Y, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ J : Subgroup Y, GLAPComponent 3 (fixSubgroup ξ) J →
      I1431JType ξ J → catalogIs (Y ⧸ Subgroup.center Y) i1431LieList

@[expose] def I1431AltS : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    ∀ n : ℕ, catalogIs (Y ⧸ Subgroup.center Y) (isAltN n) → ∀ ξ : MulAut Y, ξ ^ 3 = 1 → ξ ≠ 1 →
      ∀ J : Subgroup Y, GLAPComponent 3 (fixSubgroup ξ) J → I1431JType ξ J → n = 12

@[expose] def I1431SporS : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    ∀ s : TauCeti.SporadicName, catalogIs (Y ⧸ Subgroup.center Y) (S8.sporIs s) →
      ∀ ξ : MulAut Y, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ J : Subgroup Y, GLAPComponent 3 (fixSubgroup ξ) J →
        I1431JType ξ J → s = TauCeti.SporadicName.HN

@[expose] def I1431InspF42 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    catalogIs (Y ⧸ Subgroup.center Y) isF4two → ∀ τ : MulAut Y, τ ^ 3 = 1 → ∀ A : Subgroup Y,
      GLAPComponent 3 (fixSubgroup τ) A → ¬ S8.IsTypeWithCenter 3 A S8.isA6 1

@[expose] def I1431InspSp68 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    catalogIs (Y ⧸ Subgroup.center Y) isSp68 → ∀ τ : MulAut Y, τ ^ 3 = 1 → ∀ A : Subgroup Y,
      GLAPComponent 3 (fixSubgroup τ) A → ¬ S8.IsTypeWithCenter 3 A S8.isA6 1

@[expose] def I1431InspSp492 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    catalogIs (Y ⧸ Subgroup.center Y) isSp492 → ∀ τ : MulAut Y, τ ^ 3 = 1 → ∀ A : Subgroup Y,
      GLAPComponent 3 (fixSubgroup τ) A → ¬ S8.IsTypeWithCenter 3 A S8.isA6 1

@[expose] def I1431InspL2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    catalogIs (Y ⧸ Subgroup.center Y) isL2three18 → ∀ τ : MulAut Y, τ ^ 3 = 1 → ∀ A : Subgroup Y,
      GLAPComponent 3 (fixSubgroup τ) A → ¬ S8.IsTypeWithCenter 3 A S8.isA6 1

@[expose] def I1431InspHN : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    catalogIs (Y ⧸ Subgroup.center Y) (S8.sporIs TauCeti.SporadicName.HN) → ∀ τ : MulAut Y, τ ^ 3 = 1 →
      ∀ A : Subgroup Y, GLAPComponent 3 (fixSubgroup τ) A → ¬ S8.IsTypeWithCenter 3 A S8.isA6 1

@[expose] def I1431MultS : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    catalogIs (Y ⧸ Subgroup.center Y) (fun i => S8.L84.isSp82 i ∨ isAltN 12 i) →
      Subgroup.center Y = ⊥

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
