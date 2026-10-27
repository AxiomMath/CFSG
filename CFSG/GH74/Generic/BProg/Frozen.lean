module

public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.GH74.Generic.JStar2Defs

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

@[expose] def NoAltJ2 (G : Type) [Group G] : Prop :=
  ¬ ∃ (x' : G) (M' : Subgroup G), IsJ2Alt x' M'

@[expose] def Stage1AltFor (P : ∀ (Kt : Type) [Group Kt], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → P (↥K ⧸ pPrimeCore 2 ↥K) →
      ∀ A : Subgroup G, IsSource2 x K A → IsAllowable x K A ∨ IsReg32 A

@[expose] def Stage1Alt : Prop :=
  Stage1AltFor QShape1 ∧ Stage1AltFor QShape3 ∧ Stage1AltFor QShape4 ∧ Stage1AltFor QShape5

@[expose] def Stage2Allow : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → ∀ A : Subgroup G, IsSource2 x K A → IsAllowable x K A

@[expose] def JPrimeNS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2 x K → 1 < pRank 2 ↥(CxK x K) → QShapeNS (↥K ⧸ pPrimeCore 2 ↥K)

end CFSG.GH74.Generic.BProg
