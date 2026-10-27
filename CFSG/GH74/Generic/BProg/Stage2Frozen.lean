module

public import CFSG.GH74.Generic.BProg.Stage2Defs
public import CFSG.GH74.Uniqueness.Statements

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

@[expose] def Stage2PQExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A : Subgroup G), IsJ2Circ x K → IsSource2 x K A →
    ∃ P Q : Subgroup G, IsSylowOf 2 P (centralizer ({x} : Set G)) ∧ A ≤ P ∧ Q = P ⊓ CxK x K ∧
      IsSylowOf 2 Q (CxK x K)

@[expose] def Stage2Thm1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q : Subgroup G), Stage2Setup G x K A M P Q →
    ∃ H : Subgroup G, Stage2Concl1 x K M Q H

@[expose] def Stage2Thm2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    Stage2Concl1 x K M Q H → Stage2Concl2 M

@[expose] def Stage2Cor2Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    Stage2Concl1 x K M Q H → Stage2Concl2 M → Stage2Cor2 x K A M H

@[expose] def Stage2Thm3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    Stage2Concl1 x K M Q H → Stage2Concl2 M → Stage2Cor2 x K A M H →
      (barIn M H = generalizedFitting (Mbar M) ∧ IsSimpleGroup ↥(barIn M H)) ∧
        centralizer ({x} : Set G) ≤ M

@[expose] def Stage2Prop31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    Stage2Concl1 x K M Q H → Stage3A x A M H → QShapeNS (↥K ⧸ pPrimeCore 2 ↥K) →
      OfLieType ↥(barIn M H)

@[expose] def Stage2Thm4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    Stage2Concl1 x K M Q H → Stage2Concl2 M → Stage3A x A M H → OfLieType ↥(barIn M H) →
      ∃ Z : Set G, IsInvariantInvolutionSet Z ∧ IsProductDisconnected Z M

end CFSG.GH74.Generic.BProg
