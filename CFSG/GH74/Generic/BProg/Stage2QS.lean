module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.BProg.Frozen

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def Stage2QSFor (P : ∀ (Kt : Type) [Group Kt], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → P (↥K ⧸ pPrimeCore 2 ↥K) → IsQuasisimple ↥K

@[expose] def Stage2QSNS : Prop := Stage2QSFor QShapeNS

@[expose] def SourceExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → QShapeNS (↥K ⧸ pPrimeCore 2 ↥K) → ∃ A : Subgroup G, IsSource2 x K A

@[expose] def AdmissibleExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → ∀ A : Subgroup G, IsSource2 x K A →
      ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb

end CFSG.GH74.Generic.BProg
