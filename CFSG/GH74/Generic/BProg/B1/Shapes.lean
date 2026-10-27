module

public import CFSG.GH74.Generic.BProg.Stage2QS
public import CFSG.GH74.Generic.BProg.Stage1Split

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

@[expose] def SourceExistsFor (P : ∀ (Kt : Type) [Group Kt], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → P (↥K ⧸ pPrimeCore 2 ↥K) → ∃ A : Subgroup G, IsSource2 x K A

@[expose] def AdmissibleExistsFor (P : ∀ (Kt : Type) [Group Kt], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → P (↥K ⧸ pPrimeCore 2 ↥K) → ∀ A : Subgroup G, IsSource2 x K A →
      ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb

theorem sourceExists_of_shapes (h1 : SourceExistsFor QShape1) (h3 : SourceExistsFor QShape3)
    (h4 : SourceExistsFor QShape4) (h5 : SourceExistsFor QShape5) : SourceExists := by
  intro G _ _ hyp noAlt x K hcirc hP
  rcases hP with h | h | h | h
  · exact h1 G hyp noAlt x K hcirc h
  · exact h3 G hyp noAlt x K hcirc h
  · exact h4 G hyp noAlt x K hcirc h
  · exact h5 G hyp noAlt x K hcirc h

theorem admissibleExists_of_shapes (h1 : AdmissibleExistsFor QShape1)
    (h3 : AdmissibleExistsFor QShape3) (h4 : AdmissibleExistsFor QShape4)
    (h5 : AdmissibleExistsFor QShape5) : AdmissibleExists := by
  intro G _ _ hyp noAlt x K hcirc A hsrc
  rcases qShapeNS_of_isSource2 hsrc with h | h | h | h
  · exact h1 G hyp noAlt x K hcirc h A hsrc
  · exact h3 G hyp noAlt x K hcirc h A hsrc
  · exact h4 G hyp noAlt x K hcirc h A hsrc
  · exact h5 G hyp noAlt x K hcirc h A hsrc

end CFSG.GH74.Generic.BProg.B1
