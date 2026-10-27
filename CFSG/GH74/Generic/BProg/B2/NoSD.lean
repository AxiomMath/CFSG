module

public import CFSG.GH74.Generic.BProg.Stage1Split
public import CFSG.GH74.Generic.BProg.B1.Stage3aRankJ1
public import CFSG.GH74.Generic.BProg.B1.Stage3aRankRee
public import CFSG.GH74.Generic.BProg.Stage2Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

@[expose] def NoJPrimeNonSD : Prop :=
  B1.NoJPrimeFor QShape1 ∧ B1.NoJPrimeFor B1.QShape3W ∧ B1.NoJPrimeFor QShape4 ∧
    B1.NoJPrimeFor QShape5

theorem noJPrimeNonSD :
    NoJPrimeNonSD :=
  ⟨B1.noJPrimeFor_shape1, B1.noJPrimeFor_shape3W, B1.noJPrimeFor_shape4, B1.noJPrimeFor_shape5⟩

theorem pRank_CxK_le_one_or_sd (hNo : NoJPrimeNonSD) {G : Type} [Group G] [Finite G] {x : G}
    {K A M P Q : Subgroup G} (hs : Stage2Setup G x K A M P Q) :
    pRank 2 ↥(CxK x K) ≤ 1 ∨ B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) := by
  by_cases h : pRank 2 ↥(CxK x K) ≤ 1
  · exact Or.inl h
  · right
    have h1 : 1 < pRank 2 ↥(CxK x K) := by omega
    have hJ : IsJ2 x K := hs.pair.1
    rcases qShapeNS_of_isSource2 hs.src with hQ | hQ | hQ | hQ
    · exact (hNo.1 G hs.hyp hs.noAlt x K hJ h1 hQ).elim
    · rcases B1.qShape3_split hQ with hW | hSD
      · exact (hNo.2.1 G hs.hyp hs.noAlt x K hJ h1 hW).elim
      · exact hSD
    · exact (hNo.2.2.1 G hs.hyp hs.noAlt x K hJ h1 hQ).elim
    · exact (hNo.2.2.2 G hs.hyp hs.noAlt x K hJ h1 hQ).elim

end CFSG.GH74.Generic.BProg.B2
