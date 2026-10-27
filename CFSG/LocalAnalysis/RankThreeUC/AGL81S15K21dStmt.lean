module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open KFactsSmall
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def K21dSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsK21dGroup S →
    IsSimpleGroup S ∧ ∃ a b : S, a * b ≠ b * a

@[expose] def K21dGeomAt (S : Type) [Group S] [Finite S] : Prop :=
  ∀ U D E : Subgroup S, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ → U ≤ D → Group.IsSolvable ↥D →
    E ≤ D → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
    (∃ u ∈ U ⊓ Subgroup.normalizer (E : Set S), ∀ e ∈ E, u * e * u⁻¹ = e⁻¹) →
    ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧
      Nat.card ↥(U ⊓ Subgroup.normalizer (E : Set S) ⊓ Subgroup.centralizer ({x} : Set S)) ≠
        Nat.card ↥(U ⊓ Subgroup.normalizer (E : Set S) ⊓ Subgroup.centralizer ({y} : Set S))

@[expose] def K21dGeom : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsK21dGroup S → K21dGeomAt S

@[expose] def K21dRes : Prop := K21dSimple ∧ K21dGeom

@[expose] def K21dGeomTits : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    ((∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 ∧
        (d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q ∨ (d.1 = .twistedA 3 Q ∧ Q.card ≠ 2)) ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.card = 4 ∧
        d.1 = .twistedA 4 Q ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))) →
    K21dGeomAt S

@[expose] def K21dGeomU42 : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.card = 2 ∧
      d.1 = .twistedA 3 Q ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) → K21dGeomAt S

@[expose] def K21dGeomL5 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsL5Two S →
    K21dGeomAt S

@[expose] def K21dGeomA8 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* alternatingGroup (Fin 8)) → K21dGeomAt S

@[expose] def K21dGeomA6 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* alternatingGroup (Fin 6)) → K21dGeomAt S

@[expose] def K21dGeomU3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsUThreeThree S →
    K21dGeomAt S

end CFSG.LocalAnalysis.RankThreeUC.S15
