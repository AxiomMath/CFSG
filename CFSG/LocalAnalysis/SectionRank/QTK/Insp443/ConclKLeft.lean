module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4.E443
open scoped IsMulCommutative

@[expose] def ConclKLeft (K : Type) [Group K] (L V MK : Subgroup K) : Prop :=
  (CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ Shape443 (↥L ⧸ CFSG.pCore 2 ↥L) ∧
    (((∃ _ : IsMulCommutative ↥V,
          IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set K)) V)) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsNaturalSumUnder 3 L V) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 →
          IsNaturalSumUnder 4 L V ∨
            ∃ _ : IsMulCommutative ↥V, SLExteriorTwo (V := ↥V) (autOn L V) ⊤ ⊥ 4) ∧
        ((Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
            Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
              alternatingGroup (Fin 6))) →
          ∀ S : Subgroup K, IsSylowTwoOf S L →
            ∀ z ∈ V ⊓ Subgroup.centralizer (S : Set K), orderOf z = 2 →
              ¬ V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set K))) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → Nat.card V = 2 ^ 6 →
          ∀ S : Subgroup K, IsSylowTwoOf S L →
            ∃ V₃ : Subgroup K, V₃ ≤ V ∧ Nat.card V₃ = 2 ^ 3 ∧
              S ≤ Subgroup.normalizer (V₃ : Set K) ∧
                ¬ Subgroup.centralizer (V₃ : Set K) ≤ MK)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 (2 * m) ∧
        ∃ _ : IsMulCommutative ↥V, BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ m) ∨
      (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∧
        ∃ _ : IsMulCommutative ↥V, FanoCoreModule (V := ↥V) (autOn L V) ⊤ ⊥)))

theorem ConclKLeft.conclK {K : Type} [Group K] {L V MK : Subgroup K}
    (h : ConclKLeft K L V MK) : ConclK K L V MK :=
  Or.inl h

end CFSG.SectionRank.QTK.Insp443
