module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443EFact
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4.E443
open scoped IsMulCommutative

structure KConf (K : Type) [Group K] [Finite K] (L V MK : Subgroup K) : Prop where
  quasisimple : CFSG.IsQuasisimple K
  odd_card_center : Odd (Nat.card (Subgroup.center K))
  ne_bot : V ≠ ⊥
  elemAbelian : IsElemAbelian 2 V
  perfect : ⁅L, L⁆ = L
  le_normalizer : L ≤ Subgroup.normalizer (V : Set K)
  le_pCoreOf : V ≤ pCoreOf 2 L
  pCoreOf_le : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set K)
  eq_commutator : V = ⁅V, L⁆
  le_MK : L ≤ MK
  MK_le_normalizer : MK ≤ Subgroup.normalizer (L : Set K)
  MK_ne_top : MK ≠ ⊤
  normalizer_le : ∀ Q : Subgroup K, Q ≠ ⊥ → IsPGroup 2 Q →
    (∀ σ : K ≃* K, V.map σ.toMonoidHom = V → L.map σ.toMonoidHom = L →
      MK.map σ.toMonoidHom = MK → Q.map σ.toMonoidHom = Q) →
    Subgroup.normalizer (Q : Set K) ≤ MK
  card_eq : ∀ X Y : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), X.Normal → Y.Normal →
    CFSG.IsQuasisimple ↥X → CFSG.IsQuasisimple ↥Y → Nat.card X = Nat.card Y
  card_le : ∀ Q : Subgroup K, Q ≠ ⊥ → IsPGroup 2 Q → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ E : Subgroup K, E ≤ Subgroup.normalizer (Q : Set K) → IsElemAbelian p E →
      Nat.card E ≤ p ^ 2

@[expose] def ConclK (K : Type) [Group K] (L V MK : Subgroup K) : Prop :=
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
        ∃ _ : IsMulCommutative ↥V, FanoCoreModule (V := ↥V) (autOn L V) ⊤ ⊥))) ∨
  (IsSporadic .J4 K ∧
    (IsSporadic .M24 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1))

@[expose] def ForK (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (L V MK : Subgroup K),
    KConf K L V MK → P (K ⧸ Subgroup.center K) → ConclK K L V MK

theorem ForK.mono {P Q : (S : Type) → [Group S] → Prop}
    (h : ∀ (S : Type) [Group S], P S → Q S) (hQ : ForK Q) : ForK P :=
  fun K _ _ L V MK hK hP => hQ K L V MK hK (h _ hP)

theorem ForK.or {P Q : (S : Type) → [Group S] → Prop} (hP : ForK P) (hQ : ForK Q) :
    ForK (fun S _ => P S ∨ Q S) := by
  intro K _ _ L V MK hK h
  rcases h with h' | h'
  · exact hP K L V MK hK h'
  · exact hQ K L V MK hK h'

end CFSG.SectionRank.QTK.Insp443
