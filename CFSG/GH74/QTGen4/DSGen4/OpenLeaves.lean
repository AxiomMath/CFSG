module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.Finite4

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

@[expose] def LeafSylowS : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G},
    (Hyp111R L1 L2 S) →
    IsSylowTwoOf S (bigB L1 L2 S) ∧ IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) ∧
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S

@[expose] def LeafRankBounds : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G],
    (∀ R : Subgroup G, IsPGroup 2 R → (dsFrattini R).relIndex R ≤ 16) ∧
      (∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 16)

@[expose] def LeafFrattiniFaithful : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Subgroup G},
    (CharTwo P) →
    ∀ p ∈ P, (∀ q ∈ pCoreOf 2 P, ⁅p, q⁆ ∈ dsFrattini (pCoreOf 2 P)) → p ∈ pCoreOf 2 P

@[expose] def LeafFrattiniChief : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L P : Subgroup G},
    (A5Par L P) →
    A5Chief P L (pCoreOf 2 P) (dsFrattini (pCoreOf 2 P))

@[expose] def LeafZiStructure : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (ZSetting L1 L2 S) →
    dsZ S ≠ ⊥ ∧ dsZ S ≤ dsZi L1 S ∧ dsZi L1 S ≤ dsOmega1 (centerOf (dsQ L1 L2 S)) ∧
      IsElemAbelian 2 (dsOmega1 (centerOf (dsQ L1 L2 S))) ∧
      Nat.card (dsOmega1 (centerOf (dsQ L1 L2 S))) ≤ 16 ∧
      L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsZi L1 S : Set G) ∧
      L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsOmega1 (centerOf (dsQ L1 L2 S)) : Set G)

@[expose] def LeafZiChief : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (ZSetting L1 L2 S) →
    (IsL2Quot 2 (oTwoQuot ↥L1)) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsZi L1 S) ⊥ ∧
      dsZi L1 S = dsOmega1 (centerOf (dsQ L1 L2 S)) ∧
      dsZ S = dsZi L1 S ⊓ Subgroup.centralizer (S : Set G) ∧
      (∀ x ∈ L1 ⊔ bigB L1 L2 S, IsPGroup 2 (Subgroup.zpowers x) →
        (∀ e ∈ dsZi L1 S, ⁅x, e⁆ = 1) → x ∈ dsQ L1 L2 S)

@[expose] def LeafBruhat : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G},
    (Hyp111R L1 L2 S) →
    (IsL2Quot 2 (oTwoQuot ↥L1) ∨ Nonempty (oTwoQuot ↥L1 ≃* Equiv.Perm (Fin 3))) →
    ∀ s ∈ L1 ⊔ bigB L1 L2 S, s ∉ bigB L1 L2 S →
      ∀ g ∈ L1 ⊔ bigB L1 L2 S, g ∈ bigB L1 L2 S ∨
        ∃ b₁ ∈ bigB L1 L2 S, ∃ b₂ ∈ bigB L1 L2 S, g = b₁ * s * b₂

@[expose] def LeafFaithfulA5 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P L E K : Subgroup G},
    (L ≤ P) →
    (P ≤ Subgroup.normalizer (L : Set G)) →
    (E ≤ P) →
    (P ≤ Subgroup.normalizer (E : Set G)) →
    (P ≤ Subgroup.normalizer (K : Set G)) →
    (IsElemSec K E) →
    (K.relIndex E ≤ 16) →
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (∀ q ∈ pCoreOf 2 P, ∀ e ∈ E, ⁅q, e⁆ ∈ K) →
    (∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ K) →
    A5Chief P L E K

@[expose] def LeafChiefOfA5 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P L E K : Subgroup G},
    (L ≤ P) →
    (P ≤ Subgroup.normalizer (L : Set G)) →
    (E ≤ P) →
    (P ≤ Subgroup.normalizer (E : Set G)) →
    (P ≤ Subgroup.normalizer (K : Set G)) →
    (IsElemSec K E) →
    (K.relIndex E ≤ 16) →
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (perfectCore L = L) →
    (∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ K) →
    A5Chief P L E K

@[expose] def LeafM2 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L P S : Subgroup G},
    (A5Par L P) →
    (IsSylowTwoOf S P) →
    (pCoreOf 2 P ≤ S) →
    (pCoreOf 2 P).relIndex S ∣ 8 ∧ Odd ((pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P))) ∧
      (∀ d ∈ P ⊓ Subgroup.normalizer (S : Set G), orderOf d = 3 → (pCoreOf 2 P).relIndex S = 4)

@[expose] def LeafM3 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P L E K T : Subgroup G},
    (A5Chief P L E K) →
    (IsSylowTwoOf T L) →
    (NatSec L K E →
        (∀ X : Subgroup G, K ≤ X → X ≤ E →
          L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
            X = K ∨ X = ⁅E, T⁆ ⊔ K ∨ X = E) ∧
        K.relIndex (⁅E, T⁆ ⊔ K) = 4 ∧
        (∀ t ∈ T, ∀ f ∈ ⁅E, T⁆ ⊔ K, ⁅f, t⁆ ∈ K) ∧
        (∀ e ∈ E, (∀ t ∈ T, ⁅e, t⁆ ∈ K) → e ∈ ⁅E, T⁆ ⊔ K) ∧
        (∀ s ∈ T ⊔ pCoreOf 2 P, s ∉ pCoreOf 2 P → ∀ e ∈ E, e ∉ ⁅E, T⁆ ⊔ K → ⁅e, s⁆ ∉ K)) ∧
      (¬ NatSec L K E →
        (∀ X : Subgroup G, K ≤ X → X ≤ E →
          L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
            X = K ∨ X = ⁅⁅E, T⁆, T⁆ ⊔ K ∨ X = ⁅E, T⁆ ⊔ K ∨ X = E) ∧
        K.relIndex (⁅⁅E, T⁆, T⁆ ⊔ K) = 2 ∧ K.relIndex (⁅E, T⁆ ⊔ K) = 8 ∧
        (∀ t ∈ T, ∀ f ∈ ⁅⁅E, T⁆, T⁆ ⊔ K, ⁅f, t⁆ ∈ K) ∧
        (∀ e ∈ E, (∀ t ∈ T, ⁅e, t⁆ ∈ K) → e ∈ ⁅⁅E, T⁆, T⁆ ⊔ K) ∧
        (∀ d ∈ L ⊓ Subgroup.normalizer (T : Set G), orderOf d = 3 →
          FixFree (⁅⁅E, T⁆, T⁆ ⊔ K) (⁅E, T⁆ ⊔ K) d))

@[expose] def LeafM4 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P L E K T X Y : Subgroup G},
    (A5Chief P L E K) →
    (IsSylowTwoOf T L) →
    (X ≤ T ⊔ pCoreOf 2 P) →
    (⁅⁅E, X⁆, X⁆ ≤ K) →
    (¬ ⁅E, X⁆ ≤ K) →
    (∀ x ∈ X, (∀ e ∈ E, ⁅x, e⁆ ∈ K) → x ∈ pCoreOf 2 P) →
    (K ≤ Y) →
    (Y ≤ E) →
    (∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ K) →
    (Y.relIndex E ≤ (X ⊓ pCoreOf 2 P).relIndex X) →
    NatSec L K E ∧ X ⊔ pCoreOf 2 P = T ⊔ pCoreOf 2 P ∧ Y.relIndex E = 4

@[expose] def LeafM5 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L T : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (IsSylowTwoOf T L) →
    (∀ X : Subgroup G, pCoreOf 2 L ≤ X → X ≤ T →
        L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
          X = pCoreOf 2 L ∨ X = T) ∧
      (∀ d ∈ L ⊓ Subgroup.normalizer (T : Set G), orderOf d = 3 → FixFree (pCoreOf 2 L) T d)

@[expose] def LeafM6 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P L V Z : Subgroup G},
    (A5Chief P L V Z) →
    (¬ NatSec L Z V) →
    (Nat.card Z = 2) →
    (⁅V, V⁆ ≠ ⊥) →
    Nat.card {x : ↥V | x ^ 2 = 1} = 12

@[expose] def LeafM7 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L P : Subgroup G} {d k : G},
    (S3Par L P d) →
    (k ∈ L) →
    (orderOf k = 3) →
    (dsFrattini (pCoreOf 2 P)).relIndex (pCoreOf 2 P) = 16 ∧
      (pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P)) ∣ 6 ∧
      (S3Type2 P k d ∨ S3Type1 P L k d)

@[expose] def LeafS3Module : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L Y T : Subgroup G} {k : G},
    (Nonempty (oTwoQuot ↥L ≃* Equiv.Perm (Fin 3))) →
    (IsElemAbelian 2 Y) →
    (L ≤ Subgroup.normalizer (Y : Set G)) →
    (∀ q ∈ pCoreOf 2 L, ∀ y ∈ Y, ⁅q, y⁆ = 1) →
    (k ∈ L) →
    (orderOf k = 3) →
    (FixFree ⊥ Y k) →
    (IsSylowTwoOf T L) →
    Nat.card Y = Nat.card ↥(Y ⊓ Subgroup.centralizer (T : Set G)) ^ 2

@[expose] def LeafM8a : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {V Z : Subgroup G},
    (IsElemSec Z V) →
    (Nat.card Z = 2) →
    (⁅V, V⁆ = Z) →
    (centerOf V ≤ Z) →
    ∀ g ∈ Subgroup.normalizer (V : Set G), (∀ x ∈ V, ⁅g, x⁆ ∈ Z) →
      ∃ v ∈ V, g * v⁻¹ ∈ Subgroup.centralizer (V : Set G)

@[expose] def LeafM8b : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {V Z : Subgroup G},
    (IsElemSec Z V) →
    (Nat.card Z = 2) →
    (⁅V, V⁆ = Z) →
    (centerOf V ≤ Z) →
    (Nat.card V = 32) →
    (Nat.card {x : ↥V | x ^ 2 = 1} = 12) →
    IsQ8D8 ↥V

@[expose] def LeafShort2OfA5 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (CharTwo L) →
    (IsElemAbelian 2 (pCoreOf 2 L)) →
    (Nat.card (pCoreOf 2 L) = 16) →
    IsShort2 L

@[expose] def LeafLin2OfNatural : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (CharTwo L) →
    (IsElemAbelian 2 (pCoreOf 2 L)) →
    (Nat.card (pCoreOf 2 L) = 16) →
    (NatSec L ⊥ (pCoreOf 2 L)) →
    IsLin2Type L 2

@[expose] def LeafAlt5OfOrth : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (CharTwo L) →
    (IsElemAbelian 2 (pCoreOf 2 L)) →
    (Nat.card (pCoreOf 2 L) = 16) →
    (¬ NatSec L ⊥ (pCoreOf 2 L)) →
    IsAltType L 5

@[expose] def LeafOmega4MinusOfOrth : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (CharTwo L) →
    (IsElemAbelian 2 (pCoreOf 2 L)) →
    (Nat.card (pCoreOf 2 L) = 16) →
    (¬ NatSec L ⊥ (pCoreOf 2 L)) →
    IsOmega4MinusType L 1

@[expose] def LeafDSANoField : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    S = (S ⊓ L1) ⊔ dsQ L1 L2 S ∧ S = (S ⊓ L2) ⊔ dsQ L2 L1 S ∧
      bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)

@[expose] def LeafDSACaseIOffender : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    (⁅dsZi L2 S, L2⁆ ≠ ⊥) →
    ¬ dsZi L1 S ≤ dsQ L2 L1 S ∧ ¬ dsZi L2 S ≤ dsQ L1 L2 S ∧ NatSec L1 ⊥ (dsZi L1 S) ∧ NatSec L2 ⊥ (dsZi L2 S) ∧
      dsZi L1 S ⊓ dsZi L2 S = dsZi L2 S ⊓ dsQ L1 L2 S ∧ dsZi L1 S ⊓ dsZi L2 S = dsZi L1 S ⊓ dsQ L2 L1 S ∧ Nat.card ↥(dsZi L1 S ⊓ dsZi L2 S) = 4

@[expose] def LeafDSACaseIFrattini : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    (⁅dsZi L2 S, L2⁆ ≠ ⊥) →
    dsQ L1 L2 S = dsZi L1 S ∧ dsQ L2 L1 S = dsZi L2 S

@[expose] def LeafDSACaseIStep4 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    (⁅dsZi L2 S, L2⁆ ≠ ⊥) →
    dsQ L1 L2 S ⊔ dsQ L2 L1 S = S ∧ Nat.card S = 2 ^ 6 ∧
      (IsElemAbelian 2 (dsQ L1 L2 S) ∧ Nat.card (dsQ L1 L2 S) = 16) ∧ (IsElemAbelian 2 (dsQ L2 L1 S) ∧ Nat.card (dsQ L2 L1 S) = 16)

@[expose] def LeafDSAA6 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    (⁅dsZi L2 S, L2⁆ ≠ ⊥) →
    bigB L1 L2 S ≤ L1 ⊓ L2

@[expose] def LeafDSACaseIIOmega : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L2 S, L2⁆ = ⊥) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    dsOmega1 (centerOf (dsQ L2 L1 S)) = dsZ S ∧ dsZ S ≤ dsFrattini (dsQ L2 L1 S)

@[expose] def LeafDSACaseIIQQ : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L2 S, L2⁆ = ⊥) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    dsQ L1 L2 S ⊔ dsQ L2 L1 S = S

@[expose] def LeafDSACaseIIStep3 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L2 S, L2⁆ = ⊥) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    dsZi L1 S ≤ dsQ L2 L1 S

@[expose] def LeafDSACaseIIStep4 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L2 S, L2⁆ = ⊥) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    ¬ dsZi L1 S ≤ dsQ L2 L1 S

@[expose] def LeafDSAVertex : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSAHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    (⁅dsZi L2 S, L2⁆ ≠ ⊥) →
    IsShort2 L1 ∧ IsLin2Type L1 2 ∧ perfectCore L1 = L1 ∧ S ≤ L1 ∧
      ¬ centerOf S ≤ Subgroup.centralizer (L1 : Set G)

@[expose] def LeafDSBReduce : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G},
    (DSBHyp0 L1 L2 S) →
    DSBHyp L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2))

@[expose] def LeafDSBA5Vertex : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    S = (S ⊓ L1) ⊔ dsQ L1 L2 S ∧ (dsQ L1 L2 S).relIndex S = 4 ∧ dsQ L1 L2 S ≤ L1

@[expose] def LeafDSBS3Vertex : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    S = (S ⊓ L2) ⊔ dsQ L2 L1 S ∧ (dsQ L2 L1 S).relIndex S = 2 ∧
      (∀ d ∈ borelOf L1 S, orderOf d = 3 → ∀ l ∈ L2, ⁅d, l⁆ ∈ dsQ L2 L1 S) ∧
      Nat.card (dsQ L2 L1 S) = 2 * Nat.card (dsQ L1 L2 S)

@[expose] def LeafDSBJZ2 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ = ⊥) →
    (dsOmega1 (centerOf (dsQ L1 L2 S)) = dsZ S ∧ dsZ S ≤ dsFrattini (dsQ L1 L2 S)) ∧
      (dsZi L2 S = dsOmega1 (centerOf (dsQ L2 L1 S)) ∧
        (∀ k ∈ L2, orderOf k = 3 → FixFree ⊥ (dsZi L2 S) k) ∧
        Nat.card (dsZi L2 S) = Nat.card (dsZ S) ^ 2 ∧ Nat.card (dsZ S) ≤ 4 ∧
        (∀ d ∈ borelOf L1 S, orderOf d = 3 → ∀ z ∈ dsZi L2 S, ⁅d, z⁆ = 1)) ∧
      dsZi L2 S ≤ dsQ L1 L2 S

@[expose] def LeafDSBJV1 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ = ⊥) →
    Nat.card (dsZ S) = 2 ∧ A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsV1 L1 L2 S) (dsZ S) ∧
      ¬ NatSec L1 (dsZ S) (dsV1 L1 L2 S) ∧ ⁅dsV1 L1 L2 S, dsV1 L1 L2 S⁆ = dsZ S ∧
      dsV1 L1 L2 S ≤ dsQ L1 L2 S

@[expose] def LeafDSBJQ1 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ = ⊥) →
    dsQ L1 L2 S = dsV1 L1 L2 S ∧ pCoreOf 2 L1 = dsQ L1 L2 S ∧ IsQ8D8 ↥(pCoreOf 2 L1)

@[expose] def LeafDSBJQ2 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ = ⊥) →
    pCoreOf 2 L2 = dsQ L2 L1 S ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6

@[expose] def LeafDSBUQQ : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    dsQ L1 L2 S ⊔ dsQ L2 L1 S = S ∧ (dsQ L1 L2 S ⊓ dsQ L2 L1 S).relIndex (dsQ L1 L2 S) = 2 ∧ ¬ dsZi L1 S ≤ dsQ L2 L1 S

@[expose] def LeafDSBUQ1 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    pCoreOf 2 L1 = dsQ L1 L2 S ∧ dsQ L1 L2 S = dsZi L1 S ∧ CharTwo L1 ∧ IsElemAbelian 2 (pCoreOf 2 L1) ∧
      Nat.card (pCoreOf 2 L1) = 16 ∧ ¬ NatSec L1 ⊥ (pCoreOf 2 L1) ∧ Nat.card (dsQ L2 L1 S) = 32 ∧
      Nat.card (dsZ S) = 2

@[expose] def LeafDSBUQ2 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (DSBHyp L1 L2 S) →
    (⁅dsZi L1 S, L1⁆ ≠ ⊥) →
    pCoreOf 2 L2 = dsQ L2 L1 S ∧ dsFrattini (dsQ L2 L1 S) = dsZ S ∧ IsSpecialPow 2 2 2 ↥(pCoreOf 2 L2)

@[expose] def LeafDSBZSU : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (Hyp111R L1 L2 S) →
    (Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3))) →
    (IsSpecialPow 2 2 2 ↥(pCoreOf 2 L2)) →
    ¬ centerOf S ≤ Subgroup.centralizer (L1 : Set G)

@[expose] def LeafDSBZSJ : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G},
    (Hyp111R L1 L2 S) →
    (IsL2Quot 2 (oTwoQuot ↥L1)) →
    (IsQ8D8 ↥(pCoreOf 2 L1)) →
    ¬ centerOf S ≤ Subgroup.centralizer (L2 : Set G)

end CFSG.GH74.QTGen4.DSGen4
