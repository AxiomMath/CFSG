module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

class DSLeaf (L : Prop) : Prop where
  holds : L

theorem sylow_s [DSLeaf LeafSylowS] {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) :
    IsSylowTwoOf S (bigB L1 L2 S) ∧ IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) ∧
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S :=
  DSLeaf.holds (L := LeafSylowS) h

theorem rank_bounds [DSLeaf LeafRankBounds] {G : Type} [Group G] [Finite4 G] :
    (∀ R : Subgroup G, IsPGroup 2 R → (dsFrattini R).relIndex R ≤ 16) ∧
      (∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 16) :=
  DSLeaf.holds (L := LeafRankBounds)

theorem frattini_faithful [DSLeaf LeafFrattiniFaithful] {G : Type} [Group G] [Finite G] {P : Subgroup G} (h : CharTwo P) :
    ∀ p ∈ P, (∀ q ∈ pCoreOf 2 P, ⁅p, q⁆ ∈ dsFrattini (pCoreOf 2 P)) → p ∈ pCoreOf 2 P :=
  DSLeaf.holds (L := LeafFrattiniFaithful) h

theorem frattini_chief [DSLeaf LeafFrattiniChief] {G : Type} [Group G] [Finite4 G] {L P : Subgroup G} (h : A5Par L P) :
    A5Chief P L (pCoreOf 2 P) (dsFrattini (pCoreOf 2 P)) :=
  DSLeaf.holds (L := LeafFrattiniChief) h

theorem zi_structure [DSLeaf LeafZiStructure] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : ZSetting L1 L2 S) :
    dsZ S ≠ ⊥ ∧ dsZ S ≤ dsZi L1 S ∧ dsZi L1 S ≤ dsOmega1 (centerOf (dsQ L1 L2 S)) ∧
      IsElemAbelian 2 (dsOmega1 (centerOf (dsQ L1 L2 S))) ∧
      Nat.card (dsOmega1 (centerOf (dsQ L1 L2 S))) ≤ 16 ∧
      L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsZi L1 S : Set G) ∧
      L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsOmega1 (centerOf (dsQ L1 L2 S)) : Set G) :=
  DSLeaf.holds (L := LeafZiStructure) h

theorem zi_chief [DSLeaf LeafZiChief] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : ZSetting L1 L2 S) (hq : IsL2Quot 2 (oTwoQuot ↥L1)) (hnc : ⁅dsZi L1 S, L1⁆ ≠ ⊥) :
    A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsZi L1 S) ⊥ ∧
      dsZi L1 S = dsOmega1 (centerOf (dsQ L1 L2 S)) ∧
      dsZ S = dsZi L1 S ⊓ Subgroup.centralizer (S : Set G) ∧
      (∀ x ∈ L1 ⊔ bigB L1 L2 S, IsPGroup 2 (Subgroup.zpowers x) →
        (∀ e ∈ dsZi L1 S, ⁅x, e⁆ = 1) → x ∈ dsQ L1 L2 S) :=
  DSLeaf.holds (L := LeafZiChief) h hq hnc

theorem bruhat [DSLeaf LeafBruhat] {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) (hv : IsL2Quot 2 (oTwoQuot ↥L1) ∨ Nonempty (oTwoQuot ↥L1 ≃* Equiv.Perm (Fin 3))) :
    ∀ s ∈ L1 ⊔ bigB L1 L2 S, s ∉ bigB L1 L2 S →
      ∀ g ∈ L1 ⊔ bigB L1 L2 S, g ∈ bigB L1 L2 S ∨
        ∃ b₁ ∈ bigB L1 L2 S, ∃ b₂ ∈ bigB L1 L2 S, g = b₁ * s * b₂ :=
  DSLeaf.holds (L := LeafBruhat) h hv

theorem faithful_a5 [DSLeaf LeafFaithfulA5] {G : Type} [Group G] [Finite G] {P L E K : Subgroup G} (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hEP : E ≤ P) (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hsec : IsElemSec K E) (hcard : K.relIndex E ≤ 16) (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hcore : ∀ q ∈ pCoreOf 2 P, ∀ e ∈ E, ⁅q, e⁆ ∈ K) (hnt : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ K) :
    A5Chief P L E K :=
  DSLeaf.holds (L := LeafFaithfulA5) hLP hPL hEP hPE hPK hsec hcard hq hcore hnt

theorem m2 [DSLeaf LeafM2] {G : Type} [Group G] [Finite4 G] {L P S : Subgroup G} (h : A5Par L P) (hS : IsSylowTwoOf S P) (hQS : pCoreOf 2 P ≤ S) :
    (pCoreOf 2 P).relIndex S ∣ 8 ∧ Odd ((pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P))) ∧
      (∀ d ∈ P ⊓ Subgroup.normalizer (S : Set G), orderOf d = 3 → (pCoreOf 2 P).relIndex S = 4) :=
  DSLeaf.holds (L := LeafM2) h hS hQS

theorem m3 [DSLeaf LeafM3] {G : Type} [Group G] [Finite G] {P L E K T : Subgroup G} (h : A5Chief P L E K) (hT : IsSylowTwoOf T L) :
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
          FixFree (⁅⁅E, T⁆, T⁆ ⊔ K) (⁅E, T⁆ ⊔ K) d)) :=
  DSLeaf.holds (L := LeafM3) h hT

theorem m4 [DSLeaf LeafM4] {G : Type} [Group G] [Finite G] {P L E K T X Y : Subgroup G} (h : A5Chief P L E K) (hT : IsSylowTwoOf T L) (hX : X ≤ T ⊔ pCoreOf 2 P) (hq : ⁅⁅E, X⁆, X⁆ ≤ K) (hnt : ¬ ⁅E, X⁆ ≤ K) (hfaith : ∀ x ∈ X, (∀ e ∈ E, ⁅x, e⁆ ∈ K) → x ∈ pCoreOf 2 P) (hKY : K ≤ Y) (hYE : Y ≤ E) (hYc : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ K) (hcard : Y.relIndex E ≤ (X ⊓ pCoreOf 2 P).relIndex X) :
    NatSec L K E ∧ X ⊔ pCoreOf 2 P = T ⊔ pCoreOf 2 P ∧ Y.relIndex E = 4 :=
  DSLeaf.holds (L := LeafM4) h hT hX hq hnt hfaith hKY hYE hYc hcard

theorem m5 [DSLeaf LeafM5] {G : Type} [Group G] [Finite G] {L T : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    (∀ X : Subgroup G, pCoreOf 2 L ≤ X → X ≤ T →
        L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
          X = pCoreOf 2 L ∨ X = T) ∧
      (∀ d ∈ L ⊓ Subgroup.normalizer (T : Set G), orderOf d = 3 → FixFree (pCoreOf 2 L) T d) :=
  DSLeaf.holds (L := LeafM5) hq hT

theorem m6 [DSLeaf LeafM6] {G : Type} [Group G] [Finite G] {P L V Z : Subgroup G} (h : A5Chief P L V Z) (hn : ¬ NatSec L Z V) (hZ : Nat.card Z = 2) (hV : ⁅V, V⁆ ≠ ⊥) :
    Nat.card {x : ↥V | x ^ 2 = 1} = 12 :=
  DSLeaf.holds (L := LeafM6) h hn hZ hV

theorem m7 [DSLeaf LeafM7] {G : Type} [Group G] [Finite4 G] {L P : Subgroup G} {d k : G} (h : S3Par L P d) (hk : k ∈ L) (hko : orderOf k = 3) :
    (dsFrattini (pCoreOf 2 P)).relIndex (pCoreOf 2 P) = 16 ∧
      (pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P)) ∣ 6 ∧
      (S3Type2 P k d ∨ S3Type1 P L k d) :=
  DSLeaf.holds (L := LeafM7) h hk hko

theorem s3_module [DSLeaf LeafS3Module] {G : Type} [Group G] [Finite G] {L Y T : Subgroup G} {k : G} (hq : Nonempty (oTwoQuot ↥L ≃* Equiv.Perm (Fin 3))) (hY : IsElemAbelian 2 Y) (hLY : L ≤ Subgroup.normalizer (Y : Set G)) (hc : ∀ q ∈ pCoreOf 2 L, ∀ y ∈ Y, ⁅q, y⁆ = 1) (hk : k ∈ L) (hko : orderOf k = 3) (hff : FixFree ⊥ Y k) (hT : IsSylowTwoOf T L) :
    Nat.card Y = Nat.card ↥(Y ⊓ Subgroup.centralizer (T : Set G)) ^ 2 :=
  DSLeaf.holds (L := LeafS3Module) hq hY hLY hc hk hko hff hT

theorem m8a [DSLeaf LeafM8a] {G : Type} [Group G] [Finite G] {V Z : Subgroup G} (hs : IsElemSec Z V) (hZ : Nat.card Z = 2) (hc : ⁅V, V⁆ = Z) (hz : centerOf V ≤ Z) :
    ∀ g ∈ Subgroup.normalizer (V : Set G), (∀ x ∈ V, ⁅g, x⁆ ∈ Z) →
      ∃ v ∈ V, g * v⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
  DSLeaf.holds (L := LeafM8a) hs hZ hc hz

theorem m8b [DSLeaf LeafM8b] {G : Type} [Group G] [Finite G] {V Z : Subgroup G} (hs : IsElemSec Z V) (hZ : Nat.card Z = 2) (hc : ⁅V, V⁆ = Z) (hz : centerOf V ≤ Z) (hV : Nat.card V = 32) (hn : Nat.card {x : ↥V | x ^ 2 = 1} = 12) :
    IsQ8D8 ↥V :=
  DSLeaf.holds (L := LeafM8b) hs hZ hc hz hV hn

theorem short2_of_a5 [DSLeaf LeafShort2OfA5] {G : Type} [Group G] [Finite G] {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L) (he : IsElemAbelian 2 (pCoreOf 2 L)) (hn : Nat.card (pCoreOf 2 L) = 16) :
    IsShort2 L :=
  DSLeaf.holds (L := LeafShort2OfA5) hq hc he hn

theorem lin2_of_natural [DSLeaf LeafLin2OfNatural] {G : Type} [Group G] [Finite G] {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L) (he : IsElemAbelian 2 (pCoreOf 2 L)) (hn : Nat.card (pCoreOf 2 L) = 16) (hnat : NatSec L ⊥ (pCoreOf 2 L)) :
    IsLin2Type L 2 :=
  DSLeaf.holds (L := LeafLin2OfNatural) hq hc he hn hnat

theorem omega4_minus_of_orth [DSLeaf LeafOmega4MinusOfOrth] {G : Type} [Group G] [Finite G] {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L) (he : IsElemAbelian 2 (pCoreOf 2 L)) (hn : Nat.card (pCoreOf 2 L) = 16) (hnat : ¬ NatSec L ⊥ (pCoreOf 2 L)) :
    IsOmega4MinusType L 1 :=
  DSLeaf.holds (L := LeafOmega4MinusOfOrth) hq hc he hn hnat

theorem dsa_no_field [DSLeaf LeafDSANoField] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) :
    S = (S ⊓ L1) ⊔ dsQ L1 L2 S ∧ S = (S ⊓ L2) ⊔ dsQ L2 L1 S ∧
      bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) :=
  DSLeaf.holds (L := LeafDSANoField) h

theorem dsa_case_i_offender [DSLeaf LeafDSACaseIOffender] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥) (c2 : ⁅dsZi L2 S, L2⁆ ≠ ⊥) :
    ¬ dsZi L1 S ≤ dsQ L2 L1 S ∧ ¬ dsZi L2 S ≤ dsQ L1 L2 S ∧ NatSec L1 ⊥ (dsZi L1 S) ∧ NatSec L2 ⊥ (dsZi L2 S) ∧
      dsZi L1 S ⊓ dsZi L2 S = dsZi L2 S ⊓ dsQ L1 L2 S ∧ dsZi L1 S ⊓ dsZi L2 S = dsZi L1 S ⊓ dsQ L2 L1 S ∧ Nat.card ↥(dsZi L1 S ⊓ dsZi L2 S) = 4 :=
  DSLeaf.holds (L := LeafDSACaseIOffender) h c1 c2

theorem dsa_case_i_frattini [DSLeaf LeafDSACaseIFrattini] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥) (c2 : ⁅dsZi L2 S, L2⁆ ≠ ⊥) :
    dsQ L1 L2 S = dsZi L1 S ∧ dsQ L2 L1 S = dsZi L2 S :=
  DSLeaf.holds (L := LeafDSACaseIFrattini) h c1 c2

theorem dsa_case_i_step4 [DSLeaf LeafDSACaseIStep4] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥) (c2 : ⁅dsZi L2 S, L2⁆ ≠ ⊥) :
    dsQ L1 L2 S ⊔ dsQ L2 L1 S = S ∧ Nat.card S = 2 ^ 6 ∧
      (IsElemAbelian 2 (dsQ L1 L2 S) ∧ Nat.card (dsQ L1 L2 S) = 16) ∧ (IsElemAbelian 2 (dsQ L2 L1 S) ∧ Nat.card (dsQ L2 L1 S) = 16) :=
  DSLeaf.holds (L := LeafDSACaseIStep4) h c1 c2

theorem dsaa6 [DSLeaf LeafDSAA6] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥) (c2 : ⁅dsZi L2 S, L2⁆ ≠ ⊥) :
    bigB L1 L2 S ≤ L1 ⊓ L2 :=
  DSLeaf.holds (L := LeafDSAA6) h c1 c2

theorem dsa_case_ii_omega [DSLeaf LeafDSACaseIIOmega] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) (c2 : ⁅dsZi L2 S, L2⁆ = ⊥) (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥) :
    dsOmega1 (centerOf (dsQ L2 L1 S)) = dsZ S ∧ dsZ S ≤ dsFrattini (dsQ L2 L1 S) :=
  DSLeaf.holds (L := LeafDSACaseIIOmega) h c2 c1

theorem dsa_case_iiqq [DSLeaf LeafDSACaseIIQQ] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) (c2 : ⁅dsZi L2 S, L2⁆ = ⊥) (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥) :
    dsQ L1 L2 S ⊔ dsQ L2 L1 S = S :=
  DSLeaf.holds (L := LeafDSACaseIIQQ) h c2 c1

theorem dsb_reduce [DSLeaf LeafDSBReduce] {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} (h : DSBHyp0 L1 L2 S) :
    DSBHyp L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)) :=
  DSLeaf.holds (L := LeafDSBReduce) h

theorem dsba5_vertex [DSLeaf LeafDSBA5Vertex] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) :
    S = (S ⊓ L1) ⊔ dsQ L1 L2 S ∧ (dsQ L1 L2 S).relIndex S = 4 ∧ dsQ L1 L2 S ≤ L1 :=
  DSLeaf.holds (L := LeafDSBA5Vertex) h

theorem dsbs3_vertex [DSLeaf LeafDSBS3Vertex] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) :
    S = (S ⊓ L2) ⊔ dsQ L2 L1 S ∧ (dsQ L2 L1 S).relIndex S = 2 ∧
      (∀ d ∈ borelOf L1 S, orderOf d = 3 → ∀ l ∈ L2, ⁅d, l⁆ ∈ dsQ L2 L1 S) ∧
      Nat.card (dsQ L2 L1 S) = 2 * Nat.card (dsQ L1 L2 S) :=
  DSLeaf.holds (L := LeafDSBS3Vertex) h

theorem dsbjz2 [DSLeaf LeafDSBJZ2] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) :
    (dsOmega1 (centerOf (dsQ L1 L2 S)) = dsZ S ∧ dsZ S ≤ dsFrattini (dsQ L1 L2 S)) ∧
      (dsZi L2 S = dsOmega1 (centerOf (dsQ L2 L1 S)) ∧
        (∀ k ∈ L2, orderOf k = 3 → FixFree ⊥ (dsZi L2 S) k) ∧
        Nat.card (dsZi L2 S) = Nat.card (dsZ S) ^ 2 ∧ Nat.card (dsZ S) ≤ 4 ∧
        (∀ d ∈ borelOf L1 S, orderOf d = 3 → ∀ z ∈ dsZi L2 S, ⁅d, z⁆ = 1)) ∧
      dsZi L2 S ≤ dsQ L1 L2 S :=
  DSLeaf.holds (L := LeafDSBJZ2) h cJ

theorem dsbjv1 [DSLeaf LeafDSBJV1] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) :
    Nat.card (dsZ S) = 2 ∧ A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsV1 L1 L2 S) (dsZ S) ∧
      ¬ NatSec L1 (dsZ S) (dsV1 L1 L2 S) ∧ ⁅dsV1 L1 L2 S, dsV1 L1 L2 S⁆ = dsZ S ∧
      dsV1 L1 L2 S ≤ dsQ L1 L2 S :=
  DSLeaf.holds (L := LeafDSBJV1) h cJ

theorem dsbjq1 [DSLeaf LeafDSBJQ1] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) :
    dsQ L1 L2 S = dsV1 L1 L2 S ∧ pCoreOf 2 L1 = dsQ L1 L2 S ∧ IsQ8D8 ↥(pCoreOf 2 L1) :=
  DSLeaf.holds (L := LeafDSBJQ1) h cJ

theorem dsbjq2 [DSLeaf LeafDSBJQ2] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) :
    pCoreOf 2 L2 = dsQ L2 L1 S ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6 :=
  DSLeaf.holds (L := LeafDSBJQ2) h cJ

theorem dsbuqq [DSLeaf LeafDSBUQQ] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cU : ⁅dsZi L1 S, L1⁆ ≠ ⊥) :
    dsQ L1 L2 S ⊔ dsQ L2 L1 S = S ∧ (dsQ L1 L2 S ⊓ dsQ L2 L1 S).relIndex (dsQ L1 L2 S) = 2 ∧ ¬ dsZi L1 S ≤ dsQ L2 L1 S :=
  DSLeaf.holds (L := LeafDSBUQQ) h cU

theorem dsbuq1 [DSLeaf LeafDSBUQ1] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cU : ⁅dsZi L1 S, L1⁆ ≠ ⊥) :
    pCoreOf 2 L1 = dsQ L1 L2 S ∧ dsQ L1 L2 S = dsZi L1 S ∧ CharTwo L1 ∧ IsElemAbelian 2 (pCoreOf 2 L1) ∧
      Nat.card (pCoreOf 2 L1) = 16 ∧ ¬ NatSec L1 ⊥ (pCoreOf 2 L1) ∧ Nat.card (dsQ L2 L1 S) = 32 ∧
      Nat.card (dsZ S) = 2 :=
  DSLeaf.holds (L := LeafDSBUQ1) h cU

theorem dsbuq2 [DSLeaf LeafDSBUQ2] {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cU : ⁅dsZi L1 S, L1⁆ ≠ ⊥) :
    pCoreOf 2 L2 = dsQ L2 L1 S ∧ dsFrattini (dsQ L2 L1 S) = dsZ S ∧ IsSpecialPow 2 2 2 ↥(pCoreOf 2 L2) :=
  DSLeaf.holds (L := LeafDSBUQ2) h cU

end CFSG.GH74.QTGen4.DSGen4
