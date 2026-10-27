module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.StatementsL1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def StmtFiveSelectedMenu_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      (∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL n 2 1) ∨
      (∃ (K : Type) (_ : Field K), Nat.card K = 2 ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
          ↥(⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ : Subgroup (ModGL .G2 K)))) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        alternatingGroup (Fin 6)) ∨
      ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ ∃ V : Subgroup G, V ≠ ⊥ ∧ IsElemAbelian 2 V ∧
        L ≤ Subgroup.normalizer (V : Set G) ∧
        pCoreOf 2 L ≤ L ⊓ Subgroup.centralizer (V : Set G) ∧
        L ⊓ Subgroup.centralizer (V : Set G) < L ∧
        ∃ φ : ↥L →* ↥(alternatingGroup (Fin n)), Function.Surjective φ ∧
          φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L

@[expose] def StmtFiveCandidateMenu_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      SteinbergBQ.QTFiveCandidate (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Stmt12_2_13_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ Alt12_2_2 G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      (∃ v ∈ V, v ≠ 1 ∧
        ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∨
      (∃ n : ℕ, (n = 3 ∨ n = 4) ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
        LieModel G .PSL (n + 1) 2 1) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        Nonempty (G ≃* alternatingGroup (Fin 9))) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        Nonempty (G ≃* NativeSporadic.M24))

@[expose] def Stmt12_4_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ Alt12_2_2 G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        Nat.card V = 2 ^ 10 →
        ¬ Subgroup.centralizer ((V ⊓ quasithinOmegaOneCenter T : Subgroup G) : Set G) ≤
          Subgroup.normalizer (L : Set G))

@[expose] def Stmt12_7_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ Alt12_2_2 G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    (∃ _ : ((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal,
      CFSG.IsQuasisimple (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ∧
      Nat.card (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L)) = 3 ∧
      Nonempty ((↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ⧸
          Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ≃*
        alternatingGroup (Fin 6))) →
      Nonempty (G ≃* NativeSporadic.M24) ∨ Nonempty (G ≃* NativeSporadic.He)

@[expose] def Stmt10_0_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G)

@[expose] def Stmt11_0_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    ¬ ∃ n : ℕ, 1 < n ∧
      ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 n ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .G2 0 2 n)

@[expose] def Stmt4_3_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    M ≤ Subgroup.normalizer (L : Set G) →
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) →
      (∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ≤ M' → M' = M) ∧
      ∀ S : Subgroup G, S ≤ T → QuasithinUnique.IsSylowTwoOf (S ⊓ L) L →
        Subgroup.normalizer (S : Set G) ≤ M

end CFSG.Quasithin.H13
