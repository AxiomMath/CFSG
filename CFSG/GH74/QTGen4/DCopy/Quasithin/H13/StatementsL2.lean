module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt13_3_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      QT13Five (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      (T ≤ Subgroup.normalizer (K : Set G) ∧ quasithinIsMaximalLocal T K ∧
        quasithinIsMaxTwoLocal (Subgroup.normalizer (K : Set G)) ∧
        ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → K ⊔ T ≤ M →
          M = Subgroup.normalizer (K : Set G)) ∧
      ((∃ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V) ∧
        ∀ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V →
          V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧ FSU G T K V ∧
          ∃ _ : IsMulCommutative ↥V, Modules13_3_2 K V) ∧
      ((¬ quasithinO2QuotientIso K (alternatingGroup (Fin 5)) ∨
          quasithinO2QuotientIso L (alternatingGroup (Fin 5))) → QTH13 G T K)

@[expose] def Stmt12_2_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T →
      Alt12_2_2 G ∨
      ∀ L : Subgroup G, quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
        CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
          T ≤ Subgroup.normalizer (L : Set G) ∧
          (∃ V : Subgroup G, IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) ∧
          ∀ V : Subgroup G, IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
            (V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧
              IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) ∧ FSU G T L V) ∧
            (∀ m ∈ Subgroup.normalizer (L : Set G),
              CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
            (Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) ∨
              V ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
            ∃ _ : IsMulCommutative ↥V, Modules12_2_2 L V

@[expose] def Stmt12_6_34_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ Alt12_2_2 G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    (∃ φ : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) →
      Nat.card V = 2 ^ 4 ∧ L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 4 1

end CFSG.Quasithin.H13
