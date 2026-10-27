module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def Stmt3_3_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T →
      (∀ M L : Subgroup G, quasithinIsMaxTwoLocal M → T ≤ M → quasithinIsMaximalLocal T L →
        L ≤ M → CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
          Subgroup.normalizer (T : Set G) ≤ M) ∧
      ∀ L : Subgroup G, quasithinIsMaximalLocal T L →
        CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
        (quasithinIsMaxTwoLocal (Subgroup.normalizer (conjClosure L T : Set G)) ∧
          L ⊔ T ≤ Subgroup.normalizer (conjClosure L T : Set G) ∧
          ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' →
            M' = Subgroup.normalizer (conjClosure L T : Set G)) ∧
        (∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧ quasithinIsMaxTwoLocal M₁ ∧
          quasithinIsMaxTwoLocal M₂ ∧ T ≤ M₁ ∧ T ≤ M₂) ∧
        (∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H) ∧
        Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (conjClosure L T : Set G) ∧
        ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H →
          IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (conjClosure L T : Set G)) ∧
          ¬ H ≤ Subgroup.normalizer (T : Set G)

end CFSG.Quasithin.H13
