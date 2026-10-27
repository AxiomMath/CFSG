module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def Stmt3_3_13LT_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D H : Subgroup G), Hyp331 G T M L D →
    InH T H → H ≤ L ⊔ T → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) →
      D ≤ Subgroup.normalizer (H : Set G)

@[expose] def Obl3_3_13LT_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D H K : Subgroup G), Hyp331 G T M L D → InH T H →
    H ≤ L ⊔ T → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) → pCoreOf 2 (H ⊔ D) ≠ ⊥ →
    K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) →
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G)

end CFSG.Quasithin.H13
