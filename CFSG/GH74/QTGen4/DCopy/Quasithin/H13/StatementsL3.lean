module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt5_2_3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H V : Subgroup G) (m : ℕ), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    M ≤ Subgroup.normalizer (L : Set G) →
    2 ≤ m → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 m →
    IsHStar T M H → 1 < E1.nParam H →
    V ≤ L ⊔ T → IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) → ⁅V, L⁆ ≠ ⊥ →
      (m = 2 ∧ IsA5ModuleSum L ⁅V, L⁆ ∧ CentralizerComponentClause T H) ∨
      Nonempty (G ≃* NativeSporadic.M23) ∨ Alt12_2_2Lie G

@[expose] def Stmt6_2_20_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (m : ℕ), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    M ≤ Subgroup.normalizer (L : Set G) →
    2 ≤ m → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 m →
    V ≤ L ⊔ T → IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) → ⁅V, L⁆ ≠ ⊥ →
      (m = 2 ∧ IsA5ModuleSum L ⁅V, L⁆ ∧
        ∀ H : Subgroup G, IsHStar T M H → 1 < E1.nParam H → CentralizerComponentClause T H) ∨
      Alt12_2_2Lie G ∨
      Nonempty (G ≃* NativeSporadic.M22) ∨ Nonempty (G ≃* NativeSporadic.M23)

end CFSG.Quasithin.H13
