module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def Stmt5_1_22_one_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      ((T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) : Subgroup G) : Set G) *
          (B : Set G) = (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) : Set G) ∧
        Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ≤ M

end CFSG.Quasithin.H13
