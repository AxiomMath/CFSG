module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_23_offender_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
    ¬ IsMulCommutative ↥(conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) →
      ∃ hU : IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
          (Subgroup.centralizer (Z₁ : Set G)))),
        qhatInt (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
          (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) hU <
          2

@[expose] def Stmt5_1_23_faithful_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
    ∀ (hU : IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
        (Subgroup.centralizer (Z₁ : Set G)))))
      (A : Subgroup (MulAut ↥(tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
        (Subgroup.centralizer (Z₁ : Set G)))))),
      A ∈ @QhatStar _ (commGroupOfElemAbelian hU) _
        (autOn (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
          (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))) →
      qhatInt (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
          (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) hU <
          2 →
        ¬ A ≤ Subgroup.centralizer (autOn (tildeOf Z₁ (oTwoUpper H))
          (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) :
          Set (MulAut ↥(tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
            (Subgroup.centralizer (Z₁ : Set G))))))

end CFSG.Quasithin.H13
