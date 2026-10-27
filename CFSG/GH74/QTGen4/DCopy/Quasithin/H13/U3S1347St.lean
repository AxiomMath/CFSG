module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.U3S134Defs

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Stmt13_4_7L2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : A6.Setting134 G T L V)
    (H₁ H₂ : Subgroup G), Hyp1347 T H₁ H₂ → oTwoRes H₂ = l2Of S →

    (InH T (H₁ ⊔ H₂) ∧ ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G) ∧
      quasithinOmegaOneCenter T = fsuV1 T V ∧
      cZ T H₁ ⊔ cZ T H₂ = quasithinOmegaOneCenter T ∧ cZ T H₁ ⊓ cZ T H₂ = ⊥ ∧
      Nat.card ↥(cZ T H₁) = 2 ∧ Nat.card ↥(cZ T H₂) = 2 ∧
      (Concl1347i T H₁ H₂ ∨ Concl1347ii T H₁ H₂ ∨ Concl1347iii T H₁ H₂ ∨
        Concl1347iv T H₁ H₂)) ∧

    (Concl1347ii T H₁ H₂ → ∀ X : Subgroup G, InH (H₁ ⊔ H₂) X →
      X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T → X = H₁ ⊔ H₂) ∧

    ¬ Concl1347iii T H₁ H₂ ∧

    ¬ Concl1347iv T H₁ H₂ ∧
      (Concl1347ii T H₁ H₂ → ⁅oTwoRes H₂, thompsonJi T 1⁆ = oTwoRes H₂)

end CFSG.Quasithin.H13.U3
