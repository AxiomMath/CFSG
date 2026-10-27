module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Q3.Q3B1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores

@[expose] def MemberFreeSocleOuter3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        Subgroup.normalClosure (L : Set Y) = ⊤ → NonCommConnected (Q3B.conjClass L) →
          T.Normal → Subgroup.centralizer (T : Set Y) = ⊥ →
            (∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z') → False

@[expose] def D4OuterThree3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        Subgroup.normalClosure (L : Set Y) = ⊤ → NonCommConnected (Q3B.conjClass L) →
          T.Normal → Subgroup.centralizer (T : Set Y) = ⊥ →
            ∀ f : (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* T,
              Function.Surjective f →
                f.ker ≤ Subgroup.center (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →
                  ∀ x ∈ L, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ T

theorem memberFreeSocleOuter3_of_solvBalance (hb : L2PrimeBalanceSolv) :
    MemberFreeSocleOuter3 := by
  intro Y _ _ _ hO z L hz T hT _ _ _ _ hCT hfree
  have hLT : L ≤ T := by
    have h := solvableMemberInner_of_L2PrimeBalanceSolv hb Y hO z L hz T hT
    rwa [hCT, sup_bot_eq] at h
  exact hfree ⟨z, hLT hz.mem⟩ (L.subgroupOf T) (hz.subgroupOf hLT)

theorem d4OuterThree3_of_solvBalance (hb : L2PrimeBalanceSolv) : D4OuterThree3 := by
  intro Y _ _ _ hO z L hz T hT _ _ _ _ hCT _ _ _ x hx _
  have h := solvableMemberInner_of_L2PrimeBalanceSolv hb Y hO z L hz T hT
  rw [hCT, sup_bot_eq] at h
  exact h hx

end CFSG.ClassicalInvolution.Q3.Q3T
