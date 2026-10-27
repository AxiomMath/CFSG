module

public import CFSG.CGT.Timmesfeld75.Config
public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

@[expose] def BenderCenterInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (T : Subgroup K), StrongWC T → T ≠ ⊥ →
    (¬ ∀ g : K, conjSubgroup g T = T) → Subgroup.normalClosure (T : Set K) = ⊤ →
    ((∃ f : ℕ, 2 ≤ f ∧
        Nonempty (K ⧸ Subgroup.center K ≃* CFSG.Theory.Comparator.PSL2Model f)) ∨
      (∃ a : ℕ, 1 ≤ a ∧ Nonempty (K ⧸ Subgroup.center K ≃* CFSG.Theory.Comparator.SzModel a))) →
    Subgroup.center K = ⊥

@[expose] def UnitaryTwoGenerationInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (T : Subgroup K), StrongWC T → T ≠ ⊥ →
    (¬ ∀ g : K, conjSubgroup g T = T) →
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (K ⧸ Subgroup.center K ≃* CFSG.Theory.Comparator.PSU3Model f)) →
    ∀ g : K, T ⊔ conjSubgroup g T ≠ ⊤

@[expose] def Core214 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), Cfg T T₁ → T ⊔ T₁ = ⊤ →
    (∃ x : G, T₁ = conjSubgroup x T) →
      cfgM T T₁ = pCore 2 G ∧
      ∃ _ : (cfgM T T₁).Normal,
        (∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ⧸ cfgM T T₁ ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (G ⧸ cfgM T T₁ ≃* Sz a)) ∨
        (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (G ⧸ cfgM T T₁ ≃* DihedralGroup n))

end CFSG.CGT.Timmesfeld75
