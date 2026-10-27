module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def SmallOrd {S : Type} [Group S] (I : Subgroup S) : Prop :=
  Nat.card (↥I ⧸ Subgroup.center ↥I) = 25920 ∨ Nat.card (↥I ⧸ Subgroup.center ↥I) = 360

@[expose] def TrivMult (H : Type) [Group H] : Prop :=
  ∀ (M : Type) [Group M] [Finite M], IsQuasisimple M → Nonempty (M ⧸ Subgroup.center M ≃* H) →
    Subgroup.center M = ⊥

@[expose] def ExclQuot (S : Type) [Group S] : Prop :=
  ∀ α : MulAut S, α ^ 3 = 1 → α ≠ 1 → ∀ I : Subgroup S, IsComponentOf I (fixSubgroup α) →
    SmallOrd I → Subgroup.center ↥I = ⊥ ∧
      ∃ H : Subgroup S, I ≤ H ∧ IsSimpleGroup ↥H ∧ TrivMult ↥H

@[expose] def NoSmall (S : Type) [Group S] : Prop :=
  ∀ α : MulAut S, α ^ 3 = 1 → α ≠ 1 → ∀ I : Subgroup S, IsComponentOf I (fixSubgroup α) →
    ¬ SmallOrd I

@[expose] def ExclF4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → NoSmall ↥(adjointGroup Tag.F4 K)

@[expose] def ExclU6 : Prop :=
  ExclQuot LevelLieU6.S6

@[expose] def SU5Mult : Prop :=
  TrivMult ↥(StatedSU 5 (2 ^ 1) CFSG.Fischer.F4)

section TwE6


@[expose] def ExclTE6 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 4 → (∀ c, σ c = c ^ 2) →
    NoSmall ↥(twistedE6RootGroup K σ)

end TwE6

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
