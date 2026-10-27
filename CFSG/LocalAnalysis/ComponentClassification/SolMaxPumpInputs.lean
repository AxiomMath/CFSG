module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

@[expose] def SuzOuterComponentsInput : Prop :=
  ∀ (G : Type) [Group G], Nonempty (G ≃* NativeSporadic.Suz) → ∀ α : MulAut G, α * α = 1 →
    α ∉ inner G → ∀ B : Subgroup (fixSub α), IsComponent B →
      Nat.card (B ⧸ center B) = 95040 ∨ Nat.card (B ⧸ center B) = 604800

@[expose] def ONOuterComponentsInput : Prop :=
  ∀ (G : Type) [Group G], Nonempty (G ≃* NativeSporadic.ON) → ∀ α : MulAut G, α * α = 1 →
    α ∉ inner G → ∀ B : Subgroup (fixSub α), IsComponent B →
      Nat.card (B ⧸ center B) = 175560

end CFSG.ComponentClassification.SolMax
