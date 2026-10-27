module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Def

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82CoreKGAHardD4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .POmegaPlus 4 3 1 → ¬ L34GC6 Y →
    ∀ (y : Y) (B : Subgroup Y), orderOf y = 2 → Sl23PocketIn ⊤ y B →
    ∀ σ : MulAut Y, σ * σ = 1 → σ ≠ 1 → (∀ b ∈ B, σ b = b) → σ ≠ MulAut.conj y →
      ∃ J : Subgroup Y, IsComponentIn J (L34GFix σ) ∧ InFStar J ∧ B ≤ J

end CFSG.OddStandard.SmallF3.Omega
