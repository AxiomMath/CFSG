module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def L34GStarQuotient (Y : Type) [Group Y] : Prop :=
  SimpleFStarQuotient Y ∨ (CFSG.IsQuasisimple Y ∧ IsTwoU43 Y)

@[expose] def L34GFix {Y : Type} [Group Y] (σ : MulAut Y) : Subgroup Y :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id Y)

theorem l34g_mem_fix {Y : Type} [Group Y] (σ : MulAut Y) (y : Y) :
    y ∈ L34GFix σ ↔ σ y = y :=
  Iff.rfl

theorem l34g_fix_eq_fixSub {Y : Type} [Group Y] (σ : MulAut Y) : L34GFix σ = fixSub σ :=
  Subgroup.ext fun _ => Iff.rfl

@[expose] def Asc82CoreF0 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y → IsTwoU43 Y →
    ∀ σ : MulAut Y, σ * σ = 1 → ∃ e : Y, orderOf e = 2 ∧ σ e = e ∧ e ∉ center Y

@[expose] def Asc82CoreKGA : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], L34GStarQuotient Y →
    ∀ (y : Y) (B : Subgroup Y), orderOf y = 2 → Sl23PocketIn ⊤ y B →
    ∀ σ : MulAut Y, σ * σ = 1 → (∀ b ∈ B, σ b = b) → σ ≠ MulAut.conj y →
      ∃ J : Subgroup Y, IsComponentIn J (L34GFix σ) ∧ InFStar J ∧ B ≤ J

@[expose] def Asc82CoreKGB : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], L34GStarQuotient Y →
    ∀ σ : MulAut Y, σ * σ = 1 → ∀ J : Subgroup Y, IsComponentIn J (L34GFix σ) →
      ∀ b ∈ J, IsI4PlusIn J b → IsI4PlusIn ⊤ b

end CFSG.OddStandard.SmallF3.Omega
