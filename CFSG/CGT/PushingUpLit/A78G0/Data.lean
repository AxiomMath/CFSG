module

public import CFSG.CGT.PushingUpLit.A78S4.Pair
public import CFSG.Timmesfeld.ARS.Defs

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.ABGLocalTools
open scoped commutatorElement

structure G0Core (G : Type) [Group G] [Finite G] (L₁ L₂ V W Z Z₂ : Subgroup G) (e : ℕ) :
    Prop where
  simple : IsSimpleGroup G
  charTwo : CFSG.Assembly.IsCharTwoType G
  sylow : IsSylowOf 2 (V ⊔ W) ⊤
  hZ : Z ≠ ⊥
  pair : S4Pair G L₁ L₂ V W Z Z₂ (V ⊔ W) e
  side₁ : Sp4Side G L₁ V Z (V ⊔ W) (V ⊔ W) (Subgroup.normalizer (V : Set G)) e
  side₂ : Sp4Side G L₂ W Z₂ (W ⊔ V) (W ⊔ V) (Subgroup.normalizer (W : Set G)) e

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}

theorem symm (h : G0Core G L₁ L₂ V W Z Z₂ e) : G0Core G L₂ L₁ W V Z₂ Z e := by
  have hZ₂ : Z₂ ≠ ⊥ := h.pair.Z₂_ne_bot h.hZ
  have hp := h.pair.symm
  rw [sup_comm V W] at hp
  exact ⟨h.simple, h.charTwo, by rw [sup_comm]; exact h.sylow, hZ₂, hp, h.side₂, h.side₁⟩

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
