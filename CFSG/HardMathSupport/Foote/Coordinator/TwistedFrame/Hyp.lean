module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Coordinates
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable (τ : Tag) (K : Type) [Field K]

@[expose] def HeisSpace : Submodule K ((Fin τ.rank → ℤ) → K) where
  carrier := {f | ∀ β, β ∉ Deg1 τ → f β = 0}
  add_mem' := fun {a b} ha hb β hβ => by simp [ha β hβ, hb β hβ]
  zero_mem' := fun β _ => rfl
  smul_mem' := fun c {x} hx β hβ => by simp [hx β hβ]

variable {τ K}

@[expose] def Rθ (X : Subgroup (ModGL τ K)) : Subgroup (ModGL τ K) := X ⊓ Qθ τ K

@[expose] def CQθ (X : Subgroup (ModGL τ K)) : Subgroup (ModGL τ K) :=
  Qθ τ K ⊓ Subgroup.centralizer (Rθ X : Set (ModGL τ K))

@[expose] def VS (X : Subgroup (ModGL τ K)) : Submodule K ((Fin τ.rank → ℤ) → K) :=
  Submodule.span K (heisCoord τ K '' (Rθ X : Set (ModGL τ K)))

@[expose] def VM (X : Subgroup (ModGL τ K)) : Submodule K ((Fin τ.rank → ℤ) → K) :=
  Submodule.span K (heisCoord τ K '' (CQθ X : Set (ModGL τ K)))

structure TwBasic (X₁ X₂ : Subgroup (ModGL τ K)) : Prop where
  le₁ : X₁ ≤ adjointGroup τ K
  le₂ : X₂ ≤ adjointGroup τ K
  comm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x
  Uθ_le : Uθ τ K ≤ X₁
  Uneg_le : Heis.Uneg τ K ≤ X₁
  gen : (⨆ x ∈ X₁, conjSub x (Uθ τ K)) = X₁

@[expose] def TwQuasi (X₁ X₂ : Subgroup (ModGL τ K)) : Prop :=
  CFSG.IsQuasisimple ↥X₁ ∧ CFSG.IsQuasisimple ↥X₂

structure TwCentral (X₁ X₂ : Subgroup (ModGL τ K)) : Prop where
  centralizer_le : ∃ T : Subgroup (ModGL τ K), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
    T ≤ Subgroup.normalizer (X₂ : Set (ModGL τ K)) ∧
    ∀ g ∈ adjointGroup τ K, (∀ x ∈ X₁, g * x = x * g) → g ∈ T ⊔ X₂
  unipotent_le : ∀ g ∈ adjointGroup τ K, (∀ x ∈ X₁, g * x = x * g) → g ^ ringChar K = 1 →
    g ∈ X₁ ⊔ X₂

structure TwCoords (X₁ X₂ : Subgroup (ModGL τ K)) : Prop where
  inj : ∀ q ∈ Qθ τ K, heisCoord τ K q ∈ VS (X₁ ⊔ X₂) → q ∈ X₁ ⊔ X₂
  inf_eq_bot : VS (X₁ ⊔ X₂) ⊓ VM (X₁ ⊔ X₂) = ⊥
  sup_eq_top : VS (X₁ ⊔ X₂) ⊔ VM (X₁ ⊔ X₂) = HeisSpace τ K

@[expose] def TwPure (X₁ X₂ : Subgroup (ModGL τ K)) : Prop :=
  ∀ g ∈ adjointGroup τ K, conjSub g (Uθ τ K) ≤ (X₁ ⊔ X₂) ⊓ Qθ τ K →
    ∃ x ∈ X₁, conjSub g (Uθ τ K) = conjSub x (Uθ τ K)

@[expose] def TwIrred (X₁ X₂ : Subgroup (ModGL τ K)) : Prop :=
  ∀ W : Submodule K ((Fin τ.rank → ℤ) → K), W ≤ VM (X₁ ⊔ X₂) →
    (∀ l ∈ (X₁ ⊔ X₂) ⊓ Lθ τ K, ∀ q ∈ Qθ τ K, heisCoord τ K q ∈ W →
      heisCoord τ K (l * q * l⁻¹) ∈ W) → W = ⊥ ∨ W = VM (X₁ ⊔ X₂)

structure TwFrameCore (X₁ X₂ : Subgroup (ModGL τ K)) : Prop where
  basic : TwBasic X₁ X₂
  quasi : TwQuasi X₁ X₂
  central : TwCentral X₁ X₂
  coords : TwCoords X₁ X₂
  pure : TwPure X₁ X₂
  three_le : 3 ≤ Nat.card K

structure TwFrameHyp (X₁ X₂ : Subgroup (ModGL τ K)) : Prop extends TwFrameCore X₁ X₂ where
  irred : TwIrred X₁ X₂

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
