module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

@[expose] def L4Cls1 : Prop :=
  ∀ (F : Type) [Field F] [Finite F],
    (Odd (Nat.card F) → ∀ {α : MulAut (projectiveSL 4 F)} {B : GL (Fin 4) F}, B * B = 1 →
      Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2 → α = conjAut 4 F B →
      ∀ W : Submodule F (Fin 4 → F),
        (∀ A : SL(4, F), proj 4 F A ∈ fixSub α → ∀ w ∈ W, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
    (Odd (Nat.card F) → 5 ≤ Nat.card F → ∀ {α : MulAut (projectiveSL 4 F)} {B : GL (Fin 4) F}, B * B = 1 →
      Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2 → α = conjAut 4 F B →
      ∀ x : SL(4, F), (∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) →
        ∀ g, x * ι g = ι g * x) → α (proj 4 F x) = proj 4 F x) ∧
    (Nat.card F = 3 → ∀ {α : MulAut (projectiveSL 4 F)} {B : GL (Fin 4) F}, B * B = 1 →
      Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2 → α = conjAut 4 F B →
      ∀ x : SL(4, F), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1) →
        (∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α → x * ⁅a, b⁆ = ⁅a, b⁆ * x) →
        α (proj 4 F x) = proj 4 F x)

@[expose] def L4Cls2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F],
    (Odd (Nat.card F) → ∀ {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F} {c : Fˣ},
      A * A = GeneralLinearGroup.scalar (Fin 4) c → ¬ IsSquare (c : F) → α = conjAut 4 F A →
      ∀ W : Submodule F (Fin 4 → F),
        (∀ A' : SL(4, F), proj 4 F A' ∈ fixSub α → ∀ w ∈ W, (A' : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
    (Odd (Nat.card F) → 5 ≤ Nat.card F → ∀ {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F} {c : Fˣ},
      A * A = GeneralLinearGroup.scalar (Fin 4) c → ¬ IsSquare (c : F) → α = conjAut 4 F A →
      ∀ x : SL(4, F), (∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) →
        ∀ g, x * ι g = ι g * x) → α (proj 4 F x) = proj 4 F x) ∧
    (Nat.card F = 3 → ∀ {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F} {c : Fˣ},
      A * A = GeneralLinearGroup.scalar (Fin 4) c → ¬ IsSquare (c : F) → α = conjAut 4 F A →
      ∀ x : SL(4, F), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1) →
        (∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α → x * ⁅a, b⁆ = ⁅a, b⁆ * x) →
        α (proj 4 F x) = proj 4 F x)

@[expose] def L4Cls3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F],
    (Odd (Nat.card F) → ∀ {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F},
      (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A → α = conjAut 4 F A * dualAut 4 F →
      ∀ W : Submodule F (Fin 4 → F),
        (∀ A' : SL(4, F), proj 4 F A' ∈ fixSub α → ∀ w ∈ W, (A' : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
    (Odd (Nat.card F) → 5 ≤ Nat.card F → ∀ {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F},
      (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A → α = conjAut 4 F A * dualAut 4 F →
      ∀ x : SL(4, F), (∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) →
        ∀ g, x * ι g = ι g * x) → x ∈ scalars 4 F) ∧
    (Nat.card F = 3 → ∀ {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F},
      (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A → α = conjAut 4 F A * dualAut 4 F →
      ∀ x : SL(4, F), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1) →
        (∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α → x * ⁅a, b⁆ = ⁅a, b⁆ * x) →
        x ∈ scalars 4 F)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
