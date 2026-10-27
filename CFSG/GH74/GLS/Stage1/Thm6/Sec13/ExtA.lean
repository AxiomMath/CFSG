module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

@[expose] def IG_9_16 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) [N.Normal] (x : X),
    Nat.card (centralizer ({(x : X ⧸ N)} : Set (X ⧸ N))) ≤ Nat.card (centralizer ({x} : Set X))

@[expose] def IV2_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (t f : G),
    IsPGroup 2 ↥H → t ∈ H → t ≠ 1 → t * t = 1 →
    IsElemAb2 (H ⊓ centralizer ({t} : Set G)) → Nat.card ↥(H ⊓ centralizer ({t} : Set G)) = 8 →
    Is3Element f → f ∈ normalizer (H : Set G) → f * t = t * f → (∃ h ∈ H, f * h ≠ h * f) →
      Hzero H f ⊓ zpowers t = ⊥ ∧ Hzero H f ⊔ zpowers t = H ∧
        (∀ h ∈ H, ∀ q ∈ Hzero H f, h * q * h⁻¹ ∈ Hzero H f) ∧ IsYGroup ↥(Hzero H f)

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
