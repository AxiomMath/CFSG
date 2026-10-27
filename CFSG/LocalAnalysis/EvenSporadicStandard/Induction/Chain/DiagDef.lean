module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

@[expose] def DiagData (H : Type) [Group H] : Prop :=
  ∀ (R T₀ K' A N₀ : Subgroup H) (t : H),
    CFSG.IsQuasisimple ↥K' → T₀ ≤ centralizer (R : Set H) → K' ≤ centralizer (T₀ : Set H) →
    IsCompIn A (centralizer (R : Set H)) → K' ≤ conjClosure A T₀ →
    (∃ π : ↥A →* ↥K', Function.Surjective π) →
    N₀ ≤ normalizer (R : Set H) → N₀ ≤ centralizer (K' : Set H) →
    t ∈ centralizer (R : Set H) → t ∈ centralizer (N₀ : Set H) → t * t = 1 →
    ∃ D : Subgroup H, Group.IsPerfect ↥D ∧ D ≤ centralizer (N₀ : Set H) ∧
      Nonempty ((↥D ⧸ center ↥D) ≃* (↥K' ⧸ center ↥K')) ∧
      (D.map (MulAut.conj t).toMonoidHom = D ∨
        ∀ a ∈ D, ∀ b ∈ D.map (MulAut.conj t).toMonoidHom, a * b = b * a)

end CFSG.EvenSporadicStandard.Induction
