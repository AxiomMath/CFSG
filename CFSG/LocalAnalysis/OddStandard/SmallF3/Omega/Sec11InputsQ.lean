module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactAutQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 K2 : Subgroup G),
    ⁅K1, K2⁆ = ⊥ → Nat.card ↥(K1 ⊔ K2) = 288 →
    Nonempty (↥K1 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
    Nonempty (↥K2 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
    ∀ P : Subgroup G, P ≤ twoCoreIn (K1 ⊔ K2) → IsElemAb2 P 3 →
      ∀ Φ : Subgroup (MulAut ↥(twoCoreIn (K1 ⊔ K2))),
        (∀ γ ∈ Φ, ∀ p : ↥(twoCoreIn (K1 ⊔ K2)), (p : G) ∈ P → γ p = p) → Nat.card ↥Φ ≤ 8

end CFSG.OddStandard.SmallF3.Omega
