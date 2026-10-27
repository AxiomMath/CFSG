module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactRankK5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 K2 : Subgroup G),
    ⁅K1, K2⁆ = ⊥ → Nat.card ↥(K1 ⊔ K2) = 288 →
    Nonempty (↥K1 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
    Nonempty (↥K2 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
    ∀ E : Subgroup (MulAut ↥(K1 ⊔ K2)), CFSG.Open.IsElemAbelian 2 E → Nat.card ↥E ≤ 16

@[expose] def Asc82FactQ2m : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ (z : G) (K1 K2 : Subgroup G), IsI4PlusIn L z → Sl23PocketIn L z K1 → Sl23PocketIn L z K2 →
      K1 ≠ K2 → ∀ q ∈ twoCoreIn (K1 ⊔ K2), q * q = 1 → q ∉ zpowers z →
        InducesTypeSome L q 5 1 2 (-1)

structure Asc82FactsB : Prop where
  rank : Asc82FactRankK5
  q2m : Asc82FactQ2m

end CFSG.OddStandard.SmallF3.Omega
