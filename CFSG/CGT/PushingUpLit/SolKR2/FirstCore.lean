module

public import CFSG.CGT.PushingUpLit.SolKR2.Defs

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.PartTwo (omegaOneSub)

@[expose] def R2FirstCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M B : Subgroup G), R2 M B →
    ∀ (S : Sylow 2 M) (A D : Subgroup G), A ∈ Lam M B → D ∈ Lam M B →
      A ≤ (S : Subgroup M).map M.subtype → D ≤ (S : Subgroup M).map M.subtype →
      (∀ a ∈ A, a ≠ 1 → ∀ d ∈ D, d ≠ 1 → orderOf (a * d) = 4) →
      ⁅A, D⁆ = omegaOneSub B ∧ A ⊔ D = D ⊔ omegaTwoSub B

end CFSG.CGT.PushingUpLit.SolKR2
