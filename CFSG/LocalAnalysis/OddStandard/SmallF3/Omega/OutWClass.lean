module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainDiag

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem aor_not_walterArrow_of_inCStar [Finite G] {X : Subgroup G} (hX : InCStar X)
    (W : Subgroup G) : ¬ WalterArrow X W := by
  intro h
  obtain ⟨e⟩ := hX.2 W (Relation.ReflTransGen.single (Or.inl h))
  exact (ctrQ_dvd_of_walterArrow h).2 (Nat.card_congr e.toEquiv)

theorem aor_inCStar_of_walterArrowDiag {X W : Subgroup G} (hX : InCStar X)
    (h : WalterArrowDiag X W) : InCStar W := by
  obtain ⟨x, y, -, hy, -, -, hWy, -, -⟩ := id h
  refine ⟨⟨y, hy, hWy⟩, fun V hV => ?_⟩
  obtain ⟨e₁⟩ := hX.2 W (Relation.ReflTransGen.single (Or.inr h))
  obtain ⟨e₂⟩ := hX.2 V (Relation.ReflTransGen.head (Or.inr h) hV)
  exact ⟨e₁.symm.trans e₂⟩

end CFSG.OddStandard.SmallF3.Omega
