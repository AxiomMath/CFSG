module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsThreeOnePlusTwo.card_centerIn {D : Subgroup G} (hD : IsThreeOnePlusTwo ↥D) :
    Nat.card (CFSG.centerIn D) = 3 := by
  rw [CFSG.centerIn_eq_map_center]
  rw [Subgroup.card_map_of_injective D.subtype_injective]
  exact hD.1.2.2.2

structure TwelveNineA (M H : Subgroup G) (p : ℕ) (Q : Subgroup G) : Prop where
  le_kSub : ∀ D : Subgroup G, IsThreeOnePlusTwo ↥D → D ≤ Q → D ≤ kSub p M H
  normal : ∀ D : Subgroup G, IsThreeOnePlusTwo ↥D → D ≤ Q →
    (D.subgroupOf (kSub p M H ⊓ normalizer (CFSG.centerIn D : Set G))).Normal
  center_not_le : ∀ D : Subgroup G, IsThreeOnePlusTwo ↥D → D ≤ Q →
    ¬ kSub p M H ⊓ normalizer (CFSG.centerIn D : Set G) ≤ M

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
