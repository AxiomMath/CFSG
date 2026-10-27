module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup

@[expose] def PInv {X : Type*} [Group X] (S : Subgroup X) : Prop :=
  Nat.card S = 2 ^ 8 ∧ Nat.card {x : S // x ^ 2 = 1 ∧ x ≠ 1} = 87

structure CentHyp {G : Type*} [Group G] (t : G) : Prop where
  card_le : ∀ S : Subgroup G, S ≤ centralizer {t} → IsPGroup 2 S → Nat.card S ≤ 2 ^ 8
  pinv : ∀ S : Subgroup G, S ≤ centralizer {t} → IsPGroup 2 S → Nat.card S = 2 ^ 8 → PInv S

end CFSG.OddStandard.AltStdSmall4.Tower
