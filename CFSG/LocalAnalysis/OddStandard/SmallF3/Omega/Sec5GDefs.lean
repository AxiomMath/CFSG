module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open
open scoped MatrixGroups

variable {X : Type} [Group X]

abbrev Sec5GBar (A : Subgroup X) : Type :=
  ↥(normalClosure (A : Set X)) ⧸ goldschmidtOddCore ↥(normalClosure (A : Set X))

abbrev sec5g_pi (A : Subgroup X) : ↥(normalClosure (A : Set X)) →* Sec5GBar A :=
  QuotientGroup.mk' (goldschmidtOddCore ↥(normalClosure (A : Set X)))

@[expose] def Sec5GImg (A : Subgroup X) : Subgroup (Sec5GBar A) :=
  (A.subgroupOf (normalClosure (A : Set X))).map (sec5g_pi A)

@[expose] def Sec5GCaseI (A : Subgroup X) : Prop :=
  Sec5GImg A = ⊤

@[expose] def Sec5GCaseII (A : Subgroup X) : Prop :=
  (∃ (p f : ℕ) (_ : Fact p.Prime), Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (Sec5GBar A ≃* PSL(2, GaloisField p f))) ∧
    ∃ P : Sylow 2 (Sec5GBar A), (P : Subgroup (Sec5GBar A)) = Sec5GImg A

@[expose] def Sec5GCaseIII (S A : Subgroup X) : Prop :=
  64 ≤ Nat.card ↥(S ⊓ normalClosure (A : Set X)) ∧
    ∀ s ∈ S ⊓ normalClosure (A : Set X), s * s = 1 → s ∈ A

@[expose] def Sec5GOutcome (S A : Subgroup X) : Prop :=
  S ⊓ normalClosure (A : Set X) = A ∧ (Sec5GCaseI A ∨ Sec5GCaseII A)

end CFSG.OddStandard.SmallF3.Omega
