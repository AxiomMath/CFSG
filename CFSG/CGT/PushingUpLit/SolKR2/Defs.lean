module

public import CFSG.RankThree.GF2n.Tim78S3Setting

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.PartTwo (omegaOneSub)

variable {G : Type} [Group G]

structure R2 (M B : Subgroup G) : Prop where
  H : HypH M B
  card4 : Nat.card ↥(omegaOneSub B) = 4
  c4c4 : Nonempty (↥(omegaTwoSub B) ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
  ne : ¬ CFSG.Open.IsElemAbelian 2 B

@[expose] def Lam (M B : Subgroup G) : Set (Subgroup G) :=
  {A | ∃ g : G, A = conjSubgroup g (omegaOneSub B) ∧ A ≤ M}

@[expose] def R2Weak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M B : Subgroup G), R2 M B →
    ∀ g : G, conjSubgroup g (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G) →
      conjSubgroup g (omegaTwoSub B) = omegaTwoSub B

@[expose] def R2First : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M B : Subgroup G), R2 M B →
    ∀ (S : Sylow 2 M) (A D : Subgroup G), A ∈ Lam M B → D ∈ Lam M B →
      A ≤ (S : Subgroup M).map M.subtype → D ≤ (S : Subgroup M).map M.subtype →
      (¬ ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) →
      ⁅A, D⁆ = omegaOneSub B ∧ A ⊔ D = D ⊔ omegaTwoSub B

end CFSG.CGT.PushingUpLit.SolKR2
