module

public import CFSG.CGT.PushingUpLit.SolKR2.Defs
public import CFSG.RankThree.GF2n.Tim78S31Steps

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.PartTwo (omegaOneSub)

@[expose] def R2Star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M B : Subgroup G), R2 M B →
    ∀ g : G, conjSubgroup g (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G) →
      ∀ A ∈ Lam M B, ∀ a ∈ A, ∀ d ∈ conjSubgroup g (omegaOneSub B), a * d = d * a

structure R2StarData {G : Type} [Group G] {M B : Subgroup G} (h : R2 M B) (g m α x : G) :
    Prop where
  centr : conjSubgroup g (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G)
  lam : conjSubgroup m (omegaOneSub B) ≤ M
  data31 : Data31 (conjSubgroup g (omegaTwoSub B)) (m * g⁻¹) α x
  cent_X : conjSubgroup g (omegaTwoSub B) ⊔ conjSubgroup α (conjSubgroup g (omegaTwoSub B)) ≤
    Subgroup.centralizer (omegaTwoSub B : Set G)
  cent_C : conjSubgroup x (conjSubgroup g (omegaTwoSub B)) ≤
    Subgroup.centralizer (omegaTwoSub B : Set G)
  inf_cent : ∀ a ∈ conjSubgroup m (omegaOneSub B),
    a ∈ Subgroup.centralizer (omegaTwoSub B : Set G) → a = 1
  gamma_comm : ∀ f e e' : G,
    conjSubgroup e (omegaOneSub B) ≤ Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G) →
    conjSubgroup e' (omegaOneSub B) ≤
      Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G) →
    ∀ a ∈ conjSubgroup e (omegaOneSub B), ∀ b ∈ conjSubgroup e' (omegaOneSub B), a * b = b * a
  comm_of_cent : ∀ f c : G,
    conjSubgroup f (omegaOneSub B) ≤ Subgroup.centralizer (conjSubgroup c (omegaTwoSub B) : Set G) →
    ∀ a ∈ conjSubgroup c (omegaTwoSub B), ∀ b ∈ conjSubgroup f (omegaTwoSub B), a * b = b * a

@[expose] def R2StarLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M B : Subgroup G) (h : R2 M B) (g m α x : G),
    R2StarData h g m α x → False

end CFSG.CGT.PushingUpLit.SolKR2
