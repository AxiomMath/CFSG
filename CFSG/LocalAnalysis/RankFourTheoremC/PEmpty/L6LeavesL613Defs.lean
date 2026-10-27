module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def L613 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z →
    ¬ CFSG.ABGLocalTools.IsPConstrained p ↥M →
    ∀ (H K : Subgroup G), H ≤ M ⊓ centralizer ({x} : Set G) → S622IsSimpleSection H K →
      p ∣ K.relIndex H → ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → f ∣ K.relIndex H →
        CFSG.Open.GLBStronglyEmbedded f M

@[expose] def KFact613rankP : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → f.Prime → 5 ≤ f → f < p →
    CFSG.Open.IsKGroup X →
    (∀ C : CFSG.LocalCores.ComponentIndex (X ⧸ CFSG.pPrimeCore p X),
      IsSimpleGroup ↥C.1 ∧ f ∣ Nat.card C.1) →
    p ≤ Nat.card (CFSG.LocalCores.ComponentIndex (X ⧸ CFSG.pPrimeCore p X)) →
    (∀ C D : CFSG.LocalCores.ComponentIndex (X ⧸ CFSG.pPrimeCore p X), ∃ g : X,
      C.1.map (MulAut.conj (QuotientGroup.mk' (CFSG.pPrimeCore p X) g)).toMonoidHom = D.1) →
    ∀ P : Sylow p X, (¬ ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a) →
      (∀ w ∈ (P : Subgroup X), (∀ b ∈ (P : Subgroup X), w * b = b * w) → w ^ p = 1 →
        w ∈ CFSG.pLayer X p) →
      ∀ y : X, orderOf y = f → 3 ≤ CFSG.Open.pRank f (centralizer ({y} : Set X))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
