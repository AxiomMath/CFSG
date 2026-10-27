module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def A6ShapeI (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (x : G) : Prop :=
  LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) →
    (P : Subgroup G) ≤ centralizer ({x} : Set G)

@[expose] def A6ShapeVI (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (x : G) : Prop :=
  ¬ LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) →
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) ∧
    IsElemAbelian p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ∧
    Nat.card ↥((P : Subgroup G) ⊓ centralizer ({x} : Set G)) = p ^ 3

@[expose] def A6Prop34S (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (J : Subgroup G)
    (x : G) : Prop :=
  A6Prop34 p P J x ∧ A6ShapeI p P x ∧ A6ShapeVI p P x

@[expose] def GL83GenericPrimeThreeA6ShapeVI (G : Type) [Group G] [Finite G] : Prop :=
  GenericA6At G fun p P _ x J => A6Prop34 p P J x → A6ShapeVI p P x

@[expose] def GL83GenericPrimeThreeA6Lemma43S (G : Type) [Group G] [Finite G] : Prop :=
  GenericA6At G fun p P M x J => A6Prop34S p P J x → A6PointLemma43 p P M J x

end CFSG.LocalAnalysis.RankThreeTheoremC
