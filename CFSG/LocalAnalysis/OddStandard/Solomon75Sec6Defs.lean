module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def IsSec6MType (n : ℕ) (Q : Type) [Group Q] : Prop :=
  (n = 8 ∧ Nonempty (Q ≃* Blueprint.NativeSporadic.McL)) ∨
    (n = 11 ∧ Nonempty (Q ≃* Blueprint.NativeSporadic.Ly))

@[expose] def IsMLIntrIn (X : Type) [Group X] (H M : Subgroup X) : Prop :=
  IsPCompIn 2 H M ∧
    (Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.Ly)) ∧
    ∀ s ∈ M, orderOf s = 2 → ∃ J : Subgroup X, IsAhatIntr X s J ∧
      J ≤ (M ⊓ centralizer ({s} : Set X)) ⊔ oddCoreOf (centralizer ({s} : Set X))

theorem isMLIntr_iff {X : Type} [Group X] {t : X} {M : Subgroup X} :
    IsMLIntr X t M ↔ IsMLIntrIn X (centralizer ({t} : Set X)) M :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

@[expose] def Sec6MComp (X : Type) [Group X] (n : ℕ) (H M : Subgroup X) : Prop :=
  IsMLIntrIn X H M ∧ IsSec6MType n (M ⧸ pPrimeCore 2 M)

@[expose] def Sec6KComp (X : Type) [Group X] (n : ℕ) (H L : Subgroup X) : Prop :=
  Sec5Comp X n H L ∨ Sec6MComp X n H L

@[expose] def Sec6M (X : Type) [Group X] (n : ℕ) (H : Subgroup X) : Subgroup X :=
  sSup {M | Sec6MComp X n H M}

@[expose] def Sec6K (X : Type) [Group X] (n : ℕ) (H : Subgroup X) : Subgroup X :=
  sSup {L | Sec6KComp X n H L}

theorem sec6K_eq (X : Type) [Group X] (n : ℕ) (H : Subgroup X) :
    Sec6K X n H = K0 X n H ⊔ Sec6M X n H := by
  rw [K0_eq_sSup_sec5Comp]
  unfold Sec6K Sec6M Sec6KComp
  rw [Set.setOf_or, sSup_union]

@[expose] noncomputable def modOddCard {X : Type} [Group X] (H : Subgroup X) : ℕ :=
  Nat.card (↥H ⧸ pPrimeCore 2 ↥H)

@[expose] def Sec6Q (X : Type) [Group X] (n : ℕ) (H : Subgroup X) : Subgroup X :=
  H ⊓ QOf (Sec6K X n H)

structure IsSec6Choice (X : Type) [Group X] (n : ℕ) (t : X) : Prop where
  inv : orderOf t = 2
  hasM : ∃ M, Sec6MComp X n (cen t) M
  maxM : ∀ s : X, orderOf s = 2 →
    modOddCard (Sec6M X n (cen s)) ≤ modOddCard (Sec6M X n (cen t))
  maxK : ∀ s : X, orderOf s = 2 → (∃ M, Sec6MComp X n (cen s) M) →
    modOddCard (Sec6M X n (cen s)) = modOddCard (Sec6M X n (cen t)) →
      modOddCard (Sec6K X n (cen s)) ≤ modOddCard (Sec6K X n (cen t))

structure Sec6Setting (X : Type) [Group X] [Finite X] (n : ℕ) (t : X) : Prop where
  cex : SolCEx X
  notA : ¬ HypA X
  maxdeg : IsMaxAhatDeg X n
  deg : n = 8 ∨ n = 11
  choice : IsSec6Choice X n t
  central : K0 X n (cen t) ≠ ⊥ → t ∈ K0 X n (cen t)

@[expose] def Sec6Base (X : Type) [Group X] (n : ℕ) (t : X) : Subgroup X :=
  Sec6M X n (cen t) ⊔ zStar (K0 X n (cen t))

@[expose] def sec6Sig (X : Type) [Group X] (n : ℕ) (t : X) : Subgroup X :=
  ⨆ (b : X) (_ : b ∈ Sec6M X n (cen t)) (_ : orderOf b = 2), oddCoreOf (cen b)

@[expose] def Sec6R (X : Type) [Group X] (n : ℕ) (N : Subgroup X) : Subgroup X :=
  zStar (K0 X n N) ⊔ Sec6M X n N

@[expose] def Sec6Y (X : Type) [Group X] (n : ℕ) (N : Subgroup X) : Subgroup X :=
  Sec6R X n N ⊔ oddCoreOf (Sec6K X n N)

@[expose] def sec6V (X : Type) [Group X] (n : ℕ) (t : X) : Subgroup X :=
  ⨆ (x : X) (_ : x ∈ Sec6M X n (cen t)) (_ : orderOf x = 2), Sec6K X n (cen x)

@[expose] def sec6D {X : Type} [Group X] (Y : Subgroup X) : Set X :=
  {x | ∃ g y : X, y ∈ Y ∧ orderOf y = 2 ∧ x = g * y * g⁻¹}

structure Sec6Fusion (X : Type) [Group X] (N Y : Subgroup X) : Prop where
  ne_top : N ≠ ⊤
  le : Y ≤ N
  conj : ∀ x ∈ sec6D Y, ∀ z ∈ sec6D Y, Commute x z → ∃ g : X, g * x * g⁻¹ ∈ N ∧ g * z * g⁻¹ ∈ N
  fus : ∀ x ∈ sec6D Y, x ∈ N → x ∈ Y
  cen : ∀ y ∈ Y, orderOf y = 2 → centralizer ({y} : Set X) ≤ N
  inv : ∃ y ∈ Y, orderOf y = 2
  ns : ∀ y ∈ Y, orderOf y = 2 → ¬ Group.IsSolvable ↥(centralizer ({y} : Set X))

structure Sec6Lemma51 (X : Type) [Group X] (n : ℕ) : Prop where
  b : ∀ H : Subgroup X, H ≠ ⊤ → ∀ t ∈ H, orderOf t = 2 →
    Sec6K X n (H ⊓ cen t) ≤ Sec6K X n H ∧ Sec6M X n (H ⊓ cen t) ≤ Sec6M X n H
  sub : ∀ s : X, orderOf s = 2 → ∀ H : Subgroup X, H ≤ cen s →
    Sec6K X n H ≤ Sec6K X n (cen s) ∧ Sec6M X n H ≤ Sec6M X n (cen s)

@[expose] def Sec6Entry (X : Type) [Group X] (n : ℕ) : Prop :=
  (n = 8 ∧ ∃ (t : X) (M : Subgroup X), orderOf t = 2 ∧ IsMLIntr X t M ∧
      Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.McL)) ∨
    (n = 11 ∧ ∃ (t : X) (M : Subgroup X), orderOf t = 2 ∧ IsMLIntr X t M ∧
      Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.Ly))

@[expose] def Sec6PumpUp (X : Type) [Group X] (n : ℕ) : Prop :=
  ∀ (s t u : X) (K M : Subgroup X), orderOf s = 2 → orderOf t = 2 → s * t = t * s → s ≠ t →
    IsIntrinsicIn X (cen s) K u → IsDoubleCoverOfAlt (↥K ⧸ pPrimeCore 2 ↥K) n →
    IsPCompIn 2 (cen t) M → t ∈ centralizerSection K (pPrimeCoreOf 2 K) → lTwist K t ≤ M →
      ((∃ u', IsIntrinsicIn X (cen t) M u') ∧ IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n ∧
          LPrec X M K) ∨
        Sec6MComp X n (cen t) M

@[expose] def Sec6Covers (X : Type) [Group X] (n : ℕ) (t x : X) : Prop :=
  Sec6K X n (cen x) = oddCoreOf (Sec6K X n (cen x)) ⊔ (Sec6K X n (cen x) ⊓ Sec6K X n (cen t))

@[expose] def Sec6AtAhat (X : Type) [Group X] (n : ℕ) (t : X) : Prop :=
  IsDoubleCoverOfAlt (↥(K0 X n (cen t)) ⧸ pPrimeCore 2 ↥(K0 X n (cen t))) n

structure Sec6L61 (X : Type) [Group X] (n : ℕ) (t : X) : Prop where
  a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x
  b : ¬ Sec6AtAhat X n t → ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → Sec6Covers X n t x
  c : Sec6AtAhat X n t → ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ¬ Sec6Covers X n t x →
    ∃ M0 : Subgroup X, M0 ≤ Sec6K X n (cen x) ∧
      Sec6K X n (cen x) = M0 ⊔ (Sec6M X n (cen t) ⊓ Sec6K X n (cen x)) ∧
      IsSec6MType n (↥M0 ⧸ pPrimeCore 2 ↥M0) ∧
      Sec6K X n (M0 ⊓ cen t) ≤ oddCoreOf (Sec6K X n (cen t)) ⊔ K0 X n (cen t)

@[expose] def Sec6L65 (X : Type) [Group X] (n : ℕ) (t : X) : Prop :=
  ∀ x ∈ Sec6Base X n t, orderOf x = 2 → oddCoreOf (cen x) = ⊥

end CFSG.OddStandard.Solomon75
