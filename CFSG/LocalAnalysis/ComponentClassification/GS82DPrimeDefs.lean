module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup

@[expose] def IsDatum {X : Type} [Group X] (q₀ : ℕ) (v : X) (K N : Subgroup X) (c : X) : Prop :=
  orderOf v = 2 ∧ K ≤ centralizer ({v} : Set X) ∧
    IsPComponent 2 (K.subgroupOf (centralizer ({v} : Set X))) ∧
    N ≤ K ∧ ⁅N, N⁆ = N ∧ HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N) ∧
    orderOf c = 2 ∧ c ∈ N ∧ N ≤ centralizer ({c} : Set X) ∧
    c ∈ (Open.fusionZStar ↥K).map K.subtype

@[expose] def VerticalCentral (Typ : ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) → Typ ↥T →
    ∀ w : H, orderOf w = 2 → w ∈ T → w ∈ (Open.fusionZStar ↥M).map M.subtype → Typ ↥M

@[expose] def CoreInvariant (Typ : ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (A B : Type) [Group A] [Group B],
    Nonempty (A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) → Typ A → Typ B

@[expose] def DiagonalTransfer (q₀ : ℕ) (Typ : ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (A B : Type) [Group A] [Group B] [Finite A] [Finite B],
    HarrisLit.IsTwoQuasisimple A → HarrisLit.IsTwoQuasisimple B → Typ A →
    Nonempty (A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) →
    ∀ N : Subgroup B, ⁅N, N⁆ = N → HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N) →
    ∀ c : B, orderOf c = 2 → c ∈ N → N ≤ centralizer ({c} : Set B) →
      c ∈ Open.fusionZStar B → Typ B

@[expose] def TheoremDPrime : Prop :=
  ∀ (Typ : ∀ (K : Type) [Group K], Prop) (q₀ : ℕ), Odd q₀ → 5 ≤ q₀ →
    VerticalCentral Typ → CoreInvariant Typ → DiagonalTransfer q₀ Typ →
    ∀ (X : Type) [Group X] [Finite X],
    (∀ v : X, orderOf v = 2 → SectionRank.IsKGroupCat ↥(centralizer ({v} : Set X))) →
    ∀ (t : X) (K₀ N : Subgroup X) (c : X), IsDatum q₀ t K₀ N c → Typ ↥K₀ →
      ∃ (w : X) (J N' : Subgroup X), IsDatum q₀ w J N' w ∧ w ∈ J ∧ Typ ↥J

@[expose] def VerticalCentralEsc (Typ Esc : ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) → Typ ↥T →
    ∀ w : H, orderOf w = 2 → w ∈ T → w ∈ (Open.fusionZStar ↥M).map M.subtype →
      Typ ↥M ∨ Esc ↥M

end CFSG.ComponentClassification.GS82PumpInputs
