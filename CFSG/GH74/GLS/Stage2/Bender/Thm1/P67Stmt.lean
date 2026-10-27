module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74

@[expose] def CF67 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (J : Subgroup N), IsComponent J →
    GHList (↥J ⧸ Subgroup.center ↥J) →
    ∀ (r : ℕ), r.Prime → Odd r → ∀ (V Z : Subgroup N),
      IsElementaryAbelian r ↥V → Nat.card ↥V = r ^ 2 →
      (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → Odd (Nat.card ↥Z) → Nat.Coprime (Nat.card ↥Z) r →
      (∀ v ∈ V, ∀ w ∈ Z, v * w = w * v) →
      V ≤ normalizer (J : Set N) → Z ≤ normalizer (J : Set N) →
      (∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N)) →
      ¬ J ≤ centralizer (Z : Set N) →
      (∀ v ∈ V, v ≠ 1 → ∀ c ∈ J, c ∈ centralizer ({v} : Set N) → c ∈ normalizer (Z : Set N)) →
      False

end CFSG.GH74.GLS.Stage2.Bender.Thm1
