module

public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

@[expose] def LemmaIV32 : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Exceptional r → ∀ R : Subgroup G,
    IsSylowOf r R σ.ON → σ.D ≤ Subgroup.normalizer (R : Set G) →
      Subgroup.normalizer (R : Set G) ∈ σ.familyL r ∧
        PConstrainedWithin r (Subgroup.normalizer (R : Set G))
          (CFSG.solvableRadical (Subgroup.normalizer (R : Set G)))

@[expose] def LemmaIV33 : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ H ∈ σ.familyL r, ∀ R Rs : Subgroup G,
    IsSylowOf r R σ.ON → σ.D ≤ Subgroup.normalizer (R : Set G) → R ≤ oddCoreIn H →
    IsSylowOf r Rs (oddCoreIn H) → σ.D ≤ Subgroup.normalizer (Rs : Set G) → R < Rs →
      PConstrainedWithin r H (CFSG.oddCore H)

@[expose] def PropIV61 : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Exceptional r → ∀ H ∈ σ.familyL r,
    PConstrainedWithin r H (CFSG.solvableRadical H)

@[expose] def PropIV62 : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ H ∈ σ.familyL r, ∀ R₁ : Subgroup G, R₁ ≠ ⊥ →
    IsPGroup r R₁ → R₁ ≤ oddCoreIn H → σ.D ≤ Subgroup.normalizer (R₁ : Set G) →
    (H : Set G) ⊆
      ((H ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) * (oddCoreIn H : Set G) →
    (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn H) ∧ X ≤ Subgroup.normalizer (R₁ : Set G)) →
      Subgroup.normalizer (R₁ : Set G) ∈ σ.familyL r

@[expose] def CorIV61 : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Exceptional r → ∀ H ∈ σ.familyL r,
    ∀ Rs : Subgroup G, IsSylowOf r Rs H →
    σ.D ≤ Subgroup.normalizer ((Rs ⊓ oddCoreIn H : Subgroup G) : Set G) →
    H ≤ Subgroup.normalizer ((pPrimeCoreIn r H ⊔ CFSG.thompsonCenter Rs : Subgroup G) : Set G) →
      Subgroup.normalizer (CFSG.thompsonCenter Rs : Set G) ∈ σ.familyL r

@[expose] def PropIV71 : Prop :=
  ∀ r : ℕ, σ.HypIV7 r → ∀ P R : Subgroup G, IsSylowOf r P σ.C →
    σ.D ≤ Subgroup.normalizer (P : Set G) → IsSylowOf r R σ.ON →
    σ.D ≤ Subgroup.normalizer (R : Set G) → P ≤ Subgroup.normalizer (R : Set G) →
      ∃ d : σ.IV7Data r, d.P = P ∧ d.R = R

@[expose] def LemmaIV81 : Prop :=
  ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, Subgroup.normalizer (d.Q : Set G) ∈ d.familyM

@[expose] def LemmaIV83 : Prop :=
  ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ H ∈ d.familyM,
    IsDGroupWrt (σ.T.subgroupOf H) ∧ Odd (Nat.card (pPrimeCoreIn r H)) ∧
      d.Cstar ⊓ pPrimeCoreIn r H ≤ σ.ON

@[expose] def CorIV81 : Prop :=
  ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ H ∈ d.familyM, ∀ P₁ : Subgroup G,
    IsSylowOf r P₁ H →
    H ≤ Subgroup.normalizer ((pPrimeCoreIn r H ⊔ CFSG.thompsonCenter P₁ : Subgroup G) : Set G) →
      ∃ P₂ : Subgroup G, IsSylowOf r P₂ H ∧
        Subgroup.normalizer (CFSG.thompsonCenter P₂ : Set G) ∈ d.familyM

@[expose] def PropIV91 : Prop :=
  ∀ r : ℕ, σ.HypIV7 r → ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K)

end Setting

end CFSG.ABGTheoremB
