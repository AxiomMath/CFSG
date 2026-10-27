module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CF81E6Cls : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → ∀ c : Cat8.QConf K₀ (p ^ f), ∀ w ∈ Cat8.innA K₀ c.a, w * w = 1 →
      w ≠ 1 → ∃ n ∈ Cat8.innA K₀ c.a, n⁻¹ * w * n = c.a ∨ n⁻¹ * w * n = c.z ∨
        n⁻¹ * w * n = c.a * c.z * c.tau ∨ n⁻¹ * w * n = c.z * c.tau

@[expose] def CF81E6Out : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → ∀ α : MulAut K₀, Cat8.IsAdmQ K₀ (p ^ f) α →
      (Cat8.innA K₀ α).Normal ∧
        ∃ φ : MulAut K₀, ∀ ψ : MulAut K₀, ∃ k : ℤ, (φ ^ k)⁻¹ * ψ ∈ Cat8.innA K₀ α

@[expose] def CF81E6Fld : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → ∀ α : MulAut K₀, Cat8.IsAdmQ K₀ (p ^ f) α →
      ∀ S₀ : Subgroup (MulAut K₀), (∃ R : Sylow 2 ↥(Cat8.innA K₀ α),
        (R : Subgroup _) = S₀.subgroupOf (Cat8.innA K₀ α)) → S₀ ≤ Cat8.innA K₀ α →
      ∀ ψ ∈ normalizer (S₀ : Set (MulAut K₀)), ψ ∉ Cat8.innA K₀ α → ψ * ψ ∈ S₀ →
        ∃ σ ∈ S₀, σ * ψ * (σ * ψ) = 1 ∧ ∃ E : Subgroup (MulAut K₀), E ≤ S₀ ∧
          E ≤ centralizer ({σ * ψ} : Set (MulAut K₀)) ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16

@[expose] def CF81E6Sect : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → ∀ c : Cat8.QConf K₀ (p ^ f), ∀ R : Subgroup (MulAut K₀),
      R ≤ Cat8.innA K₀ c.a → IsPGroup 2 R →
        (∃ s : Finset (MulAut K₀), s.card ≤ 4 ∧ closure (s : Set (MulAut K₀)) = R) ∧
          Nat.card R ≤ 2 * Nat.card c.D ^ 2

end CFSG.ComponentClassification.GSThmB
