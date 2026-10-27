module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def IsSec8Socle (K₀ : Type) [Group K₀] (p f : ℕ) : Prop :=
  Blueprint.LieModel K₀ .PSp 2 p f ∨ (p = 3 ∧ f = 1 ∧ Nonempty (K₀ ≃* alternatingGroup (Fin 8)))

@[expose] def IsSec8JType (Y : Type) [Group Y] (p f : ℕ) : Prop :=
  Blueprint.LieModel Y .PSL 2 p (2 * f) ∨
    (p = 3 ∧ f = 1 ∧ Nonempty (Y ≃* alternatingGroup (Fin 6)))

@[expose] def CFSec8Simple : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → IsSimpleGroup K₀ ∧ ∃ u v : K₀, u * v ≠ v * u

@[expose] def CFSec8InnerCentralizer : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime →
    p ≠ 2 → 1 ≤ f → IsSec8Socle K₀ p f → IsSec8JType Y p f → ∀ t : K₀, orderOf t = 2 →
      ¬ Nat.card Y ∣ Nat.card (centralizer ({t} : Set K₀))

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X)

theorem Sec8Case.exists_params (hc : h.Sec8Case) :
    conjugate h.K h.a = h.K ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      IsSec8Socle (h.K ⧸ pPrimeCore 2 h.K) p f ∧ IsSec8JType (h.J ⧸ pPrimeCore 2 h.J) p f := by
  rcases hc with ⟨hJ, hKa, hK⟩ | ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩
  · exact ⟨hKa, 3, 1, Nat.prime_three, by norm_num, le_rfl, Or.inr ⟨rfl, rfl, hK⟩,
      Or.inr ⟨rfl, rfl, hJ⟩⟩
  · exact ⟨hKa, p, f, hp, hp2, hf, Or.inl hK, Or.inl hJ⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
