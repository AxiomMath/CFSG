module

public import CFSG.Certificates.OrbitChain

public section

namespace CFSG.KC.G23F48

open MulAction CFSG.Certificates

variable {α : Type*} [Finite α]

theorem card_parabolics_of_orbits {X P₁ P₂ B S₀ K : Subgroup (Equiv.Perm α)} {p q : α}
    {Op Oq O₁ O₂ : Finset α} (hX : Nat.card X = 4245696)
    (hOp : Op.card = 364) (hOpX : ∀ r ∈ Op, ∃ g ∈ X, g p = r)
    (hOq : Oq.card = 364) (hOqX : ∀ r ∈ Oq, ∃ g ∈ X, g q = r)
    (hO₁ : O₁.card = 4) (hO₁P : ∀ r ∈ O₁, ∃ g ∈ P₁, g q = r)
    (hO₂ : O₂.card = 4) (hO₂P : ∀ r ∈ O₂, ∃ g ∈ P₂, g p = r)
    (hP₁ : P₁ ≤ X ⊓ stabilizer (Equiv.Perm α) p) (hP₂ : P₂ ≤ X ⊓ stabilizer (Equiv.Perm α) q)
    (hB₁ : B ≤ P₁ ⊓ stabilizer (Equiv.Perm α) q) (hB₂ : B ≤ P₂ ⊓ stabilizer (Equiv.Perm α) p)
    (hS : S₀ ≤ B) (hK : K ≤ B) (hS₀ : Nat.card S₀ = 729) (hK₄ : Nat.card K = 4) :
    Nat.card P₁ = 11664 ∧ Nat.card P₂ = 11664 ∧ Nat.card B = 2916 := by
  have hXp := card_mul_card_inf_stabilizer_le X p Op hOpX
  have hXq := card_mul_card_inf_stabilizer_le X q Oq hOqX
  have h₁ := card_mul_card_inf_stabilizer_le P₁ q O₁ hO₁P
  have h₂ := card_mul_card_inf_stabilizer_le P₂ p O₂ hO₂P
  have c₁ := Subgroup.card_le_of_le hP₁
  have c₂ := Subgroup.card_le_of_le hP₂
  have d₁ := Subgroup.card_le_of_le hB₁
  have d₂ := Subgroup.card_le_of_le hB₂
  have hdvd : 2916 ∣ Nat.card B :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (hS₀ ▸ Subgroup.card_dvd_of_le hS)
      (hK₄ ▸ Subgroup.card_dvd_of_le hK)
  have hpos : 0 < Nat.card B := Nat.card_pos
  rw [hOp, hX] at hXp
  rw [hOq, hX] at hXq
  rw [hO₁] at h₁
  rw [hO₂] at h₂
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨by omega, by omega, by omega⟩

end CFSG.KC.G23F48
