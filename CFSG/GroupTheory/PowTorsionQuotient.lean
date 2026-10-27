module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GroupTheory

theorem card_quotient_le_card_pow_torsion {A : Type*} [CommGroup A] [Finite A] {r : ℕ}
    (B : Subgroup A) (hB : ∀ a : A, a ^ r ∈ B) :
    Nat.card (A ⧸ B) ≤ Nat.card (MonoidHom.ker (powMonoidHom r : A →* A)) := by
  classical
  let p : A →* A := powMonoidHom r
  have hrange : p.range ≤ B := by
    rintro _ ⟨a, rfl⟩
    exact hB a
  have hsurj : Function.Surjective
      (QuotientGroup.map (N := p.range) B (MonoidHom.id A) (by simpa using hrange)) := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk a, by simp⟩
  have hcard : Nat.card (A ⧸ B) ≤ Nat.card (A ⧸ p.range) :=
    Nat.card_le_card_of_surjective _ hsurj
  have hq : Nat.card (A ⧸ p.range) = Nat.card p.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (p.range)
    have h2 := Subgroup.card_ker_mul_card_range p
    have h3 : Nat.card (A ⧸ p.range) * Nat.card p.range =
        Nat.card p.ker * Nat.card p.range := by rw [← h1, h2]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := p.range)) h3
  calc Nat.card (A ⧸ B) ≤ Nat.card (A ⧸ p.range) := hcard
    _ = Nat.card p.ker := hq

end CFSG.GroupTheory
