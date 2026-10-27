module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.CommutingOrderThreeTriple

open Subgroup

theorem nf_mul {L : Type} [Group L] {a b c : L} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (i j k i' j' k' : ℤ) :
    (a ^ i * b ^ j * c ^ k) * (a ^ i' * b ^ j' * c ^ k') =
      a ^ (i + i') * b ^ (j + j') * c ^ (k + k') := by
  have s1 : c ^ k * a ^ i' = a ^ i' * c ^ k := (hac.symm.zpow_zpow k i').eq
  have s2 : b ^ j * a ^ i' = a ^ i' * b ^ j := (hab.symm.zpow_zpow j i').eq
  have s3 : c ^ k * b ^ j' = b ^ j' * c ^ k := (hbc.symm.zpow_zpow k j').eq
  have t1 : ∀ z : L, c ^ k * (a ^ i' * z) = a ^ i' * (c ^ k * z) := fun z => by
    rw [← mul_assoc, s1, mul_assoc]
  have t2 : ∀ z : L, b ^ j * (a ^ i' * z) = a ^ i' * (b ^ j * z) := fun z => by
    rw [← mul_assoc, s2, mul_assoc]
  have t3 : ∀ z : L, c ^ k * (b ^ j' * z) = b ^ j' * (c ^ k * z) := fun z => by
    rw [← mul_assoc, s3, mul_assoc]
  rw [show (a ^ i * b ^ j * c ^ k) * (a ^ i' * b ^ j' * c ^ k') =
      a ^ i * (b ^ j * (c ^ k * (a ^ i' * (b ^ j' * c ^ k')))) by simp only [mul_assoc]]
  rw [t1, t2, t3, zpow_add, zpow_add, zpow_add]
  simp only [mul_assoc]

def normalForm {L : Type} [Group L] {a b c : L} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) : Subgroup L where
  carrier := {x | ∃ i j k : ℤ, a ^ i * b ^ j * c ^ k = x}
  one_mem' := ⟨0, 0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
    exact ⟨i + i', j + j', k + k', (nf_mul hab hac hbc i j k i' j' k').symm⟩
  inv_mem' := by
    rintro _ ⟨i, j, k, rfl⟩
    have hmul : (a ^ i * b ^ j * c ^ k) * (a ^ (-i) * b ^ (-j) * c ^ (-k)) = 1 := by
      rw [nf_mul hab hac hbc i j k (-i) (-j) (-k)]
      simp
    exact ⟨-i, -j, -k, eq_inv_of_mul_eq_one_right hmul⟩

theorem closure_le_normalForm {L : Type} [Group L] {a b c : L} (hab : Commute a b)
    (hac : Commute a c) (hbc : Commute b c) :
    closure ({a, b, c} : Set L) ≤ normalForm hab hac hbc := by
  refine (closure_le _).2 ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h
  · rw [h]; exact (⟨1, 0, 0, by simp⟩ : ∃ i j k : ℤ, a ^ i * b ^ j * c ^ k = a)
  · rw [h]; exact (⟨0, 1, 0, by simp⟩ : ∃ i j k : ℤ, a ^ i * b ^ j * c ^ k = b)
  · rw [h]; exact (⟨0, 0, 1, by simp⟩ : ∃ i j k : ℤ, a ^ i * b ^ j * c ^ k = c)

theorem exists_normalForm_of_mem {L : Type} [Group L] {a b c : L} (hab : Commute a b)
    (hac : Commute a c) (hbc : Commute b c) {x : L}
    (hx : x ∈ closure ({a, b, c} : Set L)) :
    ∃ i j k : ℤ, a ^ i * b ^ j * c ^ k = x :=
  closure_le_normalForm hab hac hbc hx

theorem pow_three_eq_one_of_normalForm {L : Type} [Group L] {a b c : L} (hab : Commute a b)
    (hac : Commute a c) (hbc : Commute b c) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (i j k : ℤ) : (a ^ i * b ^ j * c ^ k) ^ 3 = 1 := by
  have pw : ∀ (x : L) (m : ℤ), x ^ 3 = 1 → (x ^ m) ^ 3 = 1 := by
    intro x m hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hABC : Commute (a ^ i * b ^ j) (c ^ k) :=
    (hac.zpow_zpow i k).mul_left (hbc.zpow_zpow j k)
  rw [hABC.mul_pow, (hab.zpow_zpow i j).mul_pow, pw a i ha, pw b j hb, pw c k hc, one_mul,
    one_mul]

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.CommutingOrderThreeTriple

end
