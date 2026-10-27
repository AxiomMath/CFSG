module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage4.Q9

variable {G : Type*} [Group G]

theorem exists_subgroup_mul_of_normalizing (O Q : Subgroup G)
    (hQO : ∀ q ∈ Q, ∀ o ∈ O, q * o * q⁻¹ ∈ O) :
    ∃ H : Subgroup G, ∀ x, x ∈ H ↔ ∃ q ∈ Q, ∃ o ∈ O, x = q * o := by
  refine ⟨{ carrier := {x | ∃ q ∈ Q, ∃ o ∈ O, x = q * o}
            mul_mem' := ?_
            one_mem' := ⟨1, Q.one_mem, 1, O.one_mem, by simp⟩
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro _ _ ⟨q₁, hq₁, o₁, ho₁, rfl⟩ ⟨q₂, hq₂, o₂, ho₂, rfl⟩
    refine ⟨q₁ * q₂, Q.mul_mem hq₁ hq₂, (q₂⁻¹ * o₁ * q₂) * o₂, O.mul_mem ?_ ho₂, by group⟩
    simpa using hQO q₂⁻¹ (Q.inv_mem hq₂) o₁ ho₁
  · rintro _ ⟨q, hq, o, ho, rfl⟩
    exact ⟨q⁻¹, Q.inv_mem hq, q * o⁻¹ * q⁻¹, hQO q hq o⁻¹ (O.inv_mem ho), by group⟩

theorem card_mul_card_dvd_of_normalizing (O Q : Subgroup G)
    (hQO : ∀ q ∈ Q, ∀ o ∈ O, q * o * q⁻¹ ∈ O) (hdisj : ∀ x ∈ Q, x ∈ O → x = 1) :
    Nat.card O * Nat.card Q ∣ Nat.card G := by
  obtain ⟨H, hH⟩ := exists_subgroup_mul_of_normalizing O Q hQO
  let f : O × Q → H := fun oq => ⟨oq.2 * oq.1, (hH _).2 ⟨oq.2, oq.2.2, oq.1, oq.1.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨o, ho⟩, ⟨q, hq⟩⟩ ⟨⟨o', ho'⟩, ⟨q', hq'⟩⟩ h
      have h' : q * o = q' * o' := congrArg Subtype.val h
      have hmem : q'⁻¹ * q ∈ O := by
        have : q'⁻¹ * q = o' * o⁻¹ := by
          calc q'⁻¹ * q = q'⁻¹ * (q * o) * o⁻¹ := by group
            _ = q'⁻¹ * (q' * o') * o⁻¹ := by rw [h']
            _ = o' * o⁻¹ := by group
        rw [this]
        exact O.mul_mem ho' (O.inv_mem ho)
      have hqq : q = q' := (inv_mul_eq_one.mp (hdisj _ (Q.mul_mem (Q.inv_mem hq') hq) hmem)).symm
      subst hqq
      have hoo : o = o' := mul_left_cancel h'
      subst hoo
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨q, hq, o, ho, rfl⟩ := (hH x).1 hx
      exact ⟨(⟨o, ho⟩, ⟨q, hq⟩), rfl⟩
  have hcard : Nat.card O * Nat.card Q = Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (Equiv.ofBijective f hf)
  rw [hcard]
  exact Subgroup.card_subgroup_dvd_card H

theorem factorization_add_le_of_normalizing [Finite G] (p : ℕ) (O Q : Subgroup G)
    (hQO : ∀ q ∈ Q, ∀ o ∈ O, q * o * q⁻¹ ∈ O) (hdisj : ∀ x ∈ Q, x ∈ O → x = 1) :
    (Nat.card O).factorization p + (Nat.card Q).factorization p ≤ (Nat.card G).factorization p := by
  have hO : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hQ : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [← Finsupp.add_apply, ← Nat.factorization_mul hO hQ]
  exact (Nat.factorization_le_iff_dvd (mul_ne_zero hO hQ) hG).mpr
    (card_mul_card_dvd_of_normalizing O Q hQO hdisj) p

theorem sylow_bound_of_normalizing [Finite G] (p : ℕ) [Fact p.Prime] (O Q : Subgroup G)
    (hQ : IsPGroup p Q) (hQO : ∀ q ∈ Q, ∀ o ∈ O, q * o * q⁻¹ ∈ O) (hdisj : ∀ x ∈ Q, x ∈ O → x = 1) :
    (Nat.card O).factorization p + (Nat.card Q).factorization p ≤ (Nat.card G).factorization p := by
  have _ := hQ
  exact factorization_add_le_of_normalizing p O Q hQO hdisj

end CFSG.GH74.GLS.Stage4.Q9
