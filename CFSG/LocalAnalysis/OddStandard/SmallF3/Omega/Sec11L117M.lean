module

public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem card_zpowers_eq_two {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rwa [pow_two]) hz1]

theorem sec11_card_le_inf_mul [Finite G] {P1 Q2 Q' : Subgroup G} {z : G}
    (hcomm : ∀ p ∈ P1, ∀ q ∈ Q2, p * q = q * p) (hinf : P1 ⊓ Q2 = zpowers z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hle : Q' ≤ P1 ⊔ Q2) :
    2 * Nat.card Q' ≤ Nat.card ↥(Q' ⊓ Q2) * Nat.card P1 := by
  have hzcard : Nat.card ↥(P1 ⊓ Q2) = 2 := by rw [hinf, card_zpowers_eq_two hz2 hz1]
  obtain ⟨hcard, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute P1 Q2 hcomm
  rw [hzcard] at hcard
  have hQ2pos : 0 < Nat.card Q2 := Nat.card_pos
  set m := Q2.relIndex (P1 ⊔ Q2) with hm
  have hmul : m * Nat.card Q2 = Nat.card ↥(P1 ⊔ Q2) := by
    rw [hm]
    have h := Subgroup.relIndex_mul_card (H := Q2) (K := P1 ⊔ Q2)
    rwa [inf_eq_left.mpr le_sup_right] at h
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact Nat.card_pos.ne' hmul.symm
  have hrel : Q2.relIndex Q' ≤ m := by
    rw [hm]
    exact Subgroup.relIndex_le_of_le_right hle hm0
  have hQ' : Q2.relIndex Q' * Nat.card ↥(Q2 ⊓ Q') = Nat.card Q' :=
    Subgroup.relIndex_mul_card (H := Q2) (K := Q')
  have h2m : 2 * m = Nat.card P1 := by
    apply Nat.eq_of_mul_eq_mul_right hQ2pos
    calc (2 * m) * Nat.card Q2 = 2 * (m * Nat.card Q2) := by rw [mul_assoc]
      _ = 2 * Nat.card ↥(P1 ⊔ Q2) := by rw [hmul]
      _ = Nat.card ↥(P1 ⊔ Q2) * 2 := by rw [mul_comm]
      _ = Nat.card P1 * Nat.card Q2 := hcard
  calc 2 * Nat.card Q'
      = 2 * (Q2.relIndex Q' * Nat.card ↥(Q2 ⊓ Q')) := by rw [hQ']
    _ = (2 * Q2.relIndex Q') * Nat.card ↥(Q2 ⊓ Q') := by ring
    _ ≤ (2 * m) * Nat.card ↥(Q2 ⊓ Q') :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hrel)
    _ = Nat.card P1 * Nat.card ↥(Q2 ⊓ Q') := by rw [h2m]
    _ = Nat.card ↥(Q' ⊓ Q2) * Nat.card P1 := by rw [inf_comm Q2 Q', mul_comm]

theorem sec11_two_mul_card_le [Finite G] {C Q' H : Subgroup G} {z : G}
    (hcomm : ∀ c ∈ C, ∀ q ∈ Q', c * q = q * c) (hinf : C ⊓ Q' = zpowers z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hH : H ≤ C ⊔ Q') :
    2 * Nat.card H ≤ Nat.card C * Nat.card Q' := by
  have hzcard : Nat.card ↥(C ⊓ Q') = 2 := by rw [hinf, card_zpowers_eq_two hz2 hz1]
  obtain ⟨hcard, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute C Q' hcomm
  rw [hzcard] at hcard
  calc 2 * Nat.card H ≤ 2 * Nat.card ↥(C ⊔ Q') :=
        Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le hH)
    _ = Nat.card ↥(C ⊔ Q') * 2 := by rw [mul_comm]
    _ = Nat.card C * Nat.card Q' := hcard

end CFSG.OddStandard.SmallF3.Omega
