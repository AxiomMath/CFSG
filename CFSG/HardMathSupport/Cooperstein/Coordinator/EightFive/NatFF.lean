module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NatFFBound
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderAlt
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {m : ℕ}

theorem mem_altFix_iff_altAct (B : Subgroup (Perm (Fin m))) (v : altHeart m) :
    v ∈ altFix m B ↔ ∀ b ∈ B, altAct b v = v := by
  rw [mem_altFix_iff]
  constructor
  · intro h b hb
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
    exact h b hb x rfl
  · intro h g hg x hx
    rw [← altAct_mk, hx]
    exact h g hg

theorem card_altHeart_eq_offIdx_mul (B : Subgroup (Perm (Fin m))) :
    Nat.card (altHeart m) = offIdx B * Nat.card (altFix m B) := by
  rw [← index_altFix, AddSubgroup.index_mul_card]

theorem card_evenVec_eq_offIdx_mul (B : Subgroup (Perm (Fin m))) :
    Nat.card (evenVec (Fin m)) = offIdx B * Nat.card (FixUp B) :=
  offIdx_mul_card.symm

theorem two_mul_card_evenVec_fin (hm : 1 ≤ m) : 2 * Nat.card (evenVec (Fin m)) = 2 ^ m := by
  rw [← evenWeight_eq_evenVec, Proving.card_evenWeight m hm, ← pow_succ']
  congr 1
  omega

theorem mul_card_altFix_le_iff (B : Subgroup (Perm (Fin m))) (k : ℕ) :
    k * Nat.card (altFix m B) ≤ Nat.card (altHeart m) ↔
      k * Nat.card (FixUp B) ≤ Nat.card (evenVec (Fin m)) := by
  rw [card_altHeart_eq_offIdx_mul B, card_evenVec_eq_offIdx_mul B,
    Nat.mul_le_mul_right_iff Nat.card_pos, Nat.mul_le_mul_right_iff Nat.card_pos]

theorem le_mul_card_altFix_iff (B : Subgroup (Perm (Fin m))) (k : ℕ) :
    Nat.card (altHeart m) ≤ k * Nat.card (altFix m B) ↔
      Nat.card (evenVec (Fin m)) ≤ k * Nat.card (FixUp B) := by
  rw [card_altHeart_eq_offIdx_mul B, card_evenVec_eq_offIdx_mul B,
    Nat.mul_le_mul_right_iff Nat.card_pos, Nat.mul_le_mul_right_iff Nat.card_pos]

theorem mul_card_altFix_eq_two_mul_iff (B : Subgroup (Perm (Fin m))) (k : ℕ) :
    k * Nat.card (altFix m B) = 2 * Nat.card (altHeart m) ↔
      k * Nat.card (FixUp B) = 2 * Nat.card (evenVec (Fin m)) := by
  rw [card_altHeart_eq_offIdx_mul B, card_evenVec_eq_offIdx_mul B, ← mul_assoc, ← mul_assoc,
    Nat.mul_left_inj Nat.card_pos.ne', Nat.mul_left_inj Nat.card_pos.ne']

theorem natFF_le (hm : 5 ≤ m) {B : Subgroup (Perm (Fin m))} (hB : ∀ b ∈ B, b * b = 1)
    (hΔ : ¬ IsMatchingGroup B) :
    Nat.card B * Nat.card (altFix m B) ≤ Nat.card (altHeart m) := by
  rw [mul_card_altFix_le_iff]
  have h := two_mul_card_mul_card_FixUp_le hB (by rwa [Nat.card_fin]) hΔ
  rw [Nat.card_fin, ← two_mul_card_evenVec_fin (by omega)] at h
  exact Nat.le_of_mul_le_mul_left h (by norm_num)

theorem natFF_matching (hm : 3 ≤ m) {B : Subgroup (Perm (Fin m))} (hΔ : IsMatchingGroup B) :
    Nat.card B * Nat.card (altFix m B) = 2 * Nat.card (altHeart m) := by
  obtain ⟨t, ht, ht2, rfl⟩ := hΔ
  rw [mul_card_altFix_eq_two_mul_iff,
    card_mul_card_FixUp_matchingGroup (by rwa [Nat.card_fin]) ht ht2, Nat.card_fin,
    two_mul_card_evenVec_fin (by omega)]

theorem natFF (hm : 5 ≤ m) {B : Subgroup (Perm (Fin m))} (hB : ∀ b ∈ B, b * b = 1) :
    (IsMatchingGroup B →
        Even m ∧ Nat.card B * Nat.card (altFix m B) = 2 * Nat.card (altHeart m)) ∧
      (¬ IsMatchingGroup B → Nat.card B * Nat.card (altFix m B) ≤ Nat.card (altHeart m)) :=
  ⟨fun h => ⟨by simpa using h.even_card, natFF_matching (by omega) h⟩, natFF_le hm hB⟩

theorem natFF_orbit (hm : 5 ≤ m) {B : Subgroup (Perm (Fin m))} (hB : ∀ b ∈ B, b * b = 1)
    (horb : ∀ i : Fin m, 4 ≤ Nat.card (orbit B i))
    (hoff : Nat.card (altHeart m) ≤ Nat.card B * Nat.card (altFix m B)) :
    m = 8 ∧ Nat.card B = 8 ∧ IsPretransitive B (Fin m) := by
  rw [le_mul_card_altFix_iff] at hoff
  have h2 := two_mul_card_evenVec_fin (m := m) (by omega)
  have h := orbit_offender_shape hB (by rwa [Nat.card_fin]) horb
    (by rw [Nat.card_fin, ← h2]; exact Nat.mul_le_mul_left 2 hoff)
  rwa [Nat.card_fin] at h

theorem natFF_fpf (hm : 8 ≤ m) {b : Perm (Fin m)} (hb : b * b = 1) (hfix : ∀ i, b i ≠ i) :
    4 * Nat.card (altFix m (Subgroup.zpowers b)) ≤ Nat.card (altHeart m) := by
  rw [mul_card_altFix_le_iff]
  have h := eight_mul_card_FixUp_zpowers_le (by rwa [Nat.card_fin]) hb hfix
  rw [Nat.card_fin, ← two_mul_card_evenVec_fin (by omega)] at h
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
