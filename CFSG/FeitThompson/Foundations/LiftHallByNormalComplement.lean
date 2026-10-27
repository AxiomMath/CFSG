module

public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {G : Type*} [Group G]

theorem isPiNumber_and_isPiNumber_compl_iff {π : Set ℕ} {n : ℕ} (hn : n ≠ 0) :
    (IsPiNumber π n ∧ IsPiNumber πᶜ n) ↔ n = 1 :=
  ⟨fun h => h.1.eq_one_of_compl h.2 hn, fun h => h ▸ ⟨isPiNumber_one, isPiNumber_one⟩⟩

theorem natCard_eq_mul_of_mul_eq_of_inf_eq_bot {N H K : Subgroup G}
    (hprod : (N : Set G) * (H : Set G) = (K : Set G)) (hdisj : N ⊓ H = ⊥) :
    Nat.card K = Nat.card N * Nat.card H := by
  have h := natCard_mul_mul_natCard_inf N H
  rw [hdisj, Subgroup.card_bot, mul_one, hprod] at h
  simpa using h

theorem isHallSubgroup_of_comap [Finite G] {π : Set ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPiNumber πᶜ (Nat.card N)) {J : Subgroup (G ⧸ N)} (hJ : IsHallSubgroup π J)
    {K H : Subgroup G} (hK : K = J.comap (QuotientGroup.mk' N))
    (hprod : (N : Set G) * (H : Set G) = (K : Set G)) (hdisj : N ⊓ H = ⊥) :
    IsHallSubgroup π H := by
  have hcardK : Nat.card K = Nat.card N * Nat.card H :=
    natCard_eq_mul_of_mul_eq_of_inf_eq_bot hprod hdisj
  have hindexK : K.index = J.index := by
    rw [hK]; exact Subgroup.index_comap_of_surjective J (QuotientGroup.mk'_surjective N)
  have hG : Nat.card G = Nat.card N * (Nat.card J * J.index) := by
    rw [Subgroup.card_mul_index J, Subgroup.card_eq_card_quotient_mul_card_subgroup N]
    ring
  have hJindex : 0 < J.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have key : Nat.card N * Nat.card H * J.index = Nat.card N * Nat.card J * J.index := by
    have h : Nat.card K * K.index = Nat.card G := Subgroup.card_mul_index K
    rw [hcardK, hindexK, hG] at h
    rw [h]; ring
  have hHJ : Nat.card H = Nat.card J :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (Nat.eq_of_mul_eq_mul_right hJindex key)
  refine ⟨hHJ ▸ hJ.1, ?_⟩
  have hHindex : H.index = Nat.card N * J.index := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H)) ?_
    rw [Subgroup.card_mul_index H, hG, hHJ]
    ring
  rw [hHindex]
  exact hN.mul hJ.2

theorem isHallSubgroup_of_comap_of_sup_eq [Finite G] {π : Set ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPiNumber πᶜ (Nat.card N)) {J : Subgroup (G ⧸ N)} (hJ : IsHallSubgroup π J)
    {K H : Subgroup G} (hK : K = J.comap (QuotientGroup.mk' N)) (hprod : K = N ⊔ H)
    (hdisj : N ⊓ H = ⊥) : IsHallSubgroup π H :=
  isHallSubgroup_of_comap hN hJ hK (by rw [hprod, Subgroup.normal_mul]) hdisj

end

end CFSG.FeitThompson

