module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCElementaryCoset
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem elementary_series_involution_coset_conjugacy {G : Type*} [Group G] [Finite G]
    {W : Subgroup G} (_hW : IsPGroup 2 W) {a : G} (ha : orderOf a = 2)
    (haW : a ∈ normalizer (W : Set G)) (_haW' : a ∉ W) {r : ℕ} (_hr : 1 ≤ r)
    (V : Fin (r + 1) → Subgroup G) (hV0 : V 0 = ⊥) (hVr : V (Fin.last r) = W)
    (hVle : ∀ i : Fin r, V i.castSucc ≤ V i.succ) (_hVW : ∀ i, ((V i).subgroupOf W).Normal)
    (haV : ∀ i, a ∈ normalizer (V i : Set G))
    [∀ i : Fin r, ((V i.castSucc).subgroupOf (V i.succ)).Normal]
    [∀ i : Fin r, IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))]
    (hC : ∀ i : Fin r, {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x} =
      Set.range fun x => x⁻¹ * sectionRightConj (haV i.succ) (haV i.castSucc) x) :
    {x | (∃ w ∈ W, x = a * w) ∧ orderOf x = 2} = {x | ∃ w ∈ W, x = w⁻¹ * a * w} ∧
      Nat.card (W ⊓ centralizer {a} : Subgroup G) =
        ∏ i : Fin r, Nat.card {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x} ∧
      Nat.card (W ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card W ∧
      Nat.card {x | (∃ w ∈ W, x = a * w) ∧ orderOf x = 2} =
        Nat.card (W ⊓ centralizer {a} : Subgroup G) := by
  classical
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  set c : Fin r → ℕ := fun i =>
    Nat.card {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x} with hc
  have key : ∀ i : Fin (r + 1),
      (∀ k ∈ V i, a * k * (a * k) = 1 → ∃ m ∈ V i, a * k = m⁻¹ * a * m) ∧
        Nat.card (V i ⊓ centralizer {a} : Subgroup G) =
          ∏ j ∈ Finset.univ.filter (fun j : Fin r => j.castSucc < i), c j ∧
        Nat.card (V i ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card (V i) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [hV0]
      refine ⟨?_, ?_, ?_⟩
      · intro k hk _
        rw [mem_bot.mp hk]
        exact ⟨1, one_mem _, by group⟩
      · have hempty : Finset.univ.filter (fun j : Fin r => j.castSucc < 0) = ∅ := by
          ext j
          simp
        rw [hempty, Finset.prod_empty, bot_inf_eq, card_bot]
      · rw [bot_inf_eq, card_bot, one_pow]
    | succ i ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      have hLK := hVle i
      refine ⟨fun k hk hsq =>
        coset_conj_of_section hLK (haV i.succ) (haV i.castSucc) ha2 (hC i) ih1 hk hsq, ?_, ?_⟩
      · have hcard := card_inf_centralizer_eq_mul_card_fixed hLK (haV i.succ) (haV i.castSucc) ha2
          ih1
        have hfilter : Finset.univ.filter (fun j : Fin r => j.castSucc < i.succ) =
            insert i (Finset.univ.filter (fun j : Fin r => j.castSucc < i.castSucc)) := by
          ext j
          simp [Fin.castSucc_lt_succ_iff, Fin.castSucc_lt_castSucc_iff, le_iff_lt_or_eq, or_comm]
        rw [hfilter, Finset.prod_insert (by simp), hcard, ih2, mul_comm]
      · have hcard := card_inf_centralizer_eq_mul_card_fixed hLK (haV i.succ) (haV i.castSucc) ha2
          ih1
        have hsq := card_eq_card_fixed_sq (sectionRightConj (haV i.succ) (haV i.castSucc)) (hC i)
        have hK := card_eq_card_quotient_mul_card_subgroup ((V i.castSucc).subgroupOf (V i.succ))
        rw [Nat.card_congr (subgroupOfEquivOfLe hLK).toEquiv, hsq, ← ih3] at hK
        rw [hK, hcard]
        ring
  obtain ⟨hconj, hprod, hsq⟩ := key (Fin.last r)
  rw [hVr] at hconj hprod hsq
  have hall : Finset.univ.filter (fun j : Fin r => j.castSucc < Fin.last r) = Finset.univ := by
    ext j
    simp [Fin.castSucc_lt_last]
  rw [hall] at hprod
  have horbit : {x | (∃ w ∈ W, x = a * w) ∧ orderOf x = 2} = {x | ∃ w ∈ W, x = w⁻¹ * a * w} := by
    ext x
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hx⟩
      have hx2 : a * w * (a * w) = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
      exact hconj w hw hx2
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨a⁻¹ * w⁻¹ * a * w,
        W.mul_mem (inv_mul_mul_mem_of_mem_normalizer haW (W.inv_mem hw)) hw, by group⟩, ?_⟩
      have h := MulEquiv.orderOf_eq (MulAut.conj w⁻¹) a
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h, ha]
  refine ⟨horbit, hprod, hsq, ?_⟩
  have horb := card_conj_orbit_mul_card_inf_centralizer W a
  rw [← horbit, ← hsq, pow_two] at horb
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos horb

end CFSG.LocalAnalysis.ComponentInitial
