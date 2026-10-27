module

public import Certificates.Certificate36407
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix

namespace ModZ

variable {α : Type} [Group α] [DecidableEq α]

theorem commB_iff (g x : α) : commB g x = true ↔ g ∈ centralizer ({x} : Set α) := by
  rw [mem_centralizer_singleton_iff, commB, beq_iff_eq]

theorem natCard_subgroup {L : List α} (hL : ∀ x, x ∈ L) (hnd : L.Nodup) (H : Subgroup α)
    (p : α → Bool) (h : ∀ x, x ∈ H ↔ p x = true) : Nat.card H = (L.filter p).length := by
  have e : Nat.card H = Nat.card {x : α // p x = true} :=
    Nat.card_congr (Equiv.subtypeEquivRight h)
  rw [e, Nat.subtype_card ⟨↑(L.filter p), Multiset.coe_nodup.2 (hnd.filter p)⟩ (fun x => by
    simp only [Finset.mem_mk, Multiset.mem_coe, List.mem_filter, hL x, true_and])]
  rfl

theorem natCard_centralizer {L : List α} (hL : ∀ x, x ∈ L) (hnd : L.Nodup) (x : α) :
    Nat.card (centralizer ({x} : Set α)) = (L.filter fun g => commB g x).length :=
  natCard_subgroup hL hnd _ _ fun g => (commB_iff g x).symm

theorem natCard_centralizer_conj (g r : α) :
    Nat.card (centralizer ({g * r * g⁻¹} : Set α)) = Nat.card (centralizer ({r} : Set α)) := by
  refine Nat.card_congr ⟨fun y => ⟨g⁻¹ * y * g, ?_⟩, fun y => ⟨g * y * g⁻¹, ?_⟩, fun y => ?_,
    fun y => ?_⟩
  · have hy := mem_centralizer_singleton_iff.1 y.2
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * ↑y * g * r = g⁻¹ * (↑y * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * r * g⁻¹ * ↑y) * g := by rw [hy]
      _ = r * (g⁻¹ * ↑y * g) := by group
  · have hy := mem_centralizer_singleton_iff.1 y.2
    rw [mem_centralizer_singleton_iff]
    calc g * ↑y * g⁻¹ * (g * r * g⁻¹) = g * (↑y * r) * g⁻¹ := by group
      _ = g * (r * ↑y) * g⁻¹ := by rw [hy]
      _ = g * r * g⁻¹ * (g * ↑y * g⁻¹) := by group
  · exact Subtype.ext (by group)
  · exact Subtype.ext (by group)

theorem mem_iff_of_checkE {L : List α} (hL : ∀ x, x ∈ L) (hnd : L.Nodup) {inE : α → Bool}
    {N : ℕ} (h : checkE L inE N = true) (x : α) :
    inE x = true ↔ x = 1 ∨ (x * x = 1 ∧ (∃ g, g * g = x) ∧
      N ≤ Nat.card (centralizer ({x} : Set α))) := by
  simp only [checkE, List.all_eq_true] at h
  have hx := h x (hL x)
  rw [beq_iff_eq] at hx
  have hS : (∃ a, a ∈ L ∧ a * a = x) ↔ ∃ g, g * g = x :=
    ⟨fun ⟨a, _, ha⟩ => ⟨a, ha⟩, fun ⟨g, hg⟩ => ⟨g, hL g, hg⟩⟩
  rw [hx, natCard_centralizer hL hnd x]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem, List.mem_map, hS, and_assoc]

theorem conj_or_exp_of_checkC {L : List α} (hL : ∀ x, x ∈ L) (hnd : L.Nodup) {code : α → ℕ}
    (hcode : Function.Injective code) {inM inA : α → Bool} {t : α} {N e : ℕ} {R : List α}
    (h : checkC L code inM inA t N e R = true) {x : α} (hM : inM x = true)
    (hA : inA x = false) (hx : x * x = 1) (hC : Nat.card (centralizer ({x} : Set α)) = N) :
    (∃ g, g * x * g⁻¹ ∈ centralizer ({t} : Set α)) ∨
      ∃ y ∈ centralizer ({x} : Set α), y ^ e ≠ 1 := by
  simp only [checkC, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hx2 := h2 x (hL x)
  simp only [hM, hA, hx, beq_self_eq_true, Bool.not_true, Bool.false_or, List.any_eq_true,
    List.mem_map, List.contains_iff_mem, conjCodes] at hx2
  obtain ⟨_, ⟨r, hr, rfl⟩, hmem⟩ := hx2
  rw [List.map_map, List.mem_map] at hmem
  obtain ⟨g, -, hg⟩ := hmem
  have hgx : g * r * g⁻¹ = x := hcode hg
  have hlen : (L.filter fun g => commB g r).length = N := by
    rw [← natCard_centralizer hL hnd r, ← natCard_centralizer_conj g r, hgx, hC]
  have h1r := h1 r hr
  simp only [hlen, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, List.any_eq_true,
    List.mem_filter, bne_iff_ne, ne_eq, List.mem_map] at h1r
  rcases h1r with ⟨y, ⟨-, hy⟩, hye⟩ | ⟨p, ⟨k, -, rfl⟩, hk⟩
  · right
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · rw [← hgx, mem_centralizer_singleton_iff]
      have hy' := mem_centralizer_singleton_iff.1 ((commB_iff y r).1 hy)
      calc g * y * g⁻¹ * (g * r * g⁻¹) = g * (y * r) * g⁻¹ := by group
        _ = g * (r * y) * g⁻¹ := by rw [hy']
        _ = g * r * g⁻¹ * (g * y * g⁻¹) := by group
    · rw [conj_pow]
      intro h0
      apply hye
      calc y ^ e = g⁻¹ * (g * y ^ e * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group
  · left
    refine ⟨k * g⁻¹, ?_⟩
    have e1 : k * g⁻¹ * x * (k * g⁻¹)⁻¹ = k * r * k⁻¹ := by rw [← hgx]; group
    rw [e1, ← commB_iff]
    exact hk

end ModZ

namespace Z4M

theorem inA_iff (p : Z4M) : inA p = true ↔ p ∈ Am := by
  simp only [inA, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨⟨hs, ha⟩, hb⟩, hc⟩ => ⟨hs, ha, hb, hc⟩, fun ⟨hs, ha, hb, hc⟩ => ⟨⟨⟨hs, ha⟩, hb⟩, hc⟩⟩

theorem inM_iff (p : Z4M) : inM p = true ↔ p ∈ Mm := by
  simp only [inM, beq_iff_eq]
  rfl

theorem inE_iff (p : Z4M) : inE p = true ↔ p ∈ Em := by
  simp only [inE, Bool.and_eq_true, beq_iff_eq, inA_iff]
  exact ⟨fun ⟨⟨⟨hA, h0⟩, h1⟩, h2⟩ => ⟨hA, h0, h1, h2⟩, fun ⟨hA, h0, h1, h2⟩ => ⟨⟨⟨hA, h0⟩, h1⟩, h2⟩⟩

theorem toCode_injective : Function.Injective toCode := fun p q h => by
  rw [← ofCode_toCode p, h, ofCode_toCode]

theorem card_Z4M : Nat.card Z4M = 1024 := by
  rw [Nat.card_eq_fintype_card]
  show (allL ()).length = 1024
  rw [allL, List.length_map, List.length_range]

end Z4M

namespace Z8M

variable {u : (ZMod 8)ˣ}

theorem inA_iff (p : Z8M u) : inA p = true ↔ p ∈ Am u := by
  simp only [inA, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨⟨hs, ha⟩, hb⟩, hc⟩ => ⟨hs, ha, hb, hc⟩, fun ⟨hs, ha, hb, hc⟩ => ⟨⟨⟨hs, ha⟩, hb⟩, hc⟩⟩

theorem inM_iff (p : Z8M u) : inM p = true ↔ p ∈ Mm u := by
  simp only [inM, beq_iff_eq]
  rfl

theorem toCode_injective : Function.Injective (toCode (u := u)) := fun p q h => by
  rw [← ofCode_toCode p, h, ofCode_toCode]

theorem card_Z8M : Nat.card (Z8M u) = 8192 := by
  rw [Nat.card_eq_fintype_card]
  show (allL u ()).length = 8192
  rw [allL, List.length_map, List.length_range]

theorem vec_tm : vec (tm u) = 0 := by
  funext i
  fin_cases i <;> rfl

end Z8M

theorem Z4M.mem_Em_iff (x : Z4M) :
    x ∈ Z4M.Em ↔ x = 1 ∨ (x * x = 1 ∧ (∃ g : Z4M, g * g = x) ∧
      2 ^ 8 ≤ Nat.card (centralizer ({x} : Set Z4M))) := by
  rw [← inE_iff]
  exact ModZ.mem_iff_of_checkE mem_allL nodup_allL Certificates.certificate36407.1 x

theorem Z4M.conj_or_exp {N e : ℕ}
    (hNe : (N = 2 ^ 7 ∧ e = 4) ∨ (N = 2 ^ 8 ∧ e = 8)) (x : Z4M) (hM : x ∈ Z4M.Mm)
    (hA : x ∉ Z4M.Am) (hx : x * x = 1) (hC : Nat.card (centralizer ({x} : Set Z4M)) = N) :
    (∃ g : Z4M, g * x * g⁻¹ ∈ centralizer ({Z4M.tm} : Set Z4M)) ∨
      ∃ y ∈ centralizer ({x} : Set Z4M), y ^ e ≠ 1 := by
  have h : ModZ.checkC (allL ()) toCode inM inA tm (2 ^ 7) 4 (reps ()) = true ∧
      ModZ.checkC (allL ()) toCode inM inA tm (2 ^ 8) 8 (reps ()) = true := by
    have h0 := Certificates.certificate36407.2.1
    unfold z4CheckC at h0
    exact Bool.and_eq_true_iff.1 h0
  have hM' := (inM_iff x).2 hM
  have hA' : inA x = false := Bool.eq_false_iff.2 fun h' => hA ((inA_iff x).1 h')
  rcases hNe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ModZ.conj_or_exp_of_checkC mem_allL nodup_allL toCode_injective h.1 hM' hA' hx hC
  · exact ModZ.conj_or_exp_of_checkC mem_allL nodup_allL toCode_injective h.2 hM' hA' hx hC

theorem Z8M.conj_or_exp {u : (ZMod 8)ˣ}
    (hu : (u : ZMod 8) = -1 ∨ (u : ZMod 8) = 3) (x : Z8M u) (hM : x ∈ Z8M.Mm u)
    (hA : x ∉ Z8M.Am u) (hx : x * x = 1)
    (hC : Nat.card (centralizer ({x} : Set (Z8M u))) = 2 ^ 8) :
    (∃ g : Z8M u, g * x * g⁻¹ ∈ centralizer ({Z8M.tm u} : Set (Z8M u))) ∨
      ∃ y ∈ centralizer ({x} : Set (Z8M u)), y ^ 8 ≠ 1 := by
  have hM' := (inM_iff x).2 hM
  have hA' : inA x = false := Bool.eq_false_iff.2 fun h' => hA ((inA_iff x).1 h')
  have hu' : u = -1 ∨ u = uThree := by
    rcases hu with h | h
    · left
      exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
    · right
      exact Units.ext h
  rcases hu' with rfl | rfl
  · exact ModZ.conj_or_exp_of_checkC mem_allL nodup_allL toCode_injective
      Certificates.certificate36407.2.2.1 hM' hA' hx hC
  · exact ModZ.conj_or_exp_of_checkC mem_allL nodup_allL toCode_injective
      Certificates.certificate36407.2.2.2 hM' hA' hx hC

end CFSG.OddStandard.AltStdSmall4.G2
