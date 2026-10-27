module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem Std.orderOf_t (h : Std G L E t) : orderOf t = 2 :=
  orderOf_eq_two_of_center h.card_center h.center_eq

theorem Std.t_mem_E (h : Std G L E t) : t ∈ E := h.m24.t_mem

theorem Std.E_comm (h : Std G L E t) : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := h.facts.E_comm

theorem Std.L_le_H (h : Std G L E t) : L ≤ centralizer ({t} : Set G) := h.facts.le_centralizer

theorem Std.E_le_H (h : Std G L E t) : E ≤ centralizer ({t} : Set G) :=
  h.E_le.trans h.L_le_H

theorem Std.relIndex_L_H (h : Std G L E t) : L.relIndex (centralizer ({t} : Set G)) = 2 := by
  have htL : t ∈ L := by
    have ht : t ∈ zpowers t := Subgroup.mem_zpowers t
    rw [← h.center_eq] at ht
    rcases ht with ⟨x, _, hx⟩
    exact hx ▸ x.2
  have hsup : L ⊔ centralizer (L : Set G) = L := by
    rw [h.cent]
    exact sup_eq_left.mpr (Subgroup.zpowers_le.mpr htL)
  have hle : L.relIndex (centralizer ({t} : Set G)) ≤ 2 := by
    have houter := h.facts.outer
    rwa [hsup] at houter
  have hne : L.relIndex (centralizer ({t} : Set G)) ≠ 1 := by
    intro h1
    exact h.ne (le_antisymm (Subgroup.relIndex_eq_one.mp h1) h.L_le_H)
  haveI : Nonempty ↥(centralizer ({t} : Set G)) := ⟨1, Subgroup.one_mem _⟩
  have hpos : 0 < L.relIndex (centralizer ({t} : Set G)) :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (H := L)
      (K := centralizer ({t} : Set G))) Nat.card_pos
  omega

theorem Std.card_L (h : Std G L E t) :
    Nat.card ↥L = 2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 := by
  have hquo : Nat.card (L ⧸ center L) = 64561751654400 := by
    obtain ⟨e⟩ := h.quo
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Fi22.card_Fi22
  have hmul : Nat.card ↥L = Nat.card (L ⧸ center L) * Nat.card (center L) := by
    rw [← Subgroup.index_mul_card (H := center L), Subgroup.index_eq_card]
  rw [hmul, hquo, h.card_center]
  norm_num

theorem Std.card_H (h : Std G L E t) :
    Nat.card ↥(centralizer ({t} : Set G)) = 2 ^ 19 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 := by
  have hrc := Subgroup.relIndex_mul_card (H := L) (K := centralizer ({t} : Set G))
  rw [h.relIndex_L_H, inf_eq_left.mpr h.L_le_H] at hrc
  rw [← hrc, h.card_L]
  norm_num

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
