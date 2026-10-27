module

public import CFSG.GroupTheory.Transfer.YoshidaParityOdd

import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

private theorem card_centralizer_singleton_eq_of_isConj {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine Nat.card_congr
    { toFun := fun u => ⟨c * u * c⁻¹, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      invFun := fun u => ⟨c⁻¹ * u * c, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      left_inv := fun u => Subtype.ext (by simp only; group)
      right_inv := fun u => Subtype.ext (by simp only; group) }
  · have hu := Subgroup.mem_centralizer_singleton_iff.1 u.2
    rw [← hc]
    calc c * (u : G) * c⁻¹ * (c * x * c⁻¹) = c * ((u : G) * x) * c⁻¹ := by group
      _ = c * (x * (u : G)) * c⁻¹ := by rw [hu]
      _ = c * x * c⁻¹ * (c * (u : G) * c⁻¹) := by group
  · have hu := Subgroup.mem_centralizer_singleton_iff.1 u.2
    generalize (u : G) = v at hu ⊢
    rw [← hc] at hu
    calc c⁻¹ * v * c * x = c⁻¹ * (v * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * v) * c := by rw [hu]
      _ = x * (c⁻¹ * v * c) := by group

theorem exists_isConj_mem_not_four_dvd_relIndex {t : G} (ht : t ^ 2 = 1)
    (htG : t ∈ _root_.commutator G) {H K : Subgroup G} (hKH : K ≤ H) (hidx : K.relIndex H = 2)
    (hH : Odd H.index)
    (htc : (H ⊓ Subgroup.centralizer ({t} : Set G)).relIndex H ≤ 2) :
    ∃ y : G, IsConj t y ∧ y ∈ K ∧
      ¬ 4 ∣ (H ⊓ Subgroup.centralizer ({y} : Set G)).relIndex H := by
  obtain ⟨y, hty, hyK, hodd⟩ := exists_isConj_mem_of_odd_index ht htG hKH hidx hH
  refine ⟨y, hty, hyK, ?_⟩
  set Cy : Subgroup G := Subgroup.centralizer ({y} : Set G) with hCy
  set Ct : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCt
  have hcard : Nat.card Ct = Nat.card Cy := card_centralizer_singleton_eq_of_isConj hty
  have h1 := Subgroup.relIndex_mul_card (H ⊓ Cy) Cy
  rw [inf_eq_left.mpr (inf_le_right : H ⊓ Cy ≤ Cy)] at h1
  have h2 := Subgroup.relIndex_mul_card (H ⊓ Cy) H
  rw [inf_eq_left.mpr (inf_le_left : H ⊓ Cy ≤ H)] at h2
  have h3 := Subgroup.relIndex_mul_card (H ⊓ Ct) H
  rw [inf_eq_left.mpr (inf_le_left : H ⊓ Ct ≤ H)] at h3
  have hdvd : Nat.card ↥(H ⊓ Ct) ∣ Nat.card Ct :=
    Subgroup.card_dvd_of_le (inf_le_right : H ⊓ Ct ≤ Ct)
  have hny : 0 < Nat.card ↥(H ⊓ Cy) := Nat.card_pos
  have hdt : 0 < (H ⊓ Ct).relIndex H := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at h3
    exact (Nat.card_pos (α := ↥H)).ne' h3.symm
  generalize (H ⊓ Cy).relIndex Cy = m at *
  generalize (H ⊓ Cy).relIndex H = dy at *
  generalize (H ⊓ Ct).relIndex H = dt at *
  generalize Nat.card ↥(H ⊓ Cy) = ny at *
  generalize Nat.card ↥(H ⊓ Ct) = nt at *
  intro h4
  have h5 : nt ∣ m * ny := by rw [h1, ← hcard]; exact hdvd
  have h6 : dy * ny ∣ (dt * m) * ny := by
    rw [h2, ← h3, mul_assoc]
    exact Nat.mul_dvd_mul_left dt h5
  have h7 : dy ∣ dt * m := Nat.dvd_of_mul_dvd_mul_right hny h6
  have h8 : 4 ∣ dt * m := h4.trans h7
  obtain ⟨k, hk⟩ := hodd
  interval_cases dt <;> omega

end CFSG.GroupTheory
