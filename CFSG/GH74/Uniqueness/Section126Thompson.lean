module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open CFSG.ShultStronglyClosedTI.InvolutionCounting

section Thompson1

variable {G : Type*} [Group G] [Finite G]

theorem card_mul_card_centralizer_eq_of_single_class {u z w₀ : G} (hu : orderOf u = 2)
    (hz : orderOf z = 2) (hw₀ : orderOf w₀ = 2) (huz : ¬ IsConj u z)
    (hsupp : ∀ w : G, orderOf w = 2 → ¬ IsConj w₀ w → thompsonPairCount u z w = 0)
    (h1 : thompsonPairCount u z w₀ = 1) :
    Nat.card G * Nat.card ↥(Subgroup.centralizer ({w₀} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) *
        Nat.card ↥(Subgroup.centralizer ({z} : Set G)) := by
  classical
  have := Fintype.ofFinite G
  have hcount := card_conjugatesOf_mul_eq_sum (mul_self_eq_one_of_orderOf_eq_two hu)
    (mul_self_eq_one_of_orderOf_eq_two hz) huz
  have hterm : ∀ w ∈ Finset.univ.filter (fun w : G => orderOf w = 2),
      thompsonPairCount u z w = if w ∈ conjugatesOf w₀ then 1 else 0 := by
    intro w hw
    have hw2 := (Finset.mem_filter.mp hw).2
    by_cases hc : w ∈ conjugatesOf w₀
    · simp only [hc, ↓reduceIte]
      rw [← thompsonPairCount_eq_of_isConj u z (show IsConj w₀ w from hc)]
      exact h1
    · simp only [hc, ↓reduceIte]
      exact hsupp w hw2 hc
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole] at hcount
  have hfilt : (Finset.univ.filter (fun w : G => orderOf w = 2)).filter
      (fun w => w ∈ conjugatesOf w₀) = (conjugatesOf w₀).toFinset := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨(orderOf_eq_of_isConj (show IsConj w₀ w from h)).symm.trans hw₀, h⟩
  rw [hfilt, ← Nat.card_eq_card_toFinset, Nat.cast_id] at hcount
  have hu' := card_centralizer_mul_card_conjugatesOf u
  have hz' := card_centralizer_mul_card_conjugatesOf z
  have hw' := card_centralizer_mul_card_conjugatesOf w₀
  have hWpos : 0 < Nat.card (conjugatesOf w₀) := by
    rcases Nat.eq_zero_or_pos (Nat.card (conjugatesOf w₀)) with h | h
    · rw [h, mul_zero] at hw'
      exact absurd hw'.symm Nat.card_pos.ne'
    · exact h
  refine Nat.eq_of_mul_eq_mul_right hWpos ?_
  calc Nat.card G * Nat.card ↥(Subgroup.centralizer ({w₀} : Set G)) * Nat.card (conjugatesOf w₀)
      = Nat.card G * (Nat.card ↥(Subgroup.centralizer ({w₀} : Set G)) *
          Nat.card (conjugatesOf w₀)) := by ring
    _ = Nat.card G * Nat.card G := by rw [hw']
    _ = (Nat.card ↥(Subgroup.centralizer ({u} : Set G)) * Nat.card (conjugatesOf u)) *
          (Nat.card ↥(Subgroup.centralizer ({z} : Set G)) * Nat.card (conjugatesOf z)) := by
        rw [hu', hz']
    _ = Nat.card ↥(Subgroup.centralizer ({u} : Set G)) *
          Nat.card ↥(Subgroup.centralizer ({z} : Set G)) *
          (Nat.card (conjugatesOf u) * Nat.card (conjugatesOf z)) := by ring
    _ = _ := by rw [hcount]

omit [Finite G] in
theorem sec126_card_filter_mem_subgroup [Fintype G] [DecidableEq G] (L : Subgroup G)
    [DecidablePred (· ∈ L)] : (Finset.univ.filter (· ∈ L)).card = Nat.card ↥L := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem commute_of_card_inf_le {u z : G} (huz : u * z = z * u)
    (hcard : Nat.card G * Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer ({z} : Set G)) ≤
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) *
        Nat.card ↥(Subgroup.centralizer ({z} : Set G))) :
    ∀ y : G, IsConj z y → u * y = y * u := by
  classical
  have := Fintype.ofFinite G
  set H := Subgroup.centralizer ({u} : Set G) with hH
  set K := Subgroup.centralizer ({z} : Set G) with hK
  have hzH : z ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact huz.symm
  set φ : G → G := fun h => h⁻¹ * z * h with hφ
  set HF : Finset G := Finset.univ.filter (· ∈ H) with hHF
  set O : Finset G := HF.image φ with hO
  have hfiber : ∀ a ∈ O, (HF.filter (fun h => φ h = a)).card ≤ Nat.card ↥(H ⊓ K) := by
    intro a ha
    obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_image.mp ha
    have hh₀H : h₀ ∈ H := (Finset.mem_filter.mp hh₀).2
    rw [← sec126_card_filter_mem_subgroup (H ⊓ K)]
    refine Finset.card_le_card_of_injOn (fun h => h * h₀⁻¹) ?_ ?_
    · intro h hh
      obtain ⟨hhHF, hφh⟩ := Finset.mem_filter.mp hh
      have hhH : h ∈ H := (Finset.mem_filter.mp hhHF).2
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      refine Subgroup.mem_inf.mpr ⟨H.mul_mem hhH (H.inv_mem hh₀H), ?_⟩
      rw [hK, Subgroup.mem_centralizer_singleton_iff]
      have h2 : h⁻¹ * z * h = h₀⁻¹ * z * h₀ := hφh
      calc h * h₀⁻¹ * z = h * (h₀⁻¹ * z * h₀) * h₀⁻¹ := by group
        _ = h * (h⁻¹ * z * h) * h₀⁻¹ := by rw [h2]
        _ = z * (h * h₀⁻¹) := by group
    · intro a _ b _ hab
      simpa using hab
  have hHle : Nat.card H ≤ Nat.card ↥(H ⊓ K) * O.card := by
    rw [← sec126_card_filter_mem_subgroup H]
    exact Finset.card_le_mul_card_image HF _ hfiber
  have hT := card_centralizer_mul_card_conjugatesOf z
  have hOsub : O ⊆ (conjugatesOf z).toFinset := by
    intro y hy
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Set.mem_toFinset]
    exact isConj_iff.mpr ⟨h⁻¹, by simp [hφ]⟩
  have hOle : O.card ≤ Nat.card (conjugatesOf z) := by
    rw [Nat.card_eq_card_toFinset]
    exact Finset.card_le_card hOsub
  have hnpos : 0 < Nat.card ↥(H ⊓ K) := Nat.card_pos
  have hkpos : 0 < Nat.card ↥K := Nat.card_pos
  have hTle : Nat.card (conjugatesOf z) ≤ O.card := by
    have h1 : Nat.card (conjugatesOf z) * (Nat.card ↥(H ⊓ K) * Nat.card ↥K) ≤
        O.card * (Nat.card ↥(H ⊓ K) * Nat.card ↥K) := by
      calc Nat.card (conjugatesOf z) * (Nat.card ↥(H ⊓ K) * Nat.card ↥K)
          = Nat.card G * Nat.card ↥(H ⊓ K) := by rw [← hT]; ring
        _ ≤ Nat.card ↥H * Nat.card ↥K := hcard
        _ ≤ (Nat.card ↥(H ⊓ K) * O.card) * Nat.card ↥K := Nat.mul_le_mul_right _ hHle
        _ = O.card * (Nat.card ↥(H ⊓ K) * Nat.card ↥K) := by ring
    exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos hnpos hkpos)
  have hOeq : O = (conjugatesOf z).toFinset := by
    refine Finset.eq_of_subset_of_card_le hOsub ?_
    rw [← Nat.card_eq_card_toFinset]
    exact hTle
  intro y hy
  have hyO : y ∈ O := by
    rw [hOeq, Set.mem_toFinset]
    exact hy
  obtain ⟨h, hhHF, rfl⟩ := Finset.mem_image.mp hyO
  have hhH : h ∈ H := (Finset.mem_filter.mp hhHF).2
  have hyH : h⁻¹ * z * h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hhH) hzH) hhH
  exact (Subgroup.mem_centralizer_singleton_iff.mp hyH).symm

end Thompson1

end CFSG.GH74.Uniqueness
