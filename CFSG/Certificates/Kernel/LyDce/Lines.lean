module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.LyDce

open Equiv MulAction Pointwise

variable {n : ℕ}

theorem le_of_mul_le {a b c m : ℕ} (ha : 0 < a) (hm : 0 < m) (h : a * b ≤ m * c) (hc : c ≤ a)
    (hb : m ≤ b) : b ≤ m ∧ a ≤ c := by
  constructor
  · have : a * b ≤ a * m := by
      calc a * b ≤ m * c := h
        _ ≤ m * a := Nat.mul_le_mul_left m hc
        _ = a * m := Nat.mul_comm m a
    exact Nat.le_of_mul_le_mul_left this ha
  · have : m * a ≤ m * c := by
      calc m * a = a * m := Nat.mul_comm m a
        _ ≤ a * b := Nat.mul_le_mul_left a hb
        _ ≤ m * c := h
    exact Nat.le_of_mul_le_mul_left this hm

theorem lines_of_card {B Y : Subgroup (Perm (Fin n))} (hYB : Y ≤ B) {O : Set (Fin n)}
    (hY : ∀ y ∈ Y, y • O = O) {m : ℕ} (L : Fin m → Set (Fin n)) (hL : Function.Injective L)
    (hLB : ∀ i, ∃ g ∈ B, L i = g • O) (hB : Nat.card B ≤ m * Nat.card Y) :
    (∀ g ∈ B, ∃ i, g • O = L i) ∧ (∀ g ∈ B, g • O = O → g ∈ Y) := by
  classical
  have hcard : Nat.card (stabilizer B O) * Nat.card (orbit B O) = Nat.card B := by
    have h := Subgroup.card_mul_index (stabilizer B O)
    rwa [index_stabilizer] at h
  have hsub : Set.range L ⊆ orbit B O := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨g, hg, e⟩ := hLB i
    exact ⟨⟨g, hg⟩, e.symm⟩
  have hfin : (orbit B O).Finite := Set.toFinite _
  have hm : m ≤ Nat.card (orbit B O) := by
    have h := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_range_of_injective hL, Nat.card_fin] at h
    rwa [Nat.card_coe_set_eq]
  have hYc : Nat.card (Y.subgroupOf B) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv
  have hYS : Y.subgroupOf B ≤ stabilizer B O := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    exact hY y hy
  have hle : Nat.card (Y.subgroupOf B) ≤ Nat.card (stabilizer B O) :=
    Subgroup.card_le_of_le hYS
  have hpos : 0 < Nat.card (stabilizer B O) := Nat.card_pos
  have hO : 0 < Nat.card (orbit B O) := by
    have : Nonempty (orbit B O) := ⟨⟨O, mem_orbit_self O⟩⟩
    exact Nat.card_pos
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have h1 : Nat.card (stabilizer B O) * Nat.card (orbit B O) ≤ 0 := by
        rw [hcard]
        simpa using hB
      have := Nat.mul_pos hpos hO
      omega
    · exact h0
  obtain ⟨h1, h2⟩ := le_of_mul_le hpos hmpos (hcard.trans_le (hB.trans_eq (by rw [hYc])))
    hle hm
  have hst : Y.subgroupOf B = stabilizer B O := Subgroup.eq_of_le_of_card_ge hYS h2
  refine ⟨fun g hg => ?_, fun g hg hgO => ?_⟩
  · have heq : Set.range L = orbit B O := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
      rw [Set.ncard_range_of_injective hL, Nat.card_fin, ← Nat.card_coe_set_eq]
      exact h1
    have hmem : g • O ∈ orbit B O := ⟨⟨g, hg⟩, rfl⟩
    rw [← heq] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, hi.symm⟩
  · have hs : (⟨g, hg⟩ : B) ∈ stabilizer B O := hgO
    rw [← hst, Subgroup.mem_subgroupOf] at hs
    exact hs

theorem cover_of_lines {B Y S : Subgroup (Perm (Fin n))} {O : Set (Fin n)} {m : ℕ}
    {L : Fin m → Set (Fin n)} (hlines : ∀ g ∈ B, ∃ i, g • O = L i)
    (hstab : ∀ g ∈ B, g • O = O → g ∈ Y) (hSB : S ≤ B) {R : Set (Perm (Fin n))}
    (hRB : R ⊆ B) (hfor : ∀ i, ∃ s ∈ S, ∃ r ∈ R, L i = (s * r) • O) :
    ∀ g ∈ B, ∃ s ∈ S, ∃ r ∈ R, ∃ y ∈ Y, g = s * r * y := by
  intro g hg
  obtain ⟨i, hi⟩ := hlines g hg
  obtain ⟨s, hs, r, hr, e⟩ := hfor i
  have hsr : s * r ∈ B := B.mul_mem (hSB hs) (hRB hr)
  refine ⟨s, hs, r, hr, (s * r)⁻¹ * g, hstab _ (B.mul_mem (B.inv_mem hsr) hg) ?_, by group⟩
  rw [mul_smul, hi, e, ← mul_smul, inv_mul_cancel, one_smul]

end CFSG.KC.LyDce

end
