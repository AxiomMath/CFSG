module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenT

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem lieModel_psu3_unpack {Gs : Type} [Group Gs] {p f : ℕ} (h : LieModel Gs .PSU 3 p f) :
    1 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ f) ^ 2 ∧
      Nonempty (Gs ≃* StatedProj (StatedSU 3 (p ^ f) F)) := by
  rcases h with ⟨-, hadm, K, iK, fK, hK, he⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact ⟨hadm.2.1, K, iK, fK, hK, he⟩
  all_goals exact absurd h0 (by norm_num)

section Counts

theorem isoIndexCount_four_ge {q k : ℕ} (hk : 3 ≤ k) : isoIndexCount q 4 k = 0 := by
  unfold isoIndexCount
  rw [Finset.prod_eq_zero (i := 2) (Finset.mem_range.mpr (by omega)) (by simp)]
  simp

theorem isoIndexCount_three_one {q : ℕ} (hq : 2 ≤ q) :
    isoIndexCount q 3 1 = (q : ℚ) ^ 3 + 1 := by
  have h2 : (q : ℚ) ^ 2 - 1 ≠ 0 := (pow_sub_one_pos hq (m := 2) (by norm_num)).ne'
  rw [isoIndexCount_one, div_eq_iff h2]
  norm_num [isoTerm]
  ring

theorem isoIndexCount_three_ge {q k : ℕ} (hk : 2 ≤ k) : isoIndexCount q 3 k = 0 := by
  unfold isoIndexCount
  rw [Finset.prod_eq_zero (i := 1) (Finset.mem_range.mpr (by omega)) (by simp)]
  simp

end Counts

section Parity

variable {p f : ℕ} {K : Type} [Field K]

theorem evenParabolics_hyp [Fact p.Prime] (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r)
    (hε : ε ≤ 1)
    (hev : ∀ k : ℕ, 1 ≤ k → ∀ idx : ℕ, 0 < idx → (idx : ℚ) = isoIndexCount (p ^ f) (2 * r + ε) k →
      Even idx) : EvenParabolics p (hypPSU h r ε) := by
  intro S M hSM hM
  obtain ⟨M', hM', hMM'⟩ := (eq_top_or_exists_le_coatom M).resolve_left hM
  have hmem : M' ∈ maximalParabolics h r ε := ⟨hM', _, ⟨S, rfl⟩, hSM.trans hMM'⟩
  obtain ⟨W, ⟨hW0, hWiso⟩, hM'W⟩ :=
    ((unitary_maximal_parabolics h hr hε).1 ▸ hmem :
      M' ∈ projIsoStabilizer h r ε '' {W | W ≠ ⊥ ∧ ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0})
  obtain ⟨hidx, hq, hpos, -⟩ := isotropic_stabilizer_index h W hWiso
  have hk1 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW0
  have hev' : Even M'.index := by
    rw [← hM'W, hidx]
    exact hev _ hk1 _ hpos hq
  exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hev').trans (Subgroup.index_dvd_of_le hMM'))

theorem even_isoIndexCount_four {q : ℕ} (hq : Odd q) (hq2 : 2 ≤ q) {k : ℕ} (hk : 1 ≤ k)
    {idx : ℕ} (hpos : 0 < idx) (h : (idx : ℚ) = isoIndexCount q (2 * 2 + 0) k) : Even idx := by
  have hodd : q % 2 = 1 := Nat.odd_iff.mp hq
  have h4 : 2 * 2 + 0 = 4 := rfl
  rw [h4] at h
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
  · rw [isoIndexCount_four_one hq2] at h
    have h2 : idx = (q ^ 2 + 1) * (q ^ 3 + 1) := by exact_mod_cast h
    rw [h2, Nat.even_iff]
    simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hodd]
  · rw [isoIndexCount_four_two hq2] at h
    have h2 : idx = (q + 1) * (q ^ 3 + 1) := by exact_mod_cast h
    rw [h2, Nat.even_iff]
    simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hodd]
  · rw [isoIndexCount_four_ge hk3] at h
    have : (idx : ℚ) = 0 := h
    have : idx = 0 := by exact_mod_cast this
    omega

theorem even_isoIndexCount_three {q : ℕ} (hq : Odd q) (hq2 : 2 ≤ q) {k : ℕ} (hk : 1 ≤ k)
    {idx : ℕ} (hpos : 0 < idx) (h : (idx : ℚ) = isoIndexCount q (2 * 1 + 1) k) : Even idx := by
  have hodd : q % 2 = 1 := Nat.odd_iff.mp hq
  have h3 : 2 * 1 + 1 = 3 := rfl
  rw [h3] at h
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · rw [isoIndexCount_three_one hq2] at h
    have h2 : idx = q ^ 3 + 1 := by exact_mod_cast h
    rw [h2, Nat.even_iff]
    simp [Nat.add_mod, Nat.pow_mod, hodd]
  · rw [isoIndexCount_three_ge hk2] at h
    have : (idx : ℚ) = 0 := h
    have : idx = 0 := by exact_mod_cast this
    omega

variable [Finite K]

theorem evenParabolics_u4 (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    EvenParabolics p (StatedProj (StatedSU 4 (p ^ f) K)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hq : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  have hq2 : 2 ≤ p ^ f :=
    h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  have hn : 1 ≤ 2 * 2 + 0 := by norm_num
  exact EvenParabolics.of_mulEquiv (hypPSUEquivStatedProj h hR hn).symm
    (evenParabolics_hyp h (by norm_num) (by norm_num) fun k hk idx hpos hidx =>
      even_isoIndexCount_four hq hq2 hk hpos hidx)

theorem evenParabolics_u3 (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    EvenParabolics p (StatedProj (StatedSU 3 (p ^ f) K)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hq : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  have hq2 : 2 ≤ p ^ f :=
    h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  have hn : 1 ≤ 2 * 1 + 1 := by norm_num
  exact EvenParabolics.of_mulEquiv (hypPSUEquivStatedProj h hR hn).symm
    (evenParabolics_hyp h (by norm_num) (by norm_num) fun k hk idx hpos hidx =>
      even_isoIndexCount_three hq hq2 hk hpos hidx)

end Parity

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
