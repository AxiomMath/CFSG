module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarPerm
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

theorem two_mul_card_alt_inf_centralizer {a : Perm (Fin 8)} (ha : a * a = 1) (ha1 : a ≠ 1) :
    2 * Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({a} : Set (Perm (Fin 8)))) =
      Nat.card ↥(centralizer ({a} : Set (Perm (Fin 8)))) := by
  classical
  let C : Subgroup (Perm (Fin 8)) := centralizer ({a} : Set (Perm (Fin 8)))
  let f : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  have hker : f.ker = (alternatingGroup (Fin 8)).subgroupOf C := by
    show (Equiv.Perm.sign.comp C.subtype).ker = _
    rw [← MonoidHom.comap_ker]
    rfl
  have hcard_ker : Nat.card f.ker = Nat.card ↥(alternatingGroup (Fin 8) ⊓ C) := by
    rw [hker]
    have h2 := Subgroup.card_subtype C ((alternatingGroup (Fin 8)).subgroupOf C)
    rw [Subgroup.subgroupOf_map_subtype] at h2
    exact h2.symm
  have hp : ∃ p : Fin 8, a p ≠ p := by
    by_contra h
    push Not at h
    exact ha1 (Equiv.ext h)
  obtain ⟨p, hp⟩ := hp
  set q := a p with hq
  have hpq : p ≠ q := by rw [hq]; exact fun h => hp h.symm
  have haq : a q = p := by rw [hq]; exact apply_apply_of_mul_self ha p
  have hconj : a * swap p q * a⁻¹ = swap p q := by
    have h := Equiv.swap_apply_apply a p q
    rw [← hq, haq, swap_comm] at h
    exact h.symm
  have hcomm : swap p q * a = a * swap p q := by
    have h := congrArg (fun x : Perm (Fin 8) => x * a) hconj
    simpa [mul_assoc] using h.symm
  have hmem : swap p q ∈ C := by
    change swap p q ∈ centralizer ({a} : Set (Perm (Fin 8)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have htop : f.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro u
    rcases Int.units_eq_one_or u with h | h
    · rw [h]; exact f.range.one_mem
    · rw [h]
      exact ⟨⟨swap p q, hmem⟩, by simp [f, Equiv.Perm.sign_swap hpq]⟩
  have hcard_range : Nat.card f.range = 2 := by
    rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  have hmain := Subgroup.card_ker_mul_card_range f
  rw [hcard_ker, hcard_range] at hmain
  change 2 * Nat.card ↥(alternatingGroup (Fin 8) ⊓ C) = Nat.card ↥C
  rw [mul_comm]
  exact hmain

theorem card_alt_inf_centralizer_cases {a : Perm (Fin 8)} (ha : a * a = 1) :
    (a = 1 ∧
      Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({a} : Set (Perm (Fin 8)))) = 20160) ∨
    (Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({a} : Set (Perm (Fin 8)))) = 720 ∧
      sign a = -1) ∨
    (Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({a} : Set (Perm (Fin 8)))) = 96 ∧
      sign a = 1) ∨
    (Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({a} : Set (Perm (Fin 8)))) = 48 ∧
      sign a = -1) ∨
    (Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({a} : Set (Perm (Fin 8)))) = 192 ∧
      sign a = 1) := by
  classical
  generalize hk : Multiset.card a.cycleType = k
  have hct : a.cycleType = Multiset.replicate k 2 := by
    rw [cycleType_eq_replicate_two ha, hk]
  have hsupp : a.support.card = 2 * k := by
    rw [card_support_eq_two_mul_card_cycleType ha, hk]
  have hle : k ≤ 4 := by
    have h := Finset.card_le_univ a.support
    simp only [Fintype.card_fin] at h
    omega
  have hsign : sign a = (-1 : ℤˣ) ^ k := by
    rw [Equiv.Perm.sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul]
    rw [pow_add]
    have : (-1 : ℤˣ) ^ (k * 2) = 1 := by
      rw [mul_comm k 2, pow_mul, Int.units_pow_two, one_pow]
    rw [this, one_mul]
  have hcardC : Nat.card ↥(centralizer ({a} : Set (Perm (Fin 8)))) =
      (8 - 2 * k).factorial * 2 ^ k * k.factorial := by
    rw [nat_card_centralizer_of_mul_self ha]
    simp only [Fintype.card_fin]
    rw [hk]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  · left
    have ha1 : a = 1 := by
      apply cycleType_eq_zero.mp
      rw [hct]; simp
    refine ⟨ha1, ?_⟩
    subst ha1
    have hC1 : centralizer ({(1 : Perm (Fin 8))} : Set (Perm (Fin 8))) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_center_iff.mpr (fun g => by simp)
    rw [hC1, inf_top_eq, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · have ha1 : a ≠ 1 := by
      intro h1
      have hzero : Multiset.card a.cycleType = 0 := by rw [cycleType_eq_zero.mpr h1]; simp
      omega
    have hCval : Nat.card ↥(centralizer ({a} : Set (Perm (Fin 8)))) = 1440 := by
      rw [hcardC]; norm_num [Nat.factorial]
    have hkey := two_mul_card_alt_inf_centralizer ha ha1
    rw [hCval] at hkey
    right; left
    refine ⟨by omega, ?_⟩
    rw [hsign]; decide
  · have ha1 : a ≠ 1 := by
      intro h1
      have hzero : Multiset.card a.cycleType = 0 := by rw [cycleType_eq_zero.mpr h1]; simp
      omega
    have hCval : Nat.card ↥(centralizer ({a} : Set (Perm (Fin 8)))) = 192 := by
      rw [hcardC]; norm_num [Nat.factorial]
    have hkey := two_mul_card_alt_inf_centralizer ha ha1
    rw [hCval] at hkey
    right; right; left
    refine ⟨by omega, ?_⟩
    rw [hsign]; decide
  · have ha1 : a ≠ 1 := by
      intro h1
      have hzero : Multiset.card a.cycleType = 0 := by rw [cycleType_eq_zero.mpr h1]; simp
      omega
    have hCval : Nat.card ↥(centralizer ({a} : Set (Perm (Fin 8)))) = 96 := by
      rw [hcardC]; norm_num [Nat.factorial]
    have hkey := two_mul_card_alt_inf_centralizer ha ha1
    rw [hCval] at hkey
    right; right; right; left
    refine ⟨by omega, ?_⟩
    rw [hsign]; decide
  · have ha1 : a ≠ 1 := by
      intro h1
      have hzero : Multiset.card a.cycleType = 0 := by rw [cycleType_eq_zero.mpr h1]; simp
      omega
    have hCval : Nat.card ↥(centralizer ({a} : Set (Perm (Fin 8)))) = 384 := by
      rw [hcardC]; norm_num [Nat.factorial]
    have hkey := two_mul_card_alt_inf_centralizer ha ha1
    rw [hCval] at hkey
    right; right; right; right
    refine ⟨by omega, ?_⟩
    rw [hsign]; decide

theorem card_alt_inf_centralizer_swap {a : Perm (Fin 8)} (ha : a.IsSwap) :
    Nat.card ↥(alternatingGroup (Fin 8) ⊓ centralizer ({a} : Set (Perm (Fin 8)))) = 720 := by
  obtain ⟨x, y, hxy, rfl⟩ := ha
  have h2 : swap x y * swap x y = 1 := swap_mul_self x y
  have hne : swap x y ≠ 1 := by
    intro h
    have hx := congrFun (congrArg DFunLike.coe h) x
    rw [Equiv.swap_apply_left] at hx
    exact hxy hx.symm
  have hkey := two_mul_card_alt_inf_centralizer h2 hne
  have hCval : Nat.card ↥(centralizer ({swap x y} : Set (Perm (Fin 8)))) = 1440 := by
    rw [nat_card_centralizer_of_isSwap (σ := swap x y) ⟨x, y, hxy, rfl⟩]
    norm_num [Fintype.card_fin, Nat.factorial]
  rw [hCval] at hkey
  omega

end CFSG.OddStandard.AltStdSec.SwapPattern
