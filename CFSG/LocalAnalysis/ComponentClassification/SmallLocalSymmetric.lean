module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFourGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.SmallLocal

open Equiv

variable {Ω : Type*}

theorem apply_eq_self_of_sq_apply_eq {σ : Perm Ω} (hodd : Odd (orderOf σ)) {i : Ω}
    (h : σ (σ i) = i) : σ i = i := by
  obtain ⟨r, hr⟩ := hodd
  have h2 : (σ ^ 2) i = i := by rw [pow_two, Perm.mul_apply, h]
  have hpow : (σ ^ (2 * r + 1)) i = i := by rw [← hr, pow_orderOf_eq_one, Perm.one_apply]
  rwa [pow_succ', pow_mul, Perm.mul_apply, Perm.pow_apply_eq_self_of_apply_eq_self h2] at hpow

theorem exists_involution_of_normal [DecidableEq Ω] [Fintype Ω] (h4 : 4 ≤ Fintype.card Ω)
    {D : Subgroup (Perm Ω)} (hD : D.Normal) {σ : Perm Ω} (hσD : σ ∈ D) (hσ : σ ≠ 1)
    (hodd : Odd (orderOf σ)) : ∃ x ∈ D, x ≠ 1 ∧ x * x = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  have hij : i ≠ σ i := fun h => hi h.symm
  have hjk : σ i ≠ σ (σ i) := fun h => hi (σ.injective h).symm
  have hik : i ≠ σ (σ i) := fun h => hi (apply_eq_self_of_sq_apply_eq hodd h.symm)
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, σ i, σ (σ i)} : Finset Ω)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact (Finset.card_le_three).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  have hli : l ≠ i := hl.1
  have hlj : l ≠ σ i := hl.2.1
  have hlk : l ≠ σ (σ i) := hl.2.2
  set j := σ i with hj
  set k := σ j with hk
  have hc : swap j k * swap i j ∈ D := by
    have h1 := mul_mem hσD (hD.conj_mem σ⁻¹ (inv_mem hσD) (swap i j))
    rw [← mul_assoc, ← mul_assoc, ← swap_apply_apply, swap_inv] at h1
    exact h1
  have hc' : swap k l * (swap j k * swap i j) * swap k l ∈ D := by
    simpa only [swap_inv] using hD.conj_mem _ hc (swap k l)
  set x := swap j k * swap i j * (swap k l * (swap j k * swap i j) * swap k l) with hx
  have hxD : x ∈ D := mul_mem hc hc'
  have hxi : x i = l := by
    simp [hx, swap_apply_of_ne_of_ne, hik, hli.symm, hli, hlj, hlk]
  have hxl : x l = i := by
    simp [hx, swap_apply_of_ne_of_ne, hij, hik, hjk, hlj.symm, hik.symm, hjk.symm]
  have hxj : x j = k := by
    simp [hx, swap_apply_of_ne_of_ne, hij, hik, hli.symm, hjk, hlj.symm]
  have hxk : x k = j := by
    simp [hx, swap_apply_of_ne_of_ne, hik.symm, hjk.symm, hli, hlj, hlk]
  have hxa : ∀ a, a ≠ i → a ≠ j → a ≠ k → a ≠ l → x a = a := by
    intro a hai haj hak hal
    simp [hx, swap_apply_of_ne_of_ne, hai, haj, hak, hal]
  refine ⟨x, hxD, fun h => hli (by rw [← hxi, h, Perm.one_apply]), Equiv.ext fun a => ?_⟩
  rw [Perm.mul_apply, Perm.one_apply]
  by_cases hai : a = i
  · rw [hai, hxi, hxl]
  by_cases haj : a = j
  · rw [haj, hxj, hxk]
  by_cases hak : a = k
  · rw [hak, hxk, hxj]
  by_cases hal : a = l
  · rw [hal, hxl, hxi]
  rw [hxa a hai haj hak hal, hxa a hai haj hak hal]

theorem symmetric_group_odd_core (Ω : Type*) [Fintype Ω] [DecidableEq Ω] :
    (Nat.card Ω = 3 → oddCore (Perm Ω) = alternatingGroup Ω) ∧
      (Nat.card Ω ≠ 3 → oddCore (Perm Ω) = ⊥) := by
  have hodd := odd_card_oddCore (H := Perm Ω)
  have hdvd : Nat.card (oddCore (Perm Ω)) ∣ (Nat.card Ω).factorial := by
    rw [← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card _
  refine ⟨fun h3 => ?_, fun h3 => ?_⟩
  · have : Nontrivial Ω := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    have hA : Nat.card (alternatingGroup Ω) = 3 := by
      have h := two_mul_card_alternatingGroup (α := Ω)
      rw [Fintype.card_perm, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h3,
        show Nat.factorial 3 = 6 from rfl] at h
      omega
    have hle : alternatingGroup Ω ≤ oddCore (Perm Ω) :=
      le_oddCore_of_normal_odd inferInstance (by rw [hA]; decide)
    have h3dvd : 3 ∣ Nat.card (oddCore (Perm Ω)) := hA ▸ Subgroup.card_dvd_of_le hle
    rw [h3] at hdvd
    have hD3 : Nat.card (oddCore (Perm Ω)) = 3 := by
      have hpos : 0 < Nat.card (oddCore (Perm Ω)) := Nat.card_pos
      have hle6 : Nat.card (oddCore (Perm Ω)) ≤ 6 := Nat.le_of_dvd (by decide) hdvd
      rw [Nat.odd_iff] at hodd
      interval_cases h : Nat.card (oddCore (Perm Ω)) <;> omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hD3, hA])).symm
  · by_cases h2 : Nat.card Ω ≤ 2
    · have hfac : (Nat.card Ω).factorial ≤ 2 := by
        rcases (show Nat.card Ω = 0 ∨ Nat.card Ω = 1 ∨ Nat.card Ω = 2 by omega) with h | h | h <;>
          rw [h] <;> decide
      have hle : Nat.card (oddCore (Perm Ω)) ≤ 2 :=
        (Nat.le_of_dvd (Nat.factorial_pos _) hdvd).trans hfac
      apply Subgroup.eq_bot_of_card_eq
      rw [Nat.odd_iff] at hodd
      omega
    · have h4 : 4 ≤ Fintype.card Ω := by
        rw [← Nat.card_eq_fintype_card]
        omega
      by_contra hne
      obtain ⟨⟨σ, hσD⟩, hσ⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hσ1 : σ ≠ 1 := fun h => hσ (Subtype.ext h)
      have hσodd : Odd (orderOf σ) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hσD)
      obtain ⟨x, hxD, hx1, hxx⟩ := exists_involution_of_normal h4 inferInstance hσD hσ1 hσodd
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
      have h2dvd := Subgroup.orderOf_dvd_natCard _ hxD
      rw [hx2] at h2dvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)

end CFSG.ComponentClassification.SmallLocal
