module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Subgroup MulAction

set_option linter.style.haveILetI false in
theorem card_le_prime_mul_ker {p : ℕ} [Fact p.Prime] {N E : Type} [Group N] [Finite N] [Group E]
    [Finite E] (hN : IsPGroup p N) (hE : Nat.card E = p ^ 3) (φ : N →* MulAut E)
    (hfix : ∀ g : N, φ g ≠ 1 → Nat.card {e : E // φ g e = e} = p) :
    Nat.card N ≤ p * Nat.card φ.ker := by
  classical
  have hp : p.Prime := Fact.out
  letI : MulAction N E := MulAction.compHom E φ
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fintype E := Fintype.ofFinite E
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group N E
  have hcard : ∀ g : N, Fintype.card (fixedBy E g) = if φ g = 1 then p ^ 3 else p := by
    intro g
    split_ifs with h1
    · have hall : ∀ e : E, e ∈ fixedBy E g := fun e => by
        rw [MulAction.mem_fixedBy]
        show φ g e = e
        rw [h1]
        rfl
      rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hall), ← Nat.card_eq_fintype_card, hE]
    · rw [← hfix g h1, Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.refl _)
  simp only [hcard] at hB
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at hB
  have hK : (Finset.univ.filter fun g : N => φ g = 1).card = Nat.card φ.ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun g : N => φ g = 1)
  rw [hK, Finset.card_univ, ← Nat.card_eq_fintype_card] at hsplit
  rw [← Nat.card_eq_fintype_card] at hB
  rw [hK] at hB
  set o := Fintype.card (Quotient (orbitRel N E))
  set n := Nat.card N
  set k := Nat.card φ.ker
  have hkn : k * φ.ker.index = n := Subgroup.card_mul_index _
  set m := φ.ker.index
  have hkpos : 0 < k := Nat.card_pos
  have hnk : (Finset.univ.filter fun g : N => ¬φ g = 1).card = n - k := by omega
  rw [hnk] at hB
  have hmdvd : m ∣ n := ⟨k, by rw [← hkn]; ring⟩
  obtain ⟨a, ha⟩ := hN.exists_card_eq
  have hmdvd' : m ∣ p ^ a := by rw [← ha]; exact hmdvd
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp hmdvd'
  by_contra hlt
  have hm : p < m := by
    by_contra hle
    apply hlt
    rw [← hkn, mul_comm]
    exact Nat.mul_le_mul_right k (not_lt.mp hle)
  have hb2 : 2 ≤ b := by
    by_contra hb1
    have : m ≤ p := by
      rw [hb]
      calc p ^ b ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    omega
  have hp2m : p ^ 2 ∣ m := by rw [hb]; exact pow_dvd_pow p hb2
  set o' := Nat.card (Quotient (orbitRel N E))
  have hmpos : 0 < m := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨s, hs⟩ := hp2m
  have hpm : p * m = p ^ 3 * s := by rw [hs]; ring
  set t := n - k with ht_def
  have ht : k + t = n := by
    have : k ≤ n := by rw [← hkn]; exact Nat.le_mul_of_pos_right k hmpos
    omega
  have key : k * (p ^ 3 + p ^ 3 * s) = k * (o' * p ^ 2 * s + p) := by
    have hB0 : k * p ^ 3 + t * p = o' * n := by
      rw [← Nat.card_eq_fintype_card] at hB
      exact hB
    have hB' : (k : ℤ) * p ^ 3 + t * p = o' * n := by exact_mod_cast hB0
    have hkn' : (k : ℤ) * m = n := by exact_mod_cast hkn
    have ht' : (k : ℤ) + t = n := by exact_mod_cast ht
    have hpm' : (p : ℤ) * m = p ^ 3 * s := by exact_mod_cast hpm
    have hs' : (m : ℤ) = p ^ 2 * s := by exact_mod_cast hs
    have : (k : ℤ) * (p ^ 3 + p ^ 3 * s) = k * (o' * p ^ 2 * s + p) := by
      linear_combination (o' * k : ℤ) * hs' - o' * hkn' + hB' - p * ht' + p * hkn' - k * hpm'
    exact_mod_cast this
  have key2 := Nat.eq_of_mul_eq_mul_left hkpos key
  have h3 : p ^ 2 ∣ o' * p ^ 2 * s + p := by
    rw [← key2]
    exact ⟨p + p * s, by ring⟩
  have h4 : p ^ 2 ∣ o' * p ^ 2 * s := ⟨o' * s, by ring⟩
  have h5 : p ^ 2 ∣ p := (Nat.dvd_add_right h4).mp h3
  have := Nat.le_of_dvd hp.pos h5
  have h6 : p < p ^ 2 := by nlinarith [hp.two_le]
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
