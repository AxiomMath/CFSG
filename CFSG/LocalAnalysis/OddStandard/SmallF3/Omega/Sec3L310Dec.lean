module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem exists_involution_decomposition [Finite G] {L : Subgroup G}
    (hΩ : LieModel (↥L ⧸ oddCore ↥L) .POmegaPlus 4 3 1) {s a c : G} (ha : a ∈ L)
    (hc : c ∈ centralizer (L : Set G)) (hs : s = a * c) (hs2 : s * s = 1) :
    ∃ a' c' : G, a' ∈ L ∧ c' ∈ centralizer (L : Set G) ∧ a' * a' = 1 ∧ c' * c' = 1 ∧
      s = a' * c' := by
  have hac : Commute a c := (Subgroup.mem_centralizer_iff.mp hc) a ha
  have hs2' : (a * c) * (a * c) = 1 := by rw [← hs]; exact hs2
  have hp : a ^ 2 * c ^ 2 = 1 := by
    rw [← hac.mul_pow 2, pow_two]
    exact hs2'
  have hc2 : c ^ 2 = (a ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hp
  have ha2c : a ^ 2 ∈ centralizer (L : Set G) := by
    have h1 : c ^ 2 ∈ centralizer (L : Set G) := (centralizer (L : Set G)).pow_mem hc 2
    rw [hc2] at h1
    simpa using (centralizer (L : Set G)).inv_mem h1
  have ha2L : a ^ 2 ∈ L := L.pow_mem ha 2
  let N := Nat.card (CFSG.oddCore ↥L)
  have hNodd : Odd N := odd_card_oddCore' ↥L
  have hcenter : (⟨a ^ 2, ha2L⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : G) * a ^ 2 = a ^ 2 * (y : G)
    exact (Subgroup.mem_centralizer_iff.mp ha2c) (y : G) y.2
  have hodd : (⟨a ^ 2, ha2L⟩ : ↥L) ∈ oddCore ↥L :=
    center_le_oddCore_of_pOmegaPlus hΩ hcenter
  have hpow : (⟨a ^ 2, ha2L⟩ : ↥L) ^ N = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp ((oddCore ↥L).orderOf_dvd_natCard hodd)
  have ha2N : (a ^ 2) ^ N = 1 := by
    have h := congrArg (fun x : ↥L => (x : G)) hpow
    simpa using h
  have hc2N : (c ^ 2) ^ N = 1 := by
    rw [hc2, inv_pow, ha2N, inv_one]
  have hs2sq : s ^ 2 = 1 := by rw [pow_two]; exact hs2
  obtain ⟨k, hk⟩ := hNodd
  have hsN : s ^ N = s := by
    rw [hk, pow_add, pow_mul, hs2sq, one_pow, one_mul, pow_one]
  have ha'2 : a ^ N * a ^ N = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    exact ha2N
  have hc'2 : c ^ N * c ^ N = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    exact hc2N
  have hsc : s = a ^ N * c ^ N := by
    rw [← hsN, hs, hac.mul_pow N]
  exact ⟨a ^ N, c ^ N, L.pow_mem ha N, (centralizer (L : Set G)).pow_mem hc N, ha'2, hc'2,
    hsc⟩

end CFSG.OddStandard.SmallF3.Omega
