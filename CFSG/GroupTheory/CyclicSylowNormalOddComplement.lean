module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem le_pPrimeCore_of_normal_coprime {p : ℕ} {N : Subgroup G} (hN : N.Normal)
    (hcop : Nat.Coprime p (Nat.card N)) : N ≤ pPrimeCore p G :=
  le_sSup ⟨hN, hcop⟩

theorem exists_normal_isComplement'_of_isCyclic_sylow_two (S : Sylow 2 G)
    (hS : IsCyclic S) : ∃ N : Subgroup G, N.Normal ∧ N.IsComplement' S := by
  by_cases heven : Even (Nat.card G)
  · have hmin : (Nat.card G).minFac = 2 :=
      (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)
    exact ⟨_, MonoidHom.normal_ker _, hS.isComplement' hmin⟩
  · have hS1 : Nat.card S = 1 := by
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      rcases k with _ | k
      · simpa using hk
      · exfalso
        have h2 : 2 ∣ Nat.card G := by
          have hdvd := Subgroup.card_subgroup_dvd_card (S : Subgroup G)
          rw [hk, pow_succ] at hdvd
          exact (Dvd.intro_left _ rfl).trans hdvd
        exact heven (even_iff_two_dvd.mpr h2)
    have hbot : (S : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp hS1
    refine ⟨⊤, inferInstance, ?_⟩
    rw [hbot]
    exact isComplement'_top_bot

theorem cyclic_sylow_normal_odd_complement (S : Sylow 2 G) (hS : IsCyclic S) :
    Nat.card (pPrimeCore 2 G) = Nat.card G / Nat.card S ∧
      (pPrimeCore 2 G : Set G) * (S : Set G) = Set.univ ∧
      pPrimeCore 2 G ⊓ (S : Subgroup G) = ⊥ ∧
      ((pPrimeCore 2 G).Normal ∧ Odd (Nat.card (pPrimeCore 2 G)) ∧
        (pPrimeCore 2 G).index = Nat.card S ∧
        ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N.index = Nat.card S →
          N = pPrimeCore 2 G) ∧
      (pPrimeCore 2 G).Characteristic := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNnormal, hNS⟩ := exists_normal_isComplement'_of_isCyclic_sylow_two S hS
  set K := pPrimeCore 2 G with hKdef
  have hcardNS : Nat.card N * Nat.card S = Nat.card G := hNS.card_mul_card
  have hNindex : N.index = Nat.card S := by
    rw [← Subgroup.card_mul_index N] at hcardNS
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardNS).symm
  have hNodd : ¬ 2 ∣ Nat.card N := by
    rw [← hNS.index_eq_card]
    exact S.not_dvd_index
  have hNle : N ≤ K :=
    le_pPrimeCore_of_normal_coprime hNnormal ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      hNodd)
  have hKcop : Nat.Coprime 2 (Nat.card K) := pPrimeCore_coprime_card (p := 2) (G := G)
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  have hKdvd : Nat.card K ∣ Nat.card N := by
    have h1 : Nat.card K ∣ Nat.card N * 2 ^ a := by
      rw [← ha, hcardNS]
      exact Subgroup.card_subgroup_dvd_card K
    exact (Nat.Coprime.pow_right a hKcop.symm).dvd_of_dvd_mul_right h1
  have hNK : N = K := Subgroup.eq_of_le_of_card_ge hNle (Nat.le_of_dvd Nat.card_pos hKdvd)
  rw [hNK] at hcardNS hNindex hNodd hNnormal hNS
  have hSpos : 0 < Nat.card S := Nat.card_pos
  refine ⟨?_, ?_, ?_, ⟨hNnormal, ?_, hNindex, ?_⟩, pPrimeCore_characteristic (p := 2) (G := G)⟩
  · rw [← hcardNS, Nat.mul_div_cancel _ hSpos]
  · exact hNS.mul_eq
  · exact disjoint_iff.mp hNS.disjoint
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hNodd)
  · intro M hM hModd hMindex
    have hMle : M ≤ K := le_pPrimeCore_of_normal_coprime hM (Nat.coprime_two_left.mpr hModd)
    refine Subgroup.eq_of_le_of_card_ge hMle (le_of_eq ?_)
    have hM' := Subgroup.card_mul_index M
    rw [hMindex, ← hcardNS] at hM'
    exact (Nat.eq_of_mul_eq_mul_right hSpos hM').symm

end CFSG
