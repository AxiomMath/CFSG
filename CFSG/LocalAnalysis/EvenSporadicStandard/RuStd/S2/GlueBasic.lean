module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

theorem exists_lift {X : Type*} [Group X] {O : Subgroup X} {t c : X}
    (ht : t * t = 1) (hodd : ∀ n ∈ O, Odd (orderOf n)) (hn : c * t * c⁻¹ * t⁻¹ ∈ O) :
    ∃ s ∈ O, s⁻¹ * c ∈ centralizer ({t} : Set X) := by
  set n := c * t * c⁻¹ * t⁻¹ with hn_def
  have hct : c * t * c⁻¹ = n * t := by simp [n]
  have h1 : (n * t) * (n * t) = 1 := by
    rw [← hct]
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h2 : t * n * t⁻¹ = n⁻¹ := by
    rw [ht']
    have h : n * (t * n * t) = 1 := by
      calc n * (t * n * t) = (n * t) * (n * t) := by group
        _ = 1 := h1
    exact eq_inv_of_mul_eq_one_right h
  obtain ⟨m, hm⟩ := hodd n hn
  have hnm : n ^ (2 * m + 1) = 1 := by
    rw [← hm]; exact pow_orderOf_eq_one n
  have hnpow : n ^ (m + 1) * n ^ (m + 1) = n := by
    rw [← pow_add]
    have : m + 1 + (m + 1) = (2 * m + 1) + 1 := by ring
    rw [this, pow_succ, hnm, one_mul]
  refine ⟨n ^ (m + 1), O.pow_mem hn _, ?_⟩
  rw [mem_centralizer_singleton_iff]
  have h3 : t * n ^ (m + 1) * t⁻¹ = (n⁻¹) ^ (m + 1) := by
    rw [← h2, conj_pow]
  have h4 : n ^ (m + 1) * t * (n ^ (m + 1))⁻¹ = n * t := by
    calc n ^ (m + 1) * t * (n ^ (m + 1))⁻¹
        = n ^ (m + 1) * (t * (n ^ (m + 1))⁻¹ * t⁻¹) * t := by group
      _ = n ^ (m + 1) * (t * n ^ (m + 1) * t⁻¹)⁻¹ * t := by rw [conj_inv]
      _ = n * t := by rw [h3, inv_pow, inv_inv, hnpow]
  calc (n ^ (m + 1))⁻¹ * c * t = (n ^ (m + 1))⁻¹ * (c * t * c⁻¹) * c := by group
    _ = (n ^ (m + 1))⁻¹ * (n ^ (m + 1) * t * (n ^ (m + 1))⁻¹) * c := by rw [hct, h4]
    _ = t * ((n ^ (m + 1))⁻¹ * c) := by group

theorem card_map_mk_mul_card_inf {X : Type*} [Group X] (N H : Subgroup X) [N.Normal] :
    Nat.card (H.map (QuotientGroup.mk' N)) * Nat.card ↥(N ⊓ H) = Nat.card H := by
  have h1 := Subgroup.relIndex_ker (K := H) (QuotientGroup.mk' N)
  have h2 := Subgroup.relIndex_mul_card (H := (QuotientGroup.mk' N).ker) (K := H)
  rw [QuotientGroup.ker_mk'] at h1 h2
  rw [← h1]
  exact h2

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem le_oddCore {X : Type*} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ CFSG.oddCore X :=
  le_sSup ⟨hN, hodd⟩

theorem odd_orderOf_of_mem_oddCore {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ CFSG.oddCore X) : Odd (orderOf x) :=
  Odd.of_dvd_nat (odd_card_oddCore X) (Subgroup.orderOf_dvd_natCard _ hx)

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
