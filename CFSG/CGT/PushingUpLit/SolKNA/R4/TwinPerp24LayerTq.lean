module

public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Balance.FuzzyAdjAxis

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Sylow

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_oddCore_mul_of_sylow {K P : Subgroup Y}
    (hq : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) (hP : IsSylow2In P K) {x : Y} (hx : x ∈ K) :
    ∃ o ∈ oddCoreIn K, ∃ p ∈ P, o * p = x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hq
  have hAi : (classicalInvolutionOddCore ↥K).index = 2 ^ b := by
    rw [Subgroup.index_eq_card]
    exact hb
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hQ : IsSylow2In ((Q : Subgroup ↥K).map K.subtype) K := isSylow2In_map_sylow K Q
  have hPQ : Nat.card P = Nat.card ((Q : Subgroup ↥K).map K.subtype) := hP.natCard_eq hQ
  have hQc : Nat.card ((Q : Subgroup ↥K).map K.subtype) = Nat.card (Q : Subgroup ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hPc : Nat.card ↥(P.subgroupOf K) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hidx : (P.subgroupOf K).index = (Q : Subgroup ↥K).index := by
    have h1 : (P.subgroupOf K).index * Nat.card P = Nat.card ↥K := by
      rw [← hPc]
      exact Subgroup.index_mul_card (P.subgroupOf K)
    have h2 : (Q : Subgroup ↥K).index * Nat.card P = Nat.card ↥K := by
      rw [hPQ, hQc]
      exact Subgroup.index_mul_card (Q : Subgroup ↥K)
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hBi : ¬ 2 ∣ (P.subgroupOf K).index := by
    rw [hidx]
    exact Q.not_dvd_index
  have htop : classicalInvolutionOddCore ↥K ⊔ P.subgroupOf K = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have h1 : (classicalInvolutionOddCore ↥K ⊔ P.subgroupOf K).index ∣
        (classicalInvolutionOddCore ↥K).index := Subgroup.index_dvd_of_le le_sup_left
    have h2 : (classicalInvolutionOddCore ↥K ⊔ P.subgroupOf K).index ∣ (P.subgroupOf K).index :=
      Subgroup.index_dvd_of_le le_sup_right
    rw [hAi] at h1
    have hcop : Nat.Coprime (2 ^ b) (P.subgroupOf K).index :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hBi)
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hmem : (⟨x, hx⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K ⊔ P.subgroupOf K := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, p, hp, hap⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨(a : Y), Subgroup.mem_map_of_mem K.subtype ha, (p : Y), Subgroup.mem_subgroupOf.mp hp, ?_⟩
  have h := congrArg Subtype.val hap
  simpa using h

theorem mem_trivialOnQuot_of_centralizes {K P : Subgroup Y} {c : Y}
    (hq : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) (hP : IsSylow2In P K)
    (hcN : c ∈ Subgroup.normalizer (K : Set Y)) (hPc : ∀ x ∈ P, c * x = x * c) :
    c ∈ CFSG.ClassicalInvolution.Balance.Bootstrap.trivialOnQuot K := by
  refine ⟨hcN, fun x hx => ?_⟩
  obtain ⟨o, ho, p, hp, rfl⟩ := exists_oddCore_mul_of_sylow hq hP hx
  have hco : c * o * c⁻¹ ∈ oddCoreIn K := by
    have hN : c ∈ Subgroup.normalizer (oddCoreOf K : Set Y) :=
      mem_normalizer_oddCore_of_mem_normalizer hcN
    exact (Subgroup.mem_normalizer_iff.mp hN o).mp ho
  have hpc : c * p * c⁻¹ = p := by
    rw [hPc p hp, mul_inv_cancel_right]
  have e : ⁅c, o * p⁆ = (c * o * c⁻¹) * o⁻¹ := by
    rw [commutatorElement_def]
    calc c * (o * p) * c⁻¹ * (o * p)⁻¹ = (c * o * c⁻¹) * (c * p * c⁻¹) * p⁻¹ * o⁻¹ := by group
      _ = (c * o * c⁻¹) * p * p⁻¹ * o⁻¹ := by rw [hpc]
      _ = (c * o * c⁻¹) * o⁻¹ := by group
  rw [e]
  exact (oddCoreIn K).mul_mem hco ((oddCoreIn K).inv_mem ho)

theorem not_mem_oddCoreIn_of_orderOf_two {K : Subgroup Y} {t : Y} (ht2 : orderOf t = 2) :
    t ∉ oddCoreIn K := by
  intro ht
  have hodd : Odd (Nat.card ↥(oddCoreIn K)) := by
    unfold oddCoreIn
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card K
  have hdvd : orderOf t ∣ Nat.card ↥(oddCoreIn K) := Subgroup.orderOf_dvd_natCard (oddCoreIn K) ht
  rw [ht2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end Sylow

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
