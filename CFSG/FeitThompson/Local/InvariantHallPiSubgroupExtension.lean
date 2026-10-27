module

public import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {X : Type*} [Group X]

theorem natCard_mul_natCard_inf_of_normal_of_sup_eq_top {K L : Subgroup X} [K.Normal]
    (h : K ⊔ L = ⊤) :
    Nat.card X * Nat.card (L ⊓ K : Subgroup X) = Nat.card K * Nat.card L := by
  have h1 := natCard_sup_mul_natCard_inf_of_le_normalizer (S := K) (T := L)
    Subgroup.le_normalizer_of_normal
  rw [h, Subgroup.card_top, inf_comm] at h1
  exact h1

theorem index_subgroupOf_inf_eq_index [Finite X] {K L : Subgroup X} [K.Normal]
    (h : K ⊔ L = ⊤) : ((L ⊓ K).subgroupOf K).index = L.index := by
  have hHK : Nat.card ((L ⊓ K).subgroupOf K) = Nat.card (L ⊓ K : Subgroup X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h2 : Nat.card (L ⊓ K : Subgroup X) * ((L ⊓ K).subgroupOf K).index = Nat.card K := by
    rw [← hHK]; exact Subgroup.card_mul_index _
  have h3 := natCard_mul_natCard_inf_of_normal_of_sup_eq_top h
  have h4 : Nat.card X = ((L ⊓ K).subgroupOf K).index * Nat.card L := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (L ⊓ K : Subgroup X))) ?_
    rw [h3, ← h2]; ring
  have h5 : Nat.card L * L.index = Nat.card X := Subgroup.card_mul_index L
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := L)) ?_
  rw [h5, h4, mul_comm]

theorem index_subgroupOf (H K : Subgroup X) : (H.subgroupOf K).index = H.relIndex K := (rfl)

theorem exists_isHallSubgroup_subgroupOf_ge_le_normalizer [Finite X] [Group.IsSolvable X]
    {K A R : Subgroup X} [K.Normal] (hKA : K ⊔ A = ⊤)
    (hcop : (Nat.card K).Coprime (Nat.card A)) (π : Set ℕ)
    (hR : R ≤ K) (hRπ : IsPiNumber π (Nat.card R)) (hAR : A ≤ normalizer (R : Set X)) :
    ∃ H : Subgroup X, H ≤ K ∧ IsHallSubgroup π (H.subgroupOf K) ∧ R ≤ H ∧
      A ≤ normalizer (H : Set X) := by
  set ρ : Set ℕ := π ∪ {p : ℕ | p ∣ Nat.card A} with hρdef
  have hπρ : π ⊆ ρ := Set.subset_union_left
  have hAρ : IsPiNumber ρ (Nat.card A) :=
    isPiNumber_iff.2 fun _ hp => Or.inr (Nat.dvd_of_mem_primeFactors hp)
  have hRA : IsPiNumber ρ (Nat.card (R ⊔ A : Subgroup X)) :=
    ((hRπ.mono hπρ).mul hAρ).of_dvd
      ⟨Nat.card (R ⊓ A : Subgroup X), (natCard_sup_mul_natCard_inf_of_le_normalizer hAR).symm⟩
      (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
  obtain ⟨L, hL, hLge⟩ := exists_isHallSubgroup_ge (π := ρ) hRA
  have hAL : A ≤ L := le_sup_right.trans hLge
  have hKL : K ⊔ L = ⊤ := top_le_iff.1 (hKA.ge.trans (sup_le_sup_left hAL K))
  have hHcard : Nat.card ((L ⊓ K).subgroupOf K) = Nat.card (L ⊓ K : Subgroup X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  refine ⟨L ⊓ K, inf_le_right, ⟨?_, ?_⟩, le_inf (le_sup_left.trans hLge) hR, ?_⟩
  ·
    rw [hHcard]
    have hρ : IsPiNumber ρ (Nat.card (L ⊓ K : Subgroup X)) :=
      hL.natCard.of_dvd (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne'
    refine isPiNumber_iff.2 fun p hp => ?_
    rcases isPiNumber_iff.1 hρ p hp with hpπ | hpA
    · exact hpπ
    · have hpK : p ∣ Nat.card K :=
        (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le inf_le_right)
      exact absurd ((Nat.Coprime.coprime_dvd_left hpK hcop).eq_one_of_dvd hpA)
        (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
  ·
    rw [index_subgroupOf_inf_eq_index hKL]
    exact hL.index.mono (Set.compl_subset_compl.2 hπρ)
  ·
    exact le_trans (le_inf (hAL.trans Subgroup.le_normalizer) Subgroup.le_normalizer_of_normal)
      Subgroup.inf_normalizer_le_normalizer_inf

theorem exists_isPiNumber_isPiNumber_relIndex_ge_le_normalizer [Finite X] [Group.IsSolvable X]
    {K A R : Subgroup X} [K.Normal] (hKA : K ⊔ A = ⊤)
    (hcop : (Nat.card K).Coprime (Nat.card A)) (π : Set ℕ)
    (hR : R ≤ K) (hRπ : IsPiSubgroup π R) (hAR : A ≤ normalizer (R : Set X)) :
    ∃ H : Subgroup X, H ≤ K ∧ IsPiNumber π (Nat.card H) ∧ IsPiNumber πᶜ (H.relIndex K) ∧
      R ≤ H ∧ A ≤ normalizer (H : Set X) := by
  obtain ⟨H, hHK, hHall, hRH, hAH⟩ := exists_isHallSubgroup_subgroupOf_ge_le_normalizer hKA hcop π
    hR (isPiSubgroup_iff_isPiNumber.1 hRπ) hAR
  refine ⟨H, hHK, ?_, ?_, hRH, hAH⟩
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv) ▸ hHall.natCard
  · rw [← index_subgroupOf]; exact hHall.index

theorem exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_mul_eq_univ [Finite X]
    [Group.IsSolvable X] {K A R : Subgroup X} [K.Normal]
    (hKA : (K : Set X) * (A : Set X) = Set.univ)
    (hcop : (Nat.card K).Coprime (Nat.card A)) (π : Set ℕ)
    (hR : R ≤ K) (hRπ : IsPiNumber π (Nat.card R)) (hAR : A ≤ normalizer (R : Set X)) :
    ∃ H : Subgroup X, H ≤ K ∧ IsHallSubgroup π (H.subgroupOf K) ∧ R ≤ H ∧
      A ≤ normalizer (H : Set X) :=
  exists_isHallSubgroup_subgroupOf_ge_le_normalizer
    ((sup_eq_top_iff_mul_eq_univ K A).2 hKA) hcop π hR hRπ hAR

end

end CFSG.FeitThompson

