module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.AlphaCore
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.QuotientFittingLiftPiCore
import CFSG.FeitThompson.Local.SigmaHallInDerivedSubgroup
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

section Solvable

variable {L : Type*} [Group L] [Finite L]

theorem elementaryAbelianPRank_fittingRaw_quotient_alphaCore_le_two [Group.IsSolvable L] {p : ℕ}
    (hp : p.Prime) : elementaryAbelianPRank p ↥(fittingRaw (L ⧸ alphaCore L)) ≤ 2 := by
  have h : ∀ A : Subgroup L, ∀ _ : A.Normal, A = piCore (alphaPrimes L) L →
      elementaryAbelianPRank p ↥(fittingRaw (L ⧸ A)) ≤ 2 := by
    intro A _ hAeq
    subst hAeq
    by_cases hpπ : p ∈ alphaPrimes L
    · exact le_trans (Nat.le_of_eq ((elementaryAbelianPRank_eq_zero_iff hp).2
        (not_dvd_natCard_fittingRaw_quotient_piCore _ L hp hpπ))) (Nat.zero_le 2)
    · obtain ⟨J, e, -⟩ := exists_subgroup_mulEquiv_fittingRaw_quotient_piCore (alphaPrimes L) L
      have h1 : elementaryAbelianPRank p ↥(fittingRaw (L ⧸ piCore (alphaPrimes L) L))
          = elementaryAbelianPRank p ↥J :=
        (elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt e).symm
      have h2 := elementaryAbelianPRank_subgroup_le (X := L) hp.one_lt J
      have h3 : elementaryAbelianPRank p L ≤ 2 := by
        by_contra hcon
        exact hpπ (mem_alphaPrimes.2 ⟨hp, by omega⟩)
      omega
  exact h _ (alphaCore_normal L) (alphaCore_eq_piCore L)

theorem isPiSubgroup_compl_fittingRaw_quotient_alphaCore (L : Type*) [Group L] [Finite L] :
    IsPiSubgroup (alphaPrimes L)ᶜ (fittingRaw (L ⧸ alphaCore L)) := by
  have h : ∀ A : Subgroup L, ∀ _ : A.Normal, A = piCore (alphaPrimes L) L →
      IsPiSubgroup (alphaPrimes L)ᶜ (fittingRaw (L ⧸ A)) := by
    intro A _ hAeq
    subst hAeq
    exact isPiSubgroup_compl_fittingRaw_quotient_piCore (alphaPrimes L) L
  exact h _ (alphaCore_normal L) (alphaCore_eq_piCore L)

theorem odd_natCard_quotient_alphaCore (hodd : Odd (Nat.card L)) :
    haveI := alphaCore_normal L
    Odd (Nat.card (L ⧸ alphaCore L)) := by
  have := alphaCore_normal L
  rw [← Subgroup.index_eq_card]
  exact hodd.of_dvd_nat (alphaCore L).index_dvd_card

theorem commutator_quotient_alphaCore_le_fittingRaw [Group.IsSolvable L]
    (hodd : Odd (Nat.card L)) :
    haveI := alphaCore_normal L
    _root_.commutator (L ⧸ alphaCore L) ≤ fittingRaw (L ⧸ alphaCore L) := by
  have := alphaCore_normal L
  exact commutator_le_fittingRaw (odd_natCard_quotient_alphaCore hodd) fun p hp =>
    elementaryAbelianPRank_fittingRaw_quotient_alphaCore_le_two hp

theorem map_mk'_commutator_le_fittingRaw_quotient_alphaCore [Group.IsSolvable L]
    (hodd : Odd (Nat.card L)) :
    haveI := alphaCore_normal L
    (_root_.commutator L).map (QuotientGroup.mk' (alphaCore L))
      ≤ fittingRaw (L ⧸ alphaCore L) := by
  have := alphaCore_normal L
  rw [map_commutator_eq, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective (alphaCore L))]
  exact commutator_quotient_alphaCore_le_fittingRaw hodd

theorem isHallSubgroup_alphaCore_of_forall_le_commutator [Group.IsSolvable L]
    (hodd : Odd (Nat.card L))
    (hcomm : ∀ J : Subgroup L, IsHallSubgroup (alphaPrimes L) J → J ≤ _root_.commutator L) :
    IsHallSubgroup (alphaPrimes L) (alphaCore L) := by
  have hAnorm := alphaCore_normal L
  obtain ⟨J, hJ⟩ := exists_isHallSubgroup (X := L) (alphaPrimes L)
  have hAJ : alphaCore L ≤ J := hJ.le_of_isPiSubgroup (isPiSubgroup_alphaCore L)
  have hmapJ : J.map (QuotientGroup.mk' (alphaCore L)) ≤ fittingRaw (L ⧸ alphaCore L) :=
    le_trans (Subgroup.map_mono (hcomm J hJ))
      (map_mk'_commutator_le_fittingRaw_quotient_alphaCore hodd)
  have h1 : IsPiNumber (alphaPrimes L) (Nat.card (J.map (QuotientGroup.mk' (alphaCore L)))) :=
    hJ.natCard.of_dvd (Subgroup.card_map_dvd J _) Nat.card_pos.ne'
  have h2 : IsPiNumber (alphaPrimes L)ᶜ (Nat.card (J.map (QuotientGroup.mk' (alphaCore L)))) :=
    isPiSubgroup_iff_isPiNumber.1
      ((isPiSubgroup_compl_fittingRaw_quotient_alphaCore L).of_le hmapJ)
  have h3 : J ≤ alphaCore L := by
    have h4 : J.map (QuotientGroup.mk' (alphaCore L)) = ⊥ :=
      Subgroup.card_eq_one.1 (h1.eq_one_of_compl h2 Nat.card_pos.ne')
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h4
  exact le_antisymm h3 hAJ ▸ hJ

end Solvable

section Local

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem not_dvd_index_of_mem_sigmaPrimes (hp : p ∈ sigmaPrimes M) : ¬ p ∣ M.index := by
  have hpp := prime_of_mem_sigmaPrimes hp
  have hkey := factorization_eq_of_mem_sigmaPrimes hp
  have hcard : Nat.card ↥M * M.index = Nat.card G := Subgroup.card_mul_index M
  intro hdvd
  have h0 : (Nat.card ↥M).factorization p + M.index.factorization p
      = (Nat.card G).factorization p := by
    rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
    simp
  rw [hkey] at h0
  have hz : M.index.factorization p = 0 := by omega
  rw [Nat.factorization_eq_zero_iff] at hz
  rcases hz with h | h | h
  · exact h hpp
  · exact h hdvd
  · exact Subgroup.index_ne_zero_of_finite h

theorem isPiNumber_compl_index_alphaPrimes [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) : IsPiNumber (alphaPrimes ↥M)ᶜ M.index :=
  isPiNumber_compl_iff.2 fun _ hq hq' => not_dvd_index_of_mem_sigmaPrimes
    (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM hq') (Nat.dvd_of_mem_primeFactors hq)

variable [IsSimpleGroup G]

theorem isHallSubgroup_alphaCore (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) :
    IsHallSubgroup (alphaPrimes ↥M) (alphaCore ↥M) :=
  haveI := hsolv M hM.1
  isHallSubgroup_alphaCore_of_forall_le_commutator
    (hodd.of_dvd_nat M.card_subgroup_dvd_card)
    fun _ hJ => le_commutator_of_isHallSubgroup_alphaPrimes hna hodd hsolv hM hJ

theorem isHallSubgroup_map_subtype_alphaCore (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) :
    IsHallSubgroup (alphaPrimes ↥M) ((alphaCore ↥M).map M.subtype) where
  natCard := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact (isHallSubgroup_alphaCore hna hodd hsolv hM).natCard
  index := by
    rw [Subgroup.index_map_subtype]
    exact (isHallSubgroup_alphaCore hna hodd hsolv hM).index.mul
      (isPiNumber_compl_index_alphaPrimes hna hodd hsolv hM)

theorem alphaCore_le_commutator (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) :
    alphaCore ↥M ≤ _root_.commutator ↥M :=
  haveI := hsolv M hM.1
  le_commutator_of_isHallSubgroup_alphaPrimes hna hodd hsolv hM
    (isHallSubgroup_alphaCore hna hodd hsolv hM)

theorem map_subtype_alphaCore_le_commutator (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) : (alphaCore ↥M).map M.subtype ≤ ⁅M, M⁆ := by
  haveI := hsolv M hM.1
  refine le_commutator_of_isHallSubgroup_alphaPrimes_subgroupOf hna hodd hsolv hM
    (Subgroup.map_subtype_le _) ?_
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact isHallSubgroup_alphaCore hna hodd hsolv hM

theorem commutator_quotient_alphaCore_le_fittingRaw_subgroup (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) :
    haveI := alphaCore_normal ↥M
    _root_.commutator (↥M ⧸ alphaCore ↥M) ≤ fittingRaw (↥M ⧸ alphaCore ↥M) :=
  haveI := hsolv M hM.1
  commutator_quotient_alphaCore_le_fittingRaw (hodd.of_dvd_nat M.card_subgroup_dvd_card)

end Local

end

end CFSG.FeitThompson
