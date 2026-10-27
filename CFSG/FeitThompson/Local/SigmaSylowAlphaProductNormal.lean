module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.SigmaHallInDerivedSubgroup
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientSylowEnvelope
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.OddOrder.SharedSylowNormalizedByIntersection

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep09
open Subgroup Pointwise

universe u

variable {X : Type*} [Group X]

theorem not_dvd_index_of_isHallSubgroup [Finite X] {π : Set ℕ} {H : Subgroup X}
    (hH : IsHallSubgroup π H) {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π) : ¬ p ∣ H.index := fun hdvd =>
  isPiNumber_iff.1 hH.index p
    (Nat.mem_primeFactors.2 ⟨hp, hdvd, H.index_ne_zero_of_finite⟩) hpπ

theorem factorization_natCard_eq_of_not_dvd_index [Finite X] {p : ℕ}
    {H : Subgroup X} (h : ¬ p ∣ H.index) :
    (Nat.card ↥H).factorization p = (Nat.card X).factorization p := by
  have hcard : Nat.card ↥H * H.index = Nat.card X := Subgroup.card_mul_index H
  rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' H.index_ne_zero_of_finite]
  simp [Nat.factorization_eq_zero_of_not_dvd h]

theorem isNilpotent_commutator_quotient_alphaCore [Finite X] [Group.IsSolvable X]
    (hodd : Odd (Nat.card X)) (hA : alphaCore X ≤ _root_.commutator X) :
    haveI := alphaCore_normal X
    Group.IsNilpotent (↥(_root_.commutator X) ⧸ (alphaCore X).subgroupOf
      (_root_.commutator X)) := by
  have := alphaCore_normal X
  rw [isNilpotent_commutator_quotient_iff _ hA, ← map_mk'_commutator]
  exact isNilpotent_of_le_fittingRaw
    (map_mk'_commutator_le_fittingRaw_quotient_alphaCore hodd)

theorem normal_sup_sylow_alphaCore [Finite X] [Group.IsSolvable X] {p : ℕ} [Fact p.Prime]
    (hodd : Odd (Nat.card X)) (hA : alphaCore X ≤ _root_.commutator X)
    (S : Sylow p X) (hS : (S : Subgroup X) ≤ _root_.commutator X) :
    (alphaCore X ⊔ (S : Subgroup X)).Normal :=
  haveI := alphaCore_normal X
  normal_sup_sylow (alphaCore X) hA (isNilpotent_commutator_quotient_alphaCore hodd hA) S hS

theorem FTS_sigma_sylow_alpha_product_normal :
    Statements.FTS_sigma_sylow_alpha_product_normal.{u} := by
  intro G _ _ hG M hM p hp P
  have := hG.isSimpleGroup
  have := hG.isSolvable_of_ne_top M hM.1
  have hpp : p.Prime := prime_of_mem_sigmaPrimes hp
  have : Fact p.Prime := ⟨hpp⟩
  set Q : Subgroup G := (P : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype with hQdef
  have hQS : Q ≤ sigmaCore M := hQdef ▸ map_subtype_le _
  have hQM : Q ≤ M := hQS.trans (sigmaCore_le M)
  have hAM : Prep09.alphaCoreIn M ≤ M := Prep09.alphaCoreIn_le M
  have hAsub : (Prep09.alphaCoreIn M).subgroupOf M = alphaCore ↥M := by
    rw [alphaCoreIn_def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hAnormal : ((Prep09.alphaCoreIn M).subgroupOf M).Normal := hAsub ▸ alphaCore_normal ↥M
  have hMnorm : M ≤ normalizer (Prep09.alphaCoreIn M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).1 hAnormal
  refine ⟨(Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hQM.trans hMnorm)).symm, ?_⟩
  have hoddM : Odd (Nat.card ↥M) := hG.odd_natCard.of_dvd_nat M.card_subgroup_dvd_card
  have hHallS : IsHallSubgroup (sigmaPrimes M) (sigmaCore M) :=
    isHallSubgroup_sigmaCore hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM
  have hfacS : (Nat.card ↥(sigmaCore M)).factorization p = (Nat.card G).factorization p :=
    factorization_natCard_eq_of_not_dvd_index
      (not_dvd_index_of_isHallSubgroup hHallS hpp hp)
  have hfacM : (Nat.card ↥M).factorization p = (Nat.card G).factorization p :=
    factorization_eq_of_mem_sigmaPrimes hp
  have hQcard : Nat.card ↥Q = p ^ (Nat.card ↥M).factorization p := by
    rw [hQdef, Subgroup.card_map_of_injective (sigmaCore M).subtype_injective,
      P.card_eq_multiplicity, hfacS, hfacM]
  obtain ⟨T, hT⟩ := (natCard_eq_pow_factorization_iff_exists_sylow hQM).1 hQcard
  have hTcoe : (T : Subgroup ↥M) = Q.subgroupOf M := by
    rw [Subgroup.subgroupOf, ← hT,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hQcomm : Q.subgroupOf M ≤ _root_.commutator ↥M :=
    (Subgroup.subgroupOf_mono M hQS).trans
      (le_commutator_of_isHallSubgroup_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hM
        (isHallSubgroup_subgroupOf_sigmaCore hG.not_isMulCommutative hG.odd_natCard
          hG.isSolvable_of_ne_top hM))
  have hAcomm : alphaCore ↥M ≤ _root_.commutator ↥M :=
    alphaCore_le_commutator hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM
  have hnormal := normal_sup_sylow_alphaCore (X := ↥M) hoddM hAcomm T (hTcoe ▸ hQcomm)
  rw [Subgroup.subgroupOf_sup hAM hQM, hAsub]
  rwa [hTcoe] at hnormal

end

end CFSG.FeitThompson.Proofs
