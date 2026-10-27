module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PLengthOneSylowNormalizerDerivedTransfer
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.SigmaSylowInDerived
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

private theorem natCard_subgroupOf_eq {G : Type*} [Group G] {M P : Subgroup G} (h : P ≤ M) :
    Nat.card (P.subgroupOf M) = Nat.card P := by
  have e := Subgroup.equivMapOfInjective (P.subgroupOf M) M.subtype M.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h] at e
  exact Nat.card_congr e.toEquiv

theorem FPL_global_sylow_normalizer_derived
    (h₁ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FPL_global_sylow_normalizer_derived.{u} := by
  intro G _ _ hG p hp P hPne hPsyl
  have := Fact.mk hp
  have := hG.simple
  obtain ⟨-, hPcard⟩ := hPsyl
  rw [Subgroup.card_top] at hPcard
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  obtain ⟨M, hM, hNM⟩ := exists_isCoatom_ge_of_ne_top
    (normalizer_lt_top_of_isPGroup hG.nonabelian hp hPne hPp).ne
  have hPM : P ≤ M := Subgroup.le_normalizer.trans hNM
  have hPMcard : Nat.card P = p ^ (Nat.card M).factorization p :=
    natCard_eq_pow_factorization_of_le hp hPM hPcard
  have hPMcard' : Nat.card (P.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [natCard_subgroupOf_eq hPM, hPMcard]
  have hmap : Subgroup.map M.subtype (P.subgroupOf M) = P :=
    Subgroup.map_subgroupOf_eq_of_le hPM
  have hpdvdP : p ∣ Nat.card P := by
    rcases Nat.eq_zero_or_pos ((Nat.card G).factorization p) with h | h
    · exact absurd (Subgroup.card_eq_one.1 (by rw [hPcard, h, pow_zero])) hPne
    · exact hPcard ▸ dvd_pow_self p h.ne'
  have hpM : p ∈ sigmaPrimes M := by
    rw [mem_sigmaPrimes_iff]
    refine ⟨hp, hpdvdP.trans (Subgroup.card_dvd_of_le hPM), Sylow.ofCard _ hPMcard', ?_⟩
    rw [Sylow.coe_ofCard, hmap]
    exact hNM
  have hder : P.subgroupOf M ≤ _root_.commutator M :=
    subgroupOf_le_commutator_of_mem_sigmaPrimes hG.nonabelian hG.odd hG.solvable hM hpM hPM hPMcard
  have hlen : ¬ p ∣ (pComplPCore p M).index := by
    rw [pComplPCore_eq_comap]
    exact h₁ G ⟨hG.simple, hG.nonabelian, hG.odd, hG.solvable⟩ p hp M hM.1
  have htrans := inf_commutator_le_commutator_normalizer hPMcard' hlen
  rw [inf_eq_left.2 hder] at htrans
  have hnorm : Subgroup.normalizer ((P.subgroupOf M : Subgroup M) : Set M)
      = (Subgroup.normalizer (P : Set G)).subgroupOf M :=
    (Subgroup.subgroupOf_normalizer_eq hPM).symm
  have hfin := Subgroup.map_mono (f := M.subtype) htrans
  rwa [hmap, Subgroup.map_commutator, hnorm, Subgroup.map_subgroupOf_eq_of_le hNM] at hfin

end

end CFSG.FeitThompson.Proofs
