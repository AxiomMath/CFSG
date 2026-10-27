module

public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.PLengthOneSylowNormalizerDerivedTransfer
import CFSG.FeitThompson.Local.QuotientFittingLiftPiCore
import CFSG.FeitThompson.Local.OddAutPrimesNarrowGroup
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.FiniteHomImageOrder
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p q : ℕ} {X : Type*} [Group X] [Finite X]

theorem eq_bot_of_normal_of_not_dvd_natCard_quotient_pComplCore (hp : p.Prime)
    {N : Subgroup (X ⧸ pComplCore p X)} (hN : N.Normal) (hpN : ¬ p ∣ Nat.card N) : N = ⊥ := by
  have hTn : (N.comap (QuotientGroup.mk' (pComplCore p X))).Normal := hN.comap _
  have hcard : Nat.card (N.comap (QuotientGroup.mk' (pComplCore p X)))
      = Nat.card (pComplCore p X) * Nat.card N := natCard_comap_mk' _ N
  have hTp : ¬ p ∣ Nat.card (N.comap (QuotientGroup.mk' (pComplCore p X))) := by
    rw [hcard]
    exact fun h => (hp.dvd_mul.1 h).elim (not_dvd_natCard_pComplCore hp X) hpN
  have hTK : N.comap (QuotientGroup.mk' (pComplCore p X)) ≤ pComplCore p X :=
    le_pComplCore hTn fun hmem => hTp (Nat.dvd_of_mem_primeFactors hmem)
  have hNmap : N = (N.comap (QuotientGroup.mk' (pComplCore p X))).map
      (QuotientGroup.mk' (pComplCore p X)) :=
    (Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (pComplCore p X)) N).symm
  refine le_bot_iff.1 ?_
  rw [hNmap]
  calc (N.comap (QuotientGroup.mk' (pComplCore p X))).map (QuotientGroup.mk' (pComplCore p X))
      ≤ (pComplCore p X).map (QuotientGroup.mk' (pComplCore p X)) := Subgroup.map_mono hTK
    _ = ⊥ := QuotientGroup.map_mk'_self _

theorem fittingRaw_quotient_pComplCore (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    fittingRaw (X ⧸ pComplCore p X) = pCore p (X ⧸ pComplCore p X) := by
  refine le_antisymm (fittingRaw_le fun N hN hN' => ?_) (pCore_le_fittingRaw hp)
  obtain ⟨r, hr, hNr⟩ := isPrimePowerOrder_iff_isPGroup.1 hN'
  by_cases hrp : r = p
  · subst hrp
    exact le_pCore hp hN hNr
  · have := Fact.mk hr
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hNr
    have hpN : ¬ p ∣ Nat.card N := by
      rw [hn]
      exact fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h)).symm
    rw [eq_bot_of_normal_of_not_dvd_natCard_quotient_pComplCore hp hN hpN]
    exact bot_le

theorem centralizer_pCore_quotient_pComplCore_le (hp : p.Prime) (X : Type*) [Group X] [Finite X]
    [Group.IsSolvable X] :
    centralizer ((pCore p (X ⧸ pComplCore p X) : Subgroup (X ⧸ pComplCore p X)) :
        Set (X ⧸ pComplCore p X)) ≤ pCore p (X ⧸ pComplCore p X) := by
  rw [← fittingRaw_quotient_pComplCore hp X]
  exact centralizer_fittingRaw_le_fittingRaw _

section Main

variable {P : Subgroup X} [Fact p.Prime]

theorem pCore_quotient_pComplCore_eq_map_mk'
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hSyl : Nat.card (pCore p (X ⧸ pComplCore p X))
      = p ^ (Nat.card (X ⧸ pComplCore p X)).factorization p) :
    pCore p (X ⧸ pComplCore p X) = P.map (QuotientGroup.mk' (pComplCore p X)) := by
  have hp : p.Prime := Fact.out
  have hT : ¬ p ∣ (pComplPCore p X).index := by
    rw [index_pComplPCore]
    exact not_dvd_index_of_natCard_eq_pow_factorization hp hSyl
  have h := map_mk'_pComplPCore p X
  rw [pComplPCore_eq_pComplCore_sup hP hT, Subgroup.map_sup, QuotientGroup.map_mk'_self,
    bot_sup_eq] at h
  exact h.symm

theorem isPNarrow_pCore_quotient_pComplCore
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) (hnarrow : IsPNarrow p ↥P)
    (hSyl : Nat.card (pCore p (X ⧸ pComplCore p X))
      = p ^ (Nat.card (X ⧸ pComplCore p X)).factorization p) :
    IsPNarrow p ↥(pCore p (X ⧸ pComplCore p X)) := by
  have hp : p.Prime := Fact.out
  rw [pCore_quotient_pComplCore_eq_map_mk' hP hSyl]
  exact (isPNarrow_congr hp.one_lt
    (mulEquivMapMk'OfDisjoint (inf_pComplCore_eq_bot (IsPGroup.of_card hP)))).1 hnarrow

theorem prime_le_of_dvd_natCard_quotient_pComplCore (hodd : Odd p) (hX : Odd (Nat.card X))
    [Group.IsSolvable X] (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hnarrow : IsPNarrow p ↥P)
    (hSyl : Nat.card (pCore p (X ⧸ pComplCore p X))
      = p ^ (Nat.card (X ⧸ pComplCore p X)).factorization p)
    (hq : q.Prime) (hqY : q ∣ Nat.card (X ⧸ pComplCore p X)) : q ≤ p := by
  have hp : p.Prime := Fact.out
  rcases eq_or_ne q p with rfl | hqp
  · exact le_rfl
  refine le_of_lt ?_
  set Y := X ⧸ pComplCore p X
  set Pbar := pCore p Y
  set φ : Y →* MulAut ↥Pbar := MulAut.conjNormal with hφ
  have hkerle : φ.ker ≤ Pbar := by
    rw [hφ, ker_conjNormal Pbar]
    exact centralizer_pCore_quotient_pComplCore_le hp X
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_pCore hp Y)
  have hmul : Nat.card φ.range * Nat.card φ.ker = Nat.card Y :=
    natCard_range_mul_natCard_ker φ
  have hqA : q ∣ Nat.card φ.range := by
    rcases hq.dvd_mul.1 (hmul ▸ hqY) with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1
        (hq.dvd_of_dvd_pow (h.trans (hn ▸ Subgroup.card_dvd_of_le hkerle)))) hqp
  have hAodd : Odd (Nat.card φ.range) :=
    (odd_natCard_quotient _ hX).of_dvd_nat ⟨Nat.card φ.ker, hmul.symm⟩
  exact prime_lt_of_dvd_natCard_of_odd_aut_of_isPNarrow hp hodd (isPGroup_pCore hp Y)
    (isPNarrow_pCore_quotient_pComplCore hP hnarrow hSyl) hAodd hq hqp hqA

theorem prime_le_of_dvd_natCard_quotient_pComplCore_of_sylow (hodd : Odd p)
    (hX : Odd (Nat.card X)) [Group.IsSolvable X] (P : Sylow p X)
    (hnarrow : IsPNarrow p ↥(P : Subgroup X)) (Q : Sylow p (X ⧸ pComplCore p X))
    (hQ : (Q : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X))
    (hq : q.Prime) (hqY : q ∣ Nat.card (X ⧸ pComplCore p X)) : q ≤ p :=
  prime_le_of_dvd_natCard_quotient_pComplCore hodd hX P.card_eq_multiplicity hnarrow
    (hQ ▸ Q.card_eq_multiplicity) hq hqY

theorem forall_mem_primeFactors_natCard_quotient_pComplCore_le (hodd : Odd p)
    (hX : Odd (Nat.card X)) [Group.IsSolvable X] (P : Sylow p X)
    (hnarrow : IsPNarrow p ↥(P : Subgroup X)) (Q : Sylow p (X ⧸ pComplCore p X))
    (hQ : (Q : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X)) :
    ∀ q ∈ (Nat.card (X ⧸ pComplCore p X)).primeFactors, q ≤ p := fun _ hmem =>
  prime_le_of_dvd_natCard_quotient_pComplCore_of_sylow hodd hX P hnarrow Q hQ
    (Nat.prime_of_mem_primeFactors hmem) (Nat.dvd_of_mem_primeFactors hmem)

end Main

end

end CFSG.FeitThompson
