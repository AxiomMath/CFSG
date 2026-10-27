module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaPrimeDerivedNilpotent
import CFSG.FeitThompson.Local.OrderedTwoPrimeHallNilpotent
import CFSG.FeitThompson.Local.KappaNonemptyNoPrimeInOtherSigma
import CFSG.FeitThompson.Local.SharedSigmaSylowSetup
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.SigmaSylowAlphaProductNormal
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

theorem commutator_eq_bot_of_isNilpotent_of_isPGroup {H : Type*} [Group H] [Finite H]
    [Group.IsNilpotent H] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) {A B : Subgroup H}
    (hA : IsPGroup p ↥A) (hB : IsPGroup q ↥B) : ⁅A, B⁆ = ⊥ := by
  obtain ⟨S, hS⟩ := hA.exists_le_sylow
  obtain ⟨T, hT⟩ := hB.exists_le_sylow
  have hSn : (S : Subgroup H).Normal := inferInstance
  have hTn : (T : Subgroup H).Normal := inferInstance
  have hdisj : Disjoint (S : Subgroup H) (T : Subgroup H) :=
    IsPGroup.disjoint_of_ne p q hpq _ _ S.isPGroup' T.isPGroup'
  refine le_bot_iff.1 ?_
  calc ⁅A, B⁆ ≤ ⁅(S : Subgroup H), (T : Subgroup H)⁆ := Subgroup.commutator_mono hS hT
    _ ≤ (S : Subgroup H) ⊓ (T : Subgroup H) := Subgroup.commutator_le_inf _ _
    _ = ⊥ := disjoint_iff.1 hdisj

theorem FTS_beta_prime_centralizing_sylow
    (h₁ : CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_beta_prime_centralizing_sylow.{u} := by
  intro G _ _ hG M hM p q hp hq hpodd hqodd hpq hpβ hqβ X a hXM hXcard hcase
  have hpf := Fact.mk hp
  have hqf := Fact.mk hq
  have hG2 : IsOddOrderMinimalSimple G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hG8 : Prep08.IsMinimalSimpleOddOrder G := ⟨hG.simple, hG.nonabelian, hG.odd, hG.solvable⟩
  have hXq : IsPGroup q ↥X := IsPGroup.of_card hXcard
  by_cases hpS : p ∣ Nat.card ↥(sigmaCore M)
  ·
    have hpσ : p ∈ sigmaPrimes M :=
      isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
        (Nat.mem_primeFactors.2 ⟨hp, hpS, Nat.card_pos.ne'⟩)
    obtain ⟨hHallOf, hHallG, hSM'⟩ := h₁ G hG2 M hM
    set Y : Subgroup G := X ⊔ ⁅M, M⁆ with hYdef
    have hYM : Y ≤ M := sup_le hXM (Subgroup.commutator_le_self M)
    have hXY : X ≤ Y := le_sup_left
    have hSY : sigmaCore M ≤ Y := hSM'.trans le_sup_right
    have hYsolv : Group.IsSolvable ↥Y :=
      isSolvable_of_le_of_isSolvable hYM (hG.solvable M hM.1)
    have hXpi : IsPiSubgroup ({p, q} : Set ℕ) X := by
      refine isPiSubgroup_iff.2 fun r hr => ?_
      rw [hXcard] at hr
      obtain ⟨hr1, hr2, -⟩ := Nat.mem_primeFactors.1 hr
      have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr1 hq).1 (hr1.dvd_of_dvd_pow hr2)
      simp [hrq]
    obtain ⟨W, hWHall, hXW⟩ := exists_isHallPiSubgroupOf_ge hYsolv hXY hXpi
    have hWY : W ≤ Y := hWHall.1
    have hWprimes : ∀ r ∈ (Nat.card ↥W).primeFactors, r = p ∨ r = q := by
      intro r hr
      have hcard : Nat.card ↥(W.subgroupOf Y) = Nat.card ↥W :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv
      simpa using isPiSubgroup_iff.1 hWHall.2.isPiSubgroup r (by rwa [hcard])
    have hnilW : Group.IsNilpotent ↥W := by
      rcases hcase with hXM' | hplt
      · have hYeq : Y = (⁅M, M⁆ : Subgroup G) := by rw [hYdef, sup_eq_right.2 hXM']
        refine FTS_beta_prime_derived_nilpotent h₁ h₂ G hG M hM W (hWY.trans hYeq.le) ?_
        intro r hr
        rcases hWprimes r hr with rfl | rfl
        · exact hpβ
        · exact hqβ
      · exact FTS_ordered_two_prime_hall_nilpotent h₁ h₂ G hG8 M X Y W p q hM hp hq hpodd hqodd
          hplt hpβ hqβ hXM hXq rfl hXW hWY ⟨hWHall.1, hWHall.2⟩
    have := hnilW
    obtain ⟨S⟩ : Nonempty (Sylow p ↥W) := inferInstance
    refine ⟨(S : Subgroup ↥W).map W.subtype, ⟨?_, ?_⟩, ?_⟩
    ·
      have hPM : (S : Subgroup ↥W).map W.subtype ≤ M :=
        (Subgroup.map_subtype_le _).trans (hWY.trans hYM)
      refine le_sigmaCore_of_isPiSubgroup hHallOf hPM (isPiSubgroup_iff.2 fun r hr => ?_)
      obtain ⟨k, hk⟩ := (S.isPGroup'.map W.subtype).exists_card_eq
      rw [hk] at hr
      obtain ⟨hr1, hr2, -⟩ := Nat.mem_primeFactors.1 hr
      rwa [(Nat.prime_dvd_prime_iff_eq hr1 hp).1 (hr1.dvd_of_dvd_pow hr2)]
    ·
      have hidx : ¬ p ∣ (sigmaCore M).index := fun hdvd =>
        hHallG.notMem_of_mem_primeFactors_index p
          (Nat.mem_primeFactors.2 ⟨hp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpσ
      have hfS : (Nat.card ↥(sigmaCore M)).factorization p = (Nat.card G).factorization p :=
        factorization_natCard_eq_of_not_dvd_index hidx
      have hfY : (Nat.card ↥Y).factorization p = (Nat.card G).factorization p := by
        refine le_antisymm (Nat.factorization_le_factorization_of_dvd_right
          (Subgroup.card_subgroup_dvd_card Y) Nat.card_pos.ne' Nat.card_pos.ne') ?_
        rw [← hfS]
        exact Nat.factorization_le_factorization_of_dvd_right
          (Subgroup.card_dvd_of_le hSY) Nat.card_pos.ne' Nat.card_pos.ne'
      have hfW : (Nat.card ↥W).factorization p = (Nat.card ↥Y).factorization p :=
        factorization_natCard_eq_of_isHallPiSubgroupOf hWHall hp (by simp)
      rw [Subgroup.card_subtype, S.card_eq_multiplicity, hfW, hfY, hfS]
    ·
      have hcomm : ⁅X.subgroupOf W, (S : Subgroup ↥W)⁆ = ⊥ :=
        commutator_eq_bot_of_isNilpotent_of_isPGroup hpq.symm
          (hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXW).symm) S.isPGroup'
      have h := congrArg (Subgroup.map W.subtype) hcomm
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXW, Subgroup.map_bot] at h
  ·
    refine ⟨⊥, ⟨bot_le, ?_⟩, Subgroup.commutator_bot_right X⟩
    rw [Subgroup.card_bot, Nat.factorization_eq_zero_of_not_dvd hpS, pow_zero]

end

end CFSG.FeitThompson.Proofs
