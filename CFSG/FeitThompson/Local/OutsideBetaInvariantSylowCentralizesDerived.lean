module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.DerivedComplementCentralizesBetaPrimeHall
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

variable {G : Type u} [Group G]

theorem isHallSubgroup_subgroupOf_of_isSylowOf [Finite G] {q : ℕ} (hq : q.Prime)
    {P X : Subgroup G} (h : CFSG.FeitThompson.Prep08.IsSylowOf q P X) :
    IsHallSubgroup ({q} : Set ℕ) (P.subgroupOf X) := by
  obtain ⟨T, rfl⟩ := h
  have : Fact q.Prime := ⟨hq⟩
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  exact isHallSubgroup_sylow T

theorem le_normalizer_of_le_centralizer {A B : Subgroup G}
    (h : B ≤ centralizer (A : Set G)) : A ≤ normalizer (B : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact h

theorem FTS_outside_beta_invariant_sylow_centralizes_derived_complement
    (h₁ : CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_outside_beta_invariant_sylow_centralizes_derived_complement.{u} := by
  intro G _ _ hG M E V q hM hEM hsd hq _hqodd hqβ hV hEV
  have : Fintype G := Fintype.ofFinite G
  have hamb : CFSG.FeitThompson.IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hHallOf, hHallG, -⟩ := h₁ G hG2 M hM
  obtain ⟨H, hHhall, hEH⟩ :=
    FTS_derived_complement_centralizes_beta_prime_hall h₁ h₂ G hamb M hM E hEM hsd
  have hqπ : q ∈ {r : ℕ | r.Prime ∧ r ∉ betaPrimes ↥M} := ⟨hq, hqβ⟩
  have hHS : H ≤ sigmaCore M := hHhall.1
  have hqindex : ¬ q ∣ (H.subgroupOf (sigmaCore M)).index := fun hd =>
    hHhall.2.notMem_of_mem_primeFactors_index q
      (Nat.mem_primeFactors.2 ⟨hq, hd, Subgroup.index_ne_zero_of_finite⟩) hqπ
  have hcardH : Nat.card ↥(H.subgroupOf (sigmaCore M)) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHS).toEquiv
  have hfact : (Nat.card ↥(sigmaCore M)).factorization q = (Nat.card ↥H).factorization q := by
    have h := Subgroup.card_mul_index (H.subgroupOf (sigmaCore M))
    rw [hcardH] at h
    rw [← h, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqindex, add_zero]
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨T⟩ : Nonempty (Sylow q ↥H) := inferInstance
  set W : Subgroup G := (T : Subgroup ↥H).map H.subtype with hW
  have hWH : W ≤ H := Subgroup.map_subtype_le _
  have hWS : W ≤ sigmaCore M := hWH.trans hHS
  have hcardW : Nat.card ↥W = q ^ (Nat.card ↥(sigmaCore M)).factorization q := by
    rw [hW, Subgroup.card_subtype, T.card_eq_multiplicity, hfact]
  have hWsylow : CFSG.FeitThompson.Prep08.IsSylowOf q W (sigmaCore M) :=
    (CFSG.FeitThompson.Prep08.isSylowOf_iff_natCard hq hWS).2 hcardW
  have hE'E : (⁅E, E⁆ : Subgroup G) ≤ E := Subgroup.commutator_le_self E
  have hEσ : ∀ r ∈ (Nat.card ↥E).primeFactors, r ∉ sigmaPrimes M := by
    rw [← index_subgroupOf_left_eq hsd]
    exact hHallOf.2.notMem_of_mem_primeFactors_index
  have hcop : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥(⁅E, E⁆ : Subgroup G)) := by
    refine Nat.coprime_of_dvd fun r hr hrS hrE => ?_
    refine hEσ r (Nat.mem_primeFactors.2
      ⟨hr, hrE.trans (Subgroup.card_dvd_of_le hE'E), Nat.card_pos.ne'⟩) ?_
    exact isPiSubgroup_iff.1 hHallG.isPiSubgroup r
      (Nat.mem_primeFactors.2 ⟨hr, hrS, Nat.card_pos.ne'⟩)
  have hsolv : Group.IsSolvable ↥(sigmaCore M ⊔ (⁅E, E⁆ : Subgroup G)) :=
    isSolvable_of_le_of_isSolvable (sup_le (sigmaCore_le M) (hE'E.trans hEM))
      (hG.isSolvable_of_ne_top M hM.1)
  have hE'S : (⁅E, E⁆ : Subgroup G) ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    (hE'E.trans hEM).trans (le_normalizer_sigmaCore M)
  have hHcE' : H ≤ centralizer ((⁅E, E⁆ : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact hEH)
  have hWcE' : W ≤ centralizer ((⁅E, E⁆ : Subgroup G) : Set G) := hWH.trans hHcE'
  obtain ⟨c, hc, hcWV⟩ :=
    exists_mem_inf_centralizer_conj_inv_smul_eq_of_le_normalizer (π := ({q} : Set ℕ))
      hsolv hE'S hcop hWS hV.le
      (isHallSubgroup_subgroupOf_of_isSylowOf hq hWsylow)
      (isHallSubgroup_subgroupOf_of_isSylowOf hq hV)
      (le_normalizer_of_le_centralizer hWcE') (hE'E.trans hEV)
  rw [Subgroup.mem_inf] at hc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hcWV]
  exact conj_inv_smul_le_centralizer hc.2 hWcE'

end

end CFSG.FeitThompson.Proofs
