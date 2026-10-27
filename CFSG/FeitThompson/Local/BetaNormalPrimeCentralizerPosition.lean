module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.BetaSubgroupNormalizerInMaximal
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Local.LargeAbelianNormalNoComplementaryPrime
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
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

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isPiSubgroup_of_natCard_eq_pow {π : Set ℕ} {s : ℕ} (hsp : s.Prime) (hs : s ∈ π)
    {X : Subgroup G} (hX : ∃ n : ℕ, Nat.card ↥X = s ^ n) : IsPiSubgroup π X := by
  obtain ⟨n, hn⟩ := hX
  refine isPiSubgroup_iff.2 fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ s ^ n := hn ▸ Nat.dvd_of_mem_primeFactors hp
  rwa [(Nat.prime_dvd_prime_iff_eq hpp hsp).1 (hpp.dvd_of_dvd_pow hdvd)]

theorem le_betaCore_of_isHallPiIn {M X : Subgroup G}
    (hHall : Prep06.IsHallPiIn (betaPrimes ↥M) (betaCore M) M)
    (hXM : X ≤ M) (hX : IsPiSubgroup (betaPrimes ↥M) X) : X ≤ betaCore M := by
  have hHall' : IsHallPiSubgroup (betaPrimes ↥M) ((betaCore M).subgroupOf M) := by
    constructor
    · refine isPiSubgroup_iff.2 fun p hp => hHall.2.1 p ?_
      rwa [natCard_subgroupOf_of_le (betaCore_le M)] at hp
    · intro p hp
      exact hHall.2.2 p (by rwa [index_subgroupOf] at hp)
  have hX' : IsPiSubgroup (betaPrimes ↥M) (X.subgroupOf M) := by
    refine isPiSubgroup_iff.2 fun p hp => isPiSubgroup_iff.1 hX p ?_
    rwa [natCard_subgroupOf_of_le hXM] at hp
  exact le_of_subgroupOf_le hXM (hHall'.le_of_isPiSubgroup hX')

section Ambient

variable [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
  (hsolv : ∀ Z : Subgroup G, Z ≠ ⊤ → Group.IsSolvable ↥Z)

include hna hodd hsolv in
theorem exists_conj_smul_ge_normalizer_of_mem_betaPrimes {M : Subgroup G} (hM : IsCoatom M)
    {s : ℕ} (hsp : s.Prime) (hs : s ∈ betaPrimes ↥M) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXcard : ∃ n : ℕ, Nat.card ↥X = s ^ n) :
    ∃ a : G, X ≤ MulAut.conj a • M ∧ normalizer (X : Set G) ≤ MulAut.conj a • M := by
  obtain ⟨n, hn⟩ := hXcard
  have hXs : IsPGroup s ↥X := IsPGroup.of_card hn
  have hsσ : s ∈ sigmaPrimes M := betaPrimes_subset_sigmaPrimes hna hodd hsolv hM hs
  obtain ⟨a, ha⟩ := exists_conj_smul_le_of_isPGroup hsσ hXs
  refine ⟨a, ha, normalizer_le_of_isPiSubgroup_betaPrimes hna hodd hsolv
    (isCoatom_conj_smul hM a) ha hX ?_⟩
  rw [betaPrimes_conj_smul]
  exact isPiSubgroup_of_natCard_eq_pow hsp hs ⟨n, hn⟩

include hna hodd hsolv in
theorem conj_smul_eq_of_ne_bot_le_betaCore {M : Subgroup G} (hM : IsCoatom M) {C : Subgroup G}
    (hC : C ≠ ⊥) (hCB : C ≤ betaCore M) {a : G} (hCa : C ≤ MulAut.conj a • M) :
    MulAut.conj a • M = M := by
  have hCM : C ≤ M := hCB.trans (betaCore_le M)
  have hCsolv : Group.IsSolvable ↥C := hsolv C fun h => hM.1 (top_le_iff.1 (h ▸ hCM))
  obtain ⟨t, ht, hY⟩ :
      ∃ t, Nat.Prime t ∧ _root_.CFSG.FeitThompson.pCoreIn t C ≠ ⊥ := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hC (eq_bot_of_forall_pCoreIn_eq_bot fun r hr => h r hr)
  set Y := _root_.CFSG.FeitThompson.pCoreIn t C with hYdef
  have hYC : Y ≤ C := pCoreIn_le t C
  have hYt : IsPGroup t ↥Y := isPGroup_pCoreIn ht C
  have hYβ : IsPiSubgroup (betaPrimes ↥M) Y := (isPiSubgroup_betaCore M).of_le (hYC.trans hCB)
  have htβ : t ∈ betaPrimes ↥M :=
    isPiSubgroup_iff.1 hYβ t (Nat.mem_primeFactors.2
      ⟨ht, prime_dvd_natCard_of_isPGroup ht hY hYt, Nat.card_pos.ne'⟩)
  have htσ : t ∈ sigmaPrimes M := betaPrimes_subset_sigmaPrimes hna hodd hsolv hM htβ
  have hNY : normalizer (Y : Set G) ≤ M :=
    normalizer_le_of_isPiSubgroup_betaPrimes hna hodd hsolv hM (hYC.trans hCM) hY hYβ
  have hY1 : Y ≤ MulAut.conj (1 : G) • M := by simpa using hYC.trans hCM
  have hYa : Y ≤ MulAut.conj a • M := hYC.trans hCa
  obtain ⟨c, hc, hconj⟩ := exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes hna hodd hsolv hM
    htσ hYt hY1 hYa
  have hcM : c ∈ M := hNY ((Subgroup.centralizer_le_normalizer _) hc)
  have hcfix : MulAut.conj c • M = M :=
    mem_normalizer_iff_conj_smul_eq.1 (Subgroup.le_normalizer hcM)
  have h1 : MulAut.conj (1 : G) • M = M := by simp
  rw [h1, hcfix] at hconj
  exact hconj.symm

end Ambient

theorem FBG_beta_normal_prime_centralizer_position
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_beta_normal_prime_centralizer_position.{u} := by
  intro G _ _ hG M hM P hPM hP hCne H hHC hCH s hs hsp X hXH hXN hX hXcard
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable
  obtain ⟨a, hXa, hNXa⟩ :=
    exists_conj_smul_ge_normalizer_of_mem_betaPrimes hna hodd hsolv hM hsp hs hX hXcard
  have hHa : H ≤ MulAut.conj a • M :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).1 hXN).trans hNXa
  have hCB : centralizerWithin (betaCore M) P ≤ betaCore M := inf_le_left
  have hMa : MulAut.conj a • M = M :=
    conj_smul_eq_of_ne_bot_le_betaCore hna hodd hsolv hM hCne hCB (hCH.trans hHa)
  have hHM : H ≤ M := hMa ▸ hHa
  refine ⟨hHM, ?_⟩
  have : Fintype G := Fintype.ofFinite G
  have hMin : IsOddOrderMinimalSimple G := ⟨hodd, hG.isSimpleGroup, hna, hsolv⟩
  obtain ⟨hHallOf, -, hSM⟩ := h₁ G hMin M hM
  have hG6 : Prep06.IsMinimalOddSimple G := ⟨hodd, hG.isSimpleGroup, hna, hsolv⟩
  exact le_betaCore_of_isHallPiIn (isHallPiIn_betaCore h₂ hG6 hM hHallOf.2 hSM)
    (hXH.trans hHM) (isPiSubgroup_of_natCard_eq_pow hsp hs hXcard)

end

end CFSG.FeitThompson.Proofs
