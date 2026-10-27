module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NoncyclicSigmaNormalizer
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
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
  Pointwise

universe u

variable {G : Type u} [Group G] {p q : ℕ}

theorem exists_le_natCard_eq_of_prime_dvd [Finite G] {Y : Subgroup G} (hq : q.Prime)
    (hd : q ∣ Nat.card ↥Y) : ∃ P : Subgroup G, P ≤ Y ∧ Nat.card ↥P = q := by
  have := Fact.mk hq
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) q hd
  refine ⟨Subgroup.map Y.subtype (Subgroup.zpowers x), Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective, Nat.card_zpowers, hx]

theorem mem_sigmaPrimes_of_isPGroup_le_sigmaCore [Finite G] {M P : Subgroup G} (hq : q.Prime)
    (hP : P ≠ ⊥) (hPq : IsPGroup q ↥P) (hPS : P ≤ sigmaCore M) : q ∈ sigmaPrimes M := by
  have := Fact.mk hq
  have hd : q ∣ Nat.card ↥P := by
    rcases hPq.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hP
    · exact h
  exact (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M)) q
    (Nat.mem_primeFactors.2 ⟨hq, hd.trans (Subgroup.card_dvd_of_le hPS), Nat.card_pos.ne'⟩)

theorem isMinimalSimpleOddOrder_of [Finite G] (hG : IsOddOrderMinimalSimple G) :
    Prep08.IsMinimalSimpleOddOrder G where
  isSimpleGroup := hG.isSimpleGroup
  not_isMulCommutative := hG.not_isMulCommutative
  odd_natCard := hG.odd_natCard
  isSolvable_of_ne_top := hG.isSolvable_of_ne_top

theorem isMinimalOddSimple_of [Finite G] (hG : IsOddOrderMinimalSimple G) :
    Prep06.IsMinimalOddSimple G where
  odd := hG.odd_natCard
  simple := hG.isSimpleGroup
  nonabelian := hG.not_isMulCommutative
  solvable := hG.isSolvable_of_ne_top

theorem not_centralizer_le_of_isPGroup_le_sigmaCore_inf_conj [Finite G]
    (hG : IsOddOrderMinimalSimple G) {M : Subgroup G} (hM : IsCoatom M) {g : G} (hg : g ∉ M)
    {P : Subgroup G} (hp : p.Prime) (hPbot : P ≠ ⊥) (hPp : IsPGroup p ↥P)
    (hPX : P ≤ sigmaCore M ⊓ conjSubgroup M g) : ¬ centralizer (P : Set G) ≤ M := by
  intro hCM
  have := hG.isSimpleGroup
  have hPS : P ≤ sigmaCore M := hPX.trans inf_le_left
  have hpσ : p ∈ sigmaPrimes M := mem_sigmaPrimes_of_isPGroup_le_sigmaCore hp hPbot hPp hPS
  have hPM : P ≤ MulAut.conj (1 : G) • M := by
    simpa using hPS.trans (sigmaCore_le M)
  have hPMg : P ≤ MulAut.conj g⁻¹ • M := by
    rw [conj_smul_eq_map_conj]
    exact hPX.trans inf_le_right
  obtain ⟨c, hc, hconj⟩ := exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hM hpσ hPp hPM hPMg
  have hcM : MulAut.conj c • M = M :=
    mem_normalizer_iff_conj_smul_eq.1 (Subgroup.le_normalizer (hCM hc))
  rw [map_one, one_smul, hcM] at hconj
  exact hg (inv_mem_iff.1 (normalizer_coe_eq_of_isCoatom hG.not_isMulCommutative hM ▸
    mem_normalizer_iff_conj_smul_eq.2 hconj.symm))

theorem isCyclic_of_isPGroup_le_sigmaCore_inf_conj [Finite G]
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u}) (hG : IsOddOrderMinimalSimple G)
    {M : Subgroup G} (hM : IsCoatom M) {g : G} (hg : g ∉ M) {P : Subgroup G} (hp : p.Prime)
    (hPp : IsPGroup p ↥P) (hPX : P ≤ sigmaCore M ⊓ conjSubgroup M g) : IsCyclic ↥P := by
  by_cases hPbot : P = ⊥
  · subst hPbot; infer_instance
  by_contra hnc
  have hPS : P ≤ sigmaCore M := hPX.trans inf_le_left
  have hpσ : p ∈ sigmaPrimes M := mem_sigmaPrimes_of_isPGroup_le_sigmaCore hp hPbot hPp hPS
  have hnorm : normalizer ((P : Subgroup G) : Set G) ≤ M :=
    FTS_noncyclic_sigma_normalizer h₂ G (isMinimalSimpleOddOrder_of hG) M P p hM hpσ
      (hPS.trans (sigmaCore_le M)) hPp hnc
  exact not_centralizer_le_of_isPGroup_le_sigmaCore_inf_conj hG hM hg hp hPbot hPp hPX
    ((Subgroup.centralizer_le_normalizer _).trans hnorm)

theorem not_line_of_beta_or_le_derived [Finite G]
    (h₁ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (hG : IsOddOrderMinimalSimple G) {M : Subgroup G} (hM : IsCoatom M) {g : G} (hg : g ∉ M)
    {P : Subgroup G} (hp : p.Prime) (hcard : Nat.card ↥P = p)
    (hPX : P ≤ sigmaCore M ⊓ conjSubgroup M g)
    (hor : p ∈ betaPrimes ↥M ∨ P ≤ ⁅sigmaCore M, sigmaCore M⁆) : False := by
  have : Fintype G := Fintype.ofFinite G
  have hPp : IsPGroup p ↥P := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hPbot : P ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hcard; exact hp.one_lt.ne hcard
  have huniq := (h₁ G (isMinimalOddSimple_of hG) M P hM p hp
    ((hPX.trans inf_le_left).trans (sigmaCore_le M)) hcard hor).1
  exact not_centralizer_le_of_isPGroup_le_sigmaCore_inf_conj hG hM hg hp hPbot hPp hPX huniq.le

theorem inf_commutator_sigmaCore_eq_bot [Finite G]
    (h₁ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (hG : IsOddOrderMinimalSimple G) {M : Subgroup G} (hM : IsCoatom M) {g : G} (hg : g ∉ M) :
    (sigmaCore M ⊓ conjSubgroup M g) ⊓ (⁅sigmaCore M, sigmaCore M⁆ : Subgroup G) = ⊥ := by
  by_contra hne
  obtain ⟨r, hrp, hrd⟩ :=
    (Nat.card ↥((sigmaCore M ⊓ conjSubgroup M g) ⊓
      (⁅sigmaCore M, sigmaCore M⁆ : Subgroup G))).exists_prime_and_dvd
      (fun h => hne (Subgroup.card_eq_one.1 h))
  obtain ⟨P, hPle, hPcard⟩ := exists_le_natCard_eq_of_prime_dvd hrp hrd
  exact not_line_of_beta_or_le_derived h₁ hG hM hg hrp hPcard (hPle.trans inf_le_left)
    (Or.inr (hPle.trans inf_le_right))

theorem notMem_betaPrimes_of_mem_primeFactors [Finite G]
    (h₁ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (hG : IsOddOrderMinimalSimple G) {M : Subgroup G} (hM : IsCoatom M) {g : G} (hg : g ∉ M) :
    ∀ r ∈ (Nat.card ↥(sigmaCore M ⊓ conjSubgroup M g)).primeFactors, r ∉ betaPrimes ↥M := by
  intro r hr hbeta
  obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
  obtain ⟨P, hPle, hPcard⟩ := exists_le_natCard_eq_of_prime_dvd hrp hrd
  exact not_line_of_beta_or_le_derived h₁ hG hM hg hrp hPcard hPle (Or.inl hbeta)

theorem isCyclic_sigmaCore_inf_conj [Finite G]
    (h₁ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u}) (hG : IsOddOrderMinimalSimple G)
    {M : Subgroup G} (hM : IsCoatom M) {g : G} (hg : g ∉ M) :
    IsCyclic ↥(sigmaCore M ⊓ conjSubgroup M g) := by
  set X : Subgroup G := sigmaCore M ⊓ conjSubgroup M g with hXdef
  have hcomm : IsMulCommutative ↥X := by
    rw [← Subgroup.commutator_self_eq_bot_iff]
    refine le_bot_iff.1 ?_
    have h1 : (⁅X, X⁆ : Subgroup G) ≤ X ⊓ ⁅sigmaCore M, sigmaCore M⁆ :=
      le_inf (Subgroup.commutator_le_self X)
        (Subgroup.commutator_mono inf_le_left inf_le_left)
    exact h1.trans (le_of_eq (inf_commutator_sigmaCore_eq_bot h₁ hG hM hg))
  have hz : IsZGroup ↥X := by
    rw [isZGroup_iff]
    intro r hr Q
    have hmap : IsCyclic ↥((Q : Subgroup ↥X).map X.subtype) :=
      isCyclic_of_isPGroup_le_sigmaCore_inf_conj h₂ hG hM hg hr
        ((Q.isPGroup').map X.subtype) (hXdef ▸ Subgroup.map_subtype_le _)
    exact isCyclic_of_surjective
      ((Q : Subgroup ↥X).equivMapOfInjective X.subtype X.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hnil : Group.IsNilpotent ↥X := isNilpotent_of_isMulCommutative ↥X
  exact IsZGroup.instIsCyclicOfFiniteOfIsNilpotent

theorem FBG_sigma_conjugate_intersection_cyclic
    (h₁ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FBG_sigma_conjugate_intersection_cyclic.{u} := by
  intro G _ _ hG M hM g hg X hXeq
  subst hXeq
  exact ⟨isCyclic_sigmaCore_inf_conj h₁ h₂ hG hM hg,
    notMem_betaPrimes_of_mem_primeFactors h₁ hG hM hg,
    inf_commutator_sigmaCore_eq_bot h₁ hG hM hg⟩

end

end CFSG.FeitThompson.Proofs
