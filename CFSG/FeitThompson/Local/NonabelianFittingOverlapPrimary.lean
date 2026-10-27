module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.FittingOverlapPrimeCentralizerSmall
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.GlobalMaximalPlaneGeometry
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.PLengthOneSylowNormalizerDerivedTransfer
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.DistinctPrimeCoresCommute
import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
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
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {M X L : Subgroup G} {g : G} {p q : ℕ}

theorem commutator_pCoreIn_pCoreIn_eq_bot (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (H : Subgroup G) : ⁅pCoreIn p H, pCoreIn q H⁆ = ⊥ := by
  rw [pCoreIn_eq, pCoreIn_eq, ← Subgroup.map_commutator, commutator_pCore_pCore_eq_bot hp hq hpq,
    Subgroup.map_bot]

theorem isInternalDirectProduct_pCoreIn_pComplCoreIn (hp : p.Prime) (H : Subgroup G)
    (hnil : Group.IsNilpotent ↥H) :
    IsInternalDirectProduct H (pCoreIn p H) (pComplCoreIn p H) := by
  have := Fact.mk hp
  have := hnil
  have hinf : pCore p ↥H ⊓ pComplCore p ↥H = ⊥ := by
    rw [inf_comm]; exact inf_pComplCore_eq_bot (isPGroup_pCore hp ↥H)
  have hsub : IsInternalDirectProduct (⊤ : Subgroup ↥H) (pCore p ↥H) (pComplCore p ↥H) := by
    have := pComplCore_normal p ↥H
    refine isInternalDirectProduct_of_sup_eq (V := pComplCore p ↥H)
      (pCore_sup_pComplCore_eq_top hp ↥H) hinf ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.commute_of_normal_of_disjoint _ _ (pCore_normal p ↥H)
      (pComplCore_normal p ↥H) (disjoint_iff.2 hinf) x y hx hy).symm.eq
  have hmap := isInternalDirectProduct_map (f := H.subtype) H.subtype_injective hsub
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by ext x; simp [Subgroup.mem_map]
  rw [htop, ← pCoreIn_eq, ← pComplCoreIn_eq] at hmap
  exact hmap

theorem pComplCoreIn_le_centralizerWithin (hp : p.Prime) (H : Subgroup G)
    (hnil : Group.IsNilpotent ↥H) (hL : L ≤ pCoreIn p H) :
    pComplCoreIn p H ≤ centralizerWithin H L := by
  refine le_inf (pComplCoreIn_le p H) ?_
  have hb : ⁅pComplCoreIn p H, pCoreIn p H⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (isInternalDirectProduct_pCoreIn_pComplCoreIn hp H hnil).commutator_eq_bot
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hb).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hL))

theorem pCoreIn_le_centralizerWithin_of_ne (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (H : Subgroup G) (hL : L ≤ pCoreIn q H) : pCoreIn p H ≤ centralizerWithin H L := by
  refine le_inf (pCoreIn_le p H) ?_
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
    (commutator_pCoreIn_pCoreIn_eq_bot hp hq hpq H)).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hL))

theorem pCoreIn_le_centralizerWithin_of_le_centreIn (p : ℕ) (H : Subgroup G)
    (hL : L ≤ centreIn (pCoreIn p H)) : pCoreIn p H ≤ centralizerWithin H L := by
  refine le_inf (pCoreIn_le p H) ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hL.trans (centreIn_le_centralizer _)

theorem not_isMulCommutative_pCoreIn (hp : p.Prime) (H : Subgroup G)
    (hnil : Group.IsNilpotent ↥H) (hR : IsMulCommutative ↥(pComplCoreIn p H))
    (hH : ¬ IsMulCommutative ↥H) : ¬ IsMulCommutative ↥(pCoreIn p H) := by
  intro hP
  have := hP
  have := hR
  exact hH (isInternalDirectProduct_pCoreIn_pComplCoreIn hp H hnil).isMulCommutative

theorem isCyclic_of_isFittingOverlapSetup
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g) (hXS : X ≤ sigmaCore M) :
    IsCyclic ↥X := by
  have : Fintype G := Fintype.ofFinite G
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hcyc := (_root_.CFSG.FeitThompson.Proofs.FBG_sigma_conjugate_intersection_cyclic h₅ h₆ G hG2 M
    hsetup.isCoatom g hsetup.notMem _ rfl).1
  refine isCyclic_of_le_of_isCyclic (le_inf hXS ?_) hcyc
  have hXc : X ≤ conjSubgroup (mixedFitting M) g := hsetup.eq ▸ inf_le_right
  refine hXc.trans ?_
  rw [conjSubgroup_eq, conjSubgroup_eq]
  exact Subgroup.map_mono (mixedFitting_le M)

theorem nonabelian_fitting_overlap_primary_of_isFittingOverlapSetup
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g)
    (hnab : ¬ IsMulCommutative ↥(hallCoreIn M)) (hp : p ∈ (Nat.card ↥X).primeFactors) :
    IsCyclic ↥X ∧ IsPGroup p ↥X ∧ X ≤ pCoreIn p (hallCoreIn M) ∧
      ¬ IsMulCommutative ↥(pCoreIn p (hallCoreIn M)) ∧
      IsMulCommutative ↥(pComplCoreIn p (hallCoreIn M)) ∧
      IsInternalDirectProduct (hallCoreIn M) (pCoreIn p (hallCoreIn M))
        (pComplCoreIn p (hallCoreIn M)) ∧
      ∀ L : Subgroup G, L ≤ X → Nat.card ↥L = p → ¬ L ≤ centreIn (pCoreIn p (hallCoreIn M)) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hHnil : Group.IsNilpotent ↥(hallCoreIn M) := isNilpotent_hallCoreIn M
  obtain ⟨-, hHS, hXS⟩ := isNilpotent_sigmaCore_and_hallCoreIn_eq_and_le h₁ h₂ h₃ h₇ hG hsetup
  have hXH : X ≤ hallCoreIn M := hHS ▸ hXS
  have hprod := isInternalDirectProduct_pCoreIn_pComplCoreIn hpp (hallCoreIn M) hHnil
  have habs : ∀ (r : ℕ) (J : Subgroup G), r.Prime → J ≤ X → Nat.card ↥J = r →
      IsMulCommutative ↥(centralizerWithin (hallCoreIn M) J) := fun r J hr hJX hJc =>
    (centralizerWithin_hallCoreIn_properties_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₇ hG hsetup hr
      hJX hJc).2.1
  obtain ⟨L₀, hL₀X, hL₀card⟩ := _root_.CFSG.FeitThompson.Proofs.exists_le_natCard_eq_of_prime_dvd hpp
    (Nat.dvd_of_mem_primeFactors hp)
  have hL₀p : IsPGroup p ↥L₀ := IsPGroup.of_card (n := 1) (by simpa using hL₀card)
  have hL₀P : L₀ ≤ pCoreIn p (hallCoreIn M) :=
    le_pCoreIn_of_isPGroup_of_isNilpotent hpp (hL₀X.trans hXH) hL₀p
  have hRab : IsMulCommutative ↥(pComplCoreIn p (hallCoreIn M)) := by
    have := habs p L₀ hpp hL₀X hL₀card
    exact isMulCommutative_of_le (pComplCoreIn_le_centralizerWithin hpp (hallCoreIn M) hHnil hL₀P)
  have hPnab : ¬ IsMulCommutative ↥(pCoreIn p (hallCoreIn M)) :=
    not_isMulCommutative_pCoreIn hpp (hallCoreIn M) hHnil hRab hnab
  have hXp : IsPGroup p ↥X := by
    have hall : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card ↥X → d = p := by
      intro d hd hdvd
      by_contra hne
      obtain ⟨J, hJX, hJc⟩ := _root_.CFSG.FeitThompson.Proofs.exists_le_natCard_eq_of_prime_dvd hd hdvd
      have hJq : IsPGroup d ↥J := IsPGroup.of_card (n := 1) (by simpa using hJc)
      have hJcore : J ≤ pCoreIn d (hallCoreIn M) :=
        le_pCoreIn_of_isPGroup_of_isNilpotent hd (hJX.trans hXH) hJq
      have := habs d J hd hJX hJc
      exact hPnab (isMulCommutative_of_le
        (pCoreIn_le_centralizerWithin_of_ne hpp hd (Ne.symm hne) (hallCoreIn M) hJcore))
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hall)
  refine ⟨isCyclic_of_isFittingOverlapSetup h₅ h₆ hG hsetup hXS, hXp,
    le_pCoreIn_of_isPGroup_of_isNilpotent hpp hXH hXp, hPnab, hRab, hprod, ?_⟩
  intro L hLX hLcard hLZ
  have := habs p L hpp hLX hLcard
  exact hPnab (isMulCommutative_of_le
    (pCoreIn_le_centralizerWithin_of_le_centreIn p (hallCoreIn M) hLZ))

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson

universe u

theorem FBG_nonabelian_fitting_overlap_primary
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₅ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₆ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₇ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_nonabelian_fitting_overlap_primary.{u} :=
  fun _ _ _ hG _ _ _ hsetup hnab _ hp =>
    nonabelian_fitting_overlap_primary_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₅ h₆ h₇ hG hsetup
      hnab hp

end

end CFSG.FeitThompson.Proofs
