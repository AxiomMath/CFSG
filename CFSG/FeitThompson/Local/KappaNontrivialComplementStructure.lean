module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaResidualFixedSpaceAndPrimeOrder
import CFSG.FeitThompson.Local.KappaResidualBetaEquality
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
import CFSG.FeitThompson.Local.NormalBetaSylowControlsFittingPrimes
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Representations.TINormalCentralSectionGeometry
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

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
open Pointwise

universe u

variable {G : Type*} [Group G] {p q : ℕ} {M : Subgroup G}

theorem exists_normal_sylow_of_isNilpotent_sigmaCore [Finite G]
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M)
    (hnil : Group.IsNilpotent ↥(sigmaCore M)) (hq : q ∈ sigmaPrimes M) :
    ∃ Q : Subgroup G, Q ≤ M ∧ (Q.subgroupOf M).Normal ∧
      Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := by
  have hqp := prime_of_mem_sigmaPrimes hq
  have : Fact q.Prime := ⟨hqp⟩
  let T : Sylow q ↥(sigmaCore M) := default
  have hchar : (T : Subgroup ↥(sigmaCore M)).Characteristic :=
    sylow_characteristic_of_isNilpotent T
  refine ⟨Subgroup.map (sigmaCore M).subtype (T : Subgroup ↥(sigmaCore M)), ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le _).trans (sigmaCore_le M)
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      ((Subgroup.map_subtype_le _).trans (sigmaCore_le M))]
    exact le_normalizer_map_subtype_of_characteristic _ (le_normalizer_sigmaCore M)
  · rw [Subgroup.card_subtype, T.card_eq_multiplicity,
      factorization_natCard_eq_of_isHallPiSubgroup_subgroupOf hqp hHall.1 hHall.2 hq]

theorem sigmaCore_le_map_fittingRaw [Finite G] (hnil : Group.IsNilpotent ↥(sigmaCore M)) :
    sigmaCore M ≤ (fittingRaw ↥M).map M.subtype :=
  le_map_fittingRaw_of_le_normalizer (sigmaCore_le M) (le_normalizer_sigmaCore M) hnil

theorem centralizer_le_of_le_sigmaCore_of_natCard_eq_prime [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M)
    (hnil : Group.IsNilpotent ↥(sigmaCore M)) (hbeta : sigmaPrimes M = betaPrimes ↥M)
    (hSbot : sigmaCore M ≠ ⊥) {P : Subgroup G} (hp : p.Prime) (hPS : P ≤ sigmaCore M)
    (hPcard : Nat.card ↥P = p) : centralizer (P : Set G) ≤ M := by
  obtain ⟨r, hrmem⟩ := Nat.nonempty_primeFactors.2
    (lt_of_le_of_ne Nat.card_pos (Ne.symm fun h => hSbot (Subgroup.card_eq_one.1 h)))
  have hrσ : r ∈ sigmaPrimes M := isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) r hrmem
  obtain ⟨Q, hQM, hQnormal, hQcard⟩ :=
    exists_normal_sylow_of_isNilpotent_sigmaCore hHall hnil hrσ
  exact centralizer_le_of_natCard_eq_prime_of_le_fitting hna hodd hsolv hM (hbeta ▸ hrσ) hQM
    hQnormal hQcard hp (hPS.trans (sigmaCore_le_map_fittingRaw hnil)) hPcard

theorem normalizer_sharp_sigmaCore_eq [Finite G] [IsSimpleGroup G] (hM : IsCoatom M)
    (hSbot : sigmaCore M ≠ ⊥) : normalizer (sharp (sigmaCore M)) = M := by
  have hsharp : sharp (sigmaCore M) = (sigmaCore M : Set G) \ {1} := rfl
  rw [hsharp, normalizer_sdiff_singleton_one]
  exact normalizer_eq_of_isCoatom hM hSbot (sigmaCore_le M) (le_normalizer_sigmaCore M)

theorem inter_conjSet_sharp_sigmaCore_eq_empty [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hcent : ∀ (r : ℕ) (P : Subgroup G), r.Prime → P ≤ sigmaCore M → Nat.card ↥P = r →
      centralizer (P : Set G) ≤ M)
    {g : G} (hg : g ∉ M) :
    sharp (sigmaCore M) ∩ conjSet (sharp (sigmaCore M)) g = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨hxS, hx1⟩, y, ⟨hyS, -⟩, rfl⟩
  set S : Subgroup G := sigmaCore M with hSdef
  set D : Subgroup G := S ⊓ MulAut.conj g⁻¹ • S with hDdef
  have hmemD : g⁻¹ * y * g ∈ D := by
    refine ⟨hxS, ?_⟩
    rw [conj_smul_eq_map_conj]
    exact ⟨y, hyS, by simp⟩
  have hne1 : g⁻¹ * y * g ≠ 1 := fun h => hx1 (by simp [h])
  have hDbot : D ≠ ⊥ := fun h => hne1 (Subgroup.mem_bot.1 (h ▸ hmemD))
  have hDlt : 1 < Nat.card ↥D :=
    lt_of_le_of_ne Nat.card_pos (Ne.symm fun h => hDbot (Subgroup.card_eq_one.1 h))
  obtain ⟨r, hrmem⟩ := Nat.nonempty_primeFactors.2 hDlt
  have hr : r.Prime := Nat.prime_of_mem_primeFactors hrmem
  obtain ⟨w, hwD, hwo⟩ := exists_mem_orderOf_eq_of_dvd hr (Nat.dvd_of_mem_primeFactors hrmem)
  set P : Subgroup G := zpowers w with hPdef
  have hPcard : Nat.card ↥P = r := by rw [hPdef, Nat.card_zpowers, hwo]
  have hPp : IsPGroup r ↥P := IsPGroup.of_card (n := 1) (by simpa using hPcard)
  have hPS : P ≤ S := zpowers_le.2 hwD.1
  have hPg : P ≤ MulAut.conj g⁻¹ • S := zpowers_le.2 hwD.2
  have hrσ : r ∈ sigmaPrimes M := by
    refine isPiSubgroup_iff.1 ((isPiSubgroup_sigmaCore M).of_le hPS) r ?_
    exact Nat.mem_primeFactors.2 ⟨hr, hPcard ▸ dvd_rfl, by rw [hPcard]; exact hr.pos.ne'⟩
  have hCM : centralizer (P : Set G) ≤ M := hcent r P hr hPS hPcard
  have hPM : P ≤ MulAut.conj (1 : G) • M := by
    simpa using hPS.trans (sigmaCore_le M)
  have hPMg : P ≤ MulAut.conj g⁻¹ • M := by
    refine hPg.trans ?_
    rw [conj_smul_eq_map_conj, conj_smul_eq_map_conj]
    exact Subgroup.map_mono (sigmaCore_le M)
  obtain ⟨c, hc, hconj⟩ := exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes hna hodd hsolv hM
    hrσ hPp hPM hPMg
  have hcM : c ∈ M := hCM hc
  have hcfix : MulAut.conj c • M = M := mem_normalizer_iff_conj_smul_eq.1 (M.le_normalizer hcM)
  have hgM : MulAut.conj g⁻¹ • M = M := by
    rw [← hconj]
    simpa using hcfix
  refine hg ?_
  have hginv : g⁻¹ ∈ normalizer (M : Set G) := mem_normalizer_iff_conj_smul_eq.2 hgM
  have hg' : g ∈ normalizer (M : Set G) := by
    simpa using (normalizer (M : Set G)).inv_mem hginv
  rwa [normalizer_coe_eq_of_isCoatom hna hM] at hg'

theorem FBG_kappa_nontrivial_complement_structure
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₅ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_kappa_nontrivial_complement_structure.{u} := by
  intro G _ _ hG M K U hsetup
  have : Fintype G := Fintype.ofFinite G
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hHallOf, -, -⟩ := h₁ G hG02 M hsetup.isCoatom
  obtain ⟨hKprime, hnil, -⟩ :=
    FBG_kappa_residual_fixed_space_and_prime_order h₁ h₂ h₃ h₄ G hG M K U hsetup
  have hbeta : sigmaPrimes M = betaPrimes ↥M :=
    FBG_kappa_residual_beta_equality h₁ h₂ h₃ h₄ h₅ G hG M K U hsetup
  have hSbot : sigmaCore M ≠ ⊥ := (FBG_sigma_core_nontrivial h₁ G hG02 M hsetup.isCoatom).2
  have hcent : ∀ (r : ℕ) (P : Subgroup G), r.Prime → P ≤ sigmaCore M → Nat.card ↥P = r →
      centralizer (P : Set G) ≤ M := fun r P hr hPS hPcard =>
    centralizer_le_of_le_sigmaCore_of_natCard_eq_prime hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable hsetup.isCoatom hHallOf hnil hbeta hSbot hr hPS hPcard
  exact ⟨hKprime, hbeta, hnil, normalizer_sharp_sigmaCore_eq hsetup.isCoatom hSbot,
    fun g hg => inter_conjSet_sharp_sigmaCore_eq_empty hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable hsetup.isCoatom hcent hg⟩

end

end CFSG.FeitThompson.Proofs
