module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
import CFSG.FeitThompson.Local.FiveTypeLocalClassification
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Foundations.LiftHallByNormalComplement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem prep09_hallCoreIn_eq (M : Subgroup G) :
    CFSG.FeitThompson.Prep09.hallCoreIn M = CFSG.FeitThompson.hallCoreIn M := (rfl)

theorem isFBGAmbient_of_isMinimalSimpleOddOrder [Finite G]
    (hG : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G) : CFSG.FeitThompson.IsFBGAmbient G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩

theorem isOddOrderMinimalSimple_of_isMinimalSimpleOddOrder [Finite G]
    (hG : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G) :
    CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩

theorem kappaPrimes_eq_empty_of_isHallPiSubgroup_bot [Finite G] {M : Subgroup G}
    (hK : IsHallPiSubgroup (kappaPrimes M) ((⊥ : Subgroup G).subgroupOf M)) :
    kappaPrimes M = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  refine hK.notMem_of_mem_primeFactors_index p ?_ hp
  rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
  exact Nat.mem_primeFactors.2
    ⟨prime_of_mem_kappaPrimes hp, dvd_natCard_of_mem_kappaPrimes hp, Nat.card_pos.ne'⟩

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson

universe u

theorem FTS_type_I_core_kappa_identity
    (h₁ : Statements.FBG_kappa_complement_structure.{u})
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₆ : Statements.FBG_local_p_trivial_U_alternative.{u})
    (h₇ : Statements.FBG_local_type_I_alternative.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) :
    Statements.FTS_type_I_core_kappa_identity.{u} := by
  intro G _ _ hG M hM hMI
  have : Fintype G := Fintype.ofFinite G
  have hamb : IsFBGAmbient G := isFBGAmbient_of_isMinimalSimpleOddOrder hG
  have hoo : IsOddOrderMinimalSimple G := isOddOrderMinimalSimple_of_isMinimalSimpleOddOrder hG
  obtain ⟨K, V, hKM, -, hKhall, hVM, hsemiM, hsemiVK, -, -⟩ := h₁ G hamb M hM
  have hsetup : IsLocalKappaSetup M K V :=
    ⟨hM, hKM, hKhall, hVM, hsemiVK.right_le_normalizer, hsemiM, hsemiVK⟩
  have hcls := (Proofs.FBG_five_type_local_classification.{u}
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ G hamb).2 M K V hsetup
  have hKbot : K = ⊥ := hcls.1.1 hMI
  have hκ : kappaPrimes M = ∅ := by
    refine kappaPrimes_eq_empty_of_isHallPiSubgroup_bot ?_
    rwa [hKbot] at hKhall
  have hHS : CFSG.FeitThompson.hallCoreIn M = sigmaCore M := by
    by_contra hne
    have hcon := (h₃ G hamb M K V hsetup).2 hne
    rw [hKbot] at hcon
    simp only [Subgroup.card_bot] at hcon
    exact Nat.not_prime_one hcon.2.1
  refine ⟨hκ, by rw [prep09_hallCoreIn_eq]; exact hHS, ?_⟩
  intro U hU s hs
  obtain ⟨-, hprod, hinf⟩ := hU
  rw [prep09_hallCoreIn_eq, hHS] at hprod hinf
  have hcard : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥U :=
    natCard_eq_mul_of_mul_eq_of_inf_eq_bot hprod hinf
  obtain ⟨⟨hSle, hSHall⟩, -, -⟩ := FBG_sigma_core_normal_hall.{u} G hoo M hM
  have hidx : ((sigmaCore M).subgroupOf M).index = Nat.card ↥U := by
    have h1 : Nat.card ↥((sigmaCore M).subgroupOf M) * ((sigmaCore M).subgroupOf M).index
        = Nat.card ↥M := Subgroup.card_mul_index _
    have h2 : Nat.card ↥((sigmaCore M).subgroupOf M) = Nat.card ↥(sigmaCore M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv
    rw [h2, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  rw [← hidx] at hs
  exact hSHall.notMem_of_mem_primeFactors_index s hs

end CFSG.FeitThompson.Proofs

end
