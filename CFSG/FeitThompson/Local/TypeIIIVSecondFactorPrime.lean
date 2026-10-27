module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.KappaComplementStructure
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.PConfigurationKappaFactors
import CFSG.FeitThompson.Local.KappaFixedSubgroupDerivedAndHall
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {M E R W₁ W₂ : Subgroup G}

private theorem conj_smul_eq_map_conj_aux {X : Type*} [Group X] (g : X) (S : Subgroup X) :
    MulAut.conj g • S = S.map (MulAut.conj g : X →* X) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem exists_mem_commutator_map_conj_eq_of_sigmaCore_complement
    (hc : IsWitnessedPConfiguration M E W₁ W₂)
    (hHS : (hallCore ↥M).map M.subtype = sigmaCore M)
    (hsup : sigmaCore M ⊔ R = (⁅M, M⁆ : Subgroup G))
    (hdisj : Disjoint (sigmaCore M) R)
    (hsolv : Group.IsSolvable ↥(⁅M, M⁆ : Subgroup G)) :
    ∃ g ∈ (⁅M, M⁆ : Subgroup G), R.map (MulAut.conj g : G →* G) = E := by
  have := hsolv
  have hRle : R ≤ (⁅M, M⁆ : Subgroup G) := by rw [← hsup]; exact le_sup_right
  have hsemi : FreeCore.IsInternalSemidirectProduct (⁅M, M⁆ : Subgroup G) (sigmaCore M) R :=
    ⟨hsup, (Subgroup.commutator_le_self M).trans (le_normalizer_sigmaCore M), hdisj⟩
  have hcardM' : Nat.card ↥(⁅M, M⁆ : Subgroup G) = Nat.card ↥(sigmaCore M) * Nat.card ↥R :=
    hsemi.natCard_eq_mul
  have hcardE : Nat.card ↥(⁅M, M⁆ : Subgroup G) = Nat.card ↥(sigmaCore M) * Nat.card ↥E := by
    rw [hc.natCard_commutator_eq, hHS]
  have hRE : Nat.card ↥R = Nat.card ↥E :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcardM'.symm.trans hcardE)
  have hEhall : IsHallSubgroup ((Nat.card ↥E).primeFactors : Set ℕ)
      (E.subgroupOf (⁅M, M⁆ : Subgroup G)) := hc.isHallSubgroup_subgroupOf_E rfl
  have hRcard : Nat.card ↥(R.subgroupOf (⁅M, M⁆ : Subgroup G)) = Nat.card ↥E := by
    rw [natCard_subgroupOf hRle, hRE]
  have hidx : (R.subgroupOf (⁅M, M⁆ : Subgroup G)).index = Nat.card ↥(sigmaCore M) := by
    have h := Subgroup.card_mul_index (R.subgroupOf (⁅M, M⁆ : Subgroup G))
    rw [hRcard, hcardE, mul_comm (Nat.card ↥(sigmaCore M))] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hRhall : IsHallSubgroup ((Nat.card ↥E).primeFactors : Set ℕ)
      (R.subgroupOf (⁅M, M⁆ : Subgroup G)) := by
    have hdisjpf := hc.coprime_natCard_hallCore_natCard_E.disjoint_primeFactors
    rw [hHS] at hdisjpf
    refine isHallSubgroup_iff.2 ⟨?_, ?_⟩
    · rw [isPiNumber_iff, hRcard]
      exact fun p hp => by simpa using hp
    · rw [isPiNumber_iff, hidx]
      intro p hp
      simp only [Set.mem_compl_iff, Finset.mem_coe]
      exact Finset.disjoint_left.1 hdisjpf hp
  obtain ⟨x, hx⟩ := exists_conj_smul_eq_of_isHallSubgroup hRhall hEhall
  refine ⟨(x : G), x.2, ?_⟩
  have h := congrArg (Subgroup.map (⁅M, M⁆ : Subgroup G).subtype) hx
  rwa [conj_smul_eq_map_conj_aux, map_subtype_map_conj,
    Subgroup.map_subgroupOf_eq_of_le hRle,
    Subgroup.map_subgroupOf_eq_of_le hc.le_commutator_E] at h

omit [Finite G] in
theorem normalizer_le_of_map_conj_eq {A B C : Subgroup G} {g : G} (hgC : g ∈ C)
    (hmap : A.map (MulAut.conj g : G →* G) = B) (h : normalizer (B : Set G) ≤ C) :
    normalizer (A : Set G) ≤ C := by
  intro x hx
  have h1 : MulAut.conj g x ∈ normalizer (B : Set G) := by
    rw [← hmap, ← map_normalizer_coe (MulAut.conj g) A]
    exact Subgroup.mem_map_of_mem _ hx
  simpa [MulAut.conj_apply, mul_assoc] using
    C.mul_mem (C.mul_mem (C.inv_mem hgC) (h h1)) hgC

end CFSG.FeitThompson

end

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FPF_type_iii_v_second_factor_prime
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_intersection.{u}) :
    _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc
  have hsimple := hG.simple
  have _fin : Finite G := Finite.of_fintype G
  have hMsolv : Group.IsSolvable ↥M := hG.solvable M hM.1
  have hM'solv : Group.IsSolvable ↥(⁅M, M⁆ : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (Subgroup.commutator_le_self M))
  have hambFBG : IsFBGAmbient G := ⟨hG.odd, hsimple, hG.nonabelian, hG.solvable⟩
  have hamb03 : IsAmbient G := ⟨hG.odd, hsimple, hG.nonabelian, hG.solvable⟩
  have hamb04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd, hsimple, hG.nonabelian, hG.solvable⟩
  obtain ⟨hκ, hW₁hall, hW₂eq⟩ :=
    FNI_p_configuration_kappa_factors h₂ h₃ G hamb04 M U W₁ W₂ hM hc
  obtain ⟨K, R, hKM, -, hKhall, hRM, hsd1, hsd2, -, hifK⟩ :=
    FBG_kappa_complement_structure h₂ h₃ h₅ G hambFBG M hM
  have hKpi : IsHallPiOf (kappaPrimes M) K M :=
    isHallPiOf_of_isHallSubgroup_subgroupOf hKM (isHallSubgroup_iff_isHallPiSubgroup.2 hKhall)
  have hKbot : K ≠ ⊥ := (h₃ G hamb03 M K hM hκ hKpi).1
  obtain ⟨-, hnormR, -, -⟩ := hifK hKbot
  have hsetupK : IsKappaSetup G M K (cent (sigmaCore M) (K : Set G))
      (K ⊔ cent (sigmaCore M) (K : Set G)) :=
    { ambient := hamb03
      isCoatom := hM
      kappa_nonempty := hκ
      isHall_K := hKpi
      A_eq := rfl
      Z_eq := rfl }
  have hderived : (⁅M, M⁆ : Subgroup G) = sigmaCore M ⊔ R :=
    (FNI_kappa_derived_complement h₂ h₃ G M K _ _ hsetupK).2.2 R
      (isSemidirect_of_isInternalSemidirectProduct hsd1)
      (isSemidirect_of_isInternalSemidirectProduct hsd2)
  have hdisjSR : Disjoint (sigmaCore M) R :=
    hsd1.disjoint.mono_right (le_sup_left : R ≤ R ⊔ K)
  have hRbot : R = ⊥ := by
    by_contra hRne
    have hlocal : IsLocalKappaSetup M K R :=
      { isCoatom := hM
        le_M_K := hKM
        hall_K := hKhall
        le_M_U := hRM
        le_normalizer_U := hsd2.right_le_normalizer
        semidirect_M := hsd1
        semidirect_UK := hsd2 }
    obtain ⟨-, -, -, hHS⟩ := h₁ G hambFBG M K R hlocal hKbot hRne
    have hHS' : (hallCore ↥M).map M.subtype = sigmaCore M := hHS
    rcases htype with htype | htype | htype
    ·
      obtain ⟨-, -, -, hnorm⟩ := htype.clauses_of_isWitnessedPConfiguration hMsolv hc
      obtain ⟨g, hg, hgR⟩ := exists_mem_commutator_map_conj_eq_of_sigmaCore_complement hc hHS'
        hderived.symm hdisjSR hM'solv
      exact hnormR (normalizer_le_of_map_conj_eq (Subgroup.commutator_le_self M hg) hgR hnorm)
    ·
      obtain ⟨-, -, hnorm⟩ := htype.clauses_of_isWitnessedPConfiguration hMsolv hc
      obtain ⟨g, hg, hgR⟩ := exists_mem_commutator_map_conj_eq_of_sigmaCore_complement hc hHS'
        hderived.symm hdisjSR hM'solv
      exact hnormR (normalizer_le_of_map_conj_eq (Subgroup.commutator_le_self M hg) hgR hnorm)
    ·
      obtain ⟨hU, -⟩ := htype.clauses_of_isWitnessedPConfiguration hMsolv hc
      have hM'S : (⁅M, M⁆ : Subgroup G) = sigmaCore M := by
        rw [← hc.sup_hallCore_E, hU, sup_bot_eq, hHS']
      have hRS : R ≤ sigmaCore M := by
        rw [← hM'S, hderived]; exact le_sup_right
      exact hRne (le_bot_iff.1 (le_trans (le_inf hRS le_rfl) (disjoint_iff.1 hdisjSR).le))
  have hM'S : (⁅M, M⁆ : Subgroup G) = sigmaCore M := by rw [hderived, hRbot, sup_bot_eq]
  have hW₁pi : IsHallPiOf (kappaPrimes M) W₁ M :=
    isHallPiOf_of_isHallSubgroup_subgroupOf hc.le_M_W₁
      (isHallSubgroup_iff_isHallPiSubgroup.2 hW₁hall)
  have hsetupW : IsKappaSetup G M W₁ (cent (sigmaCore M) (W₁ : Set G))
      (W₁ ⊔ cent (sigmaCore M) (W₁ : Set G)) :=
    { ambient := hamb03
      isCoatom := hM
      kappa_nonempty := hκ
      isHall_K := hW₁pi
      A_eq := rfl
      Z_eq := rfl }
  have hsemiW : IsSemidirect M (sigmaCore M) W₁ := by
    refine ⟨sigmaCore_le M, hc.le_M_W₁, le_normalizer_sigmaCore M, ?_, ?_⟩
    · rw [← hM'S]; exact hc.sup_commutator_W₁
    · rw [← disjoint_iff]
      exact hc.disjoint_commutator_W₁.mono_left (hM'S ▸ le_rfl)
  obtain ⟨-, -, hAprime, -⟩ := h₄ G M W₁ _ _ hsetupW hsemiW
  rwa [show cent (sigmaCore M) (W₁ : Set G) = W₂ from hW₂eq] at hAprime

end

end CFSG.FeitThompson.Proofs
