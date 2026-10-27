module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.AbelianNormalHallNoncentralActionSplit
import CFSG.FeitThompson.Local.AbelianAmbientNormalizerChain
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.NonregularPlaneLineUniqueCentralizer
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
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

open CFSG.FeitThompson Subgroup

universe u

theorem FNI_abelian_normal_hall_full_exponent_cycle
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_abelian_plane_overlap_normalizer_rank.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_abelian_normal_hall_full_exponent_cycle.{u} := by
  intro G _ _ hG p M A E K U P hsetup hK hKE hUE hEUK hPsyl hPab hAP hPU
  have hp : p.Prime := hsetup.prime
  have hpf : Fact p.Prime := ⟨hp⟩
  have hGosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hGfbg : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsetup.decomp.2.2.2.1, hsetup.decomp.2.2.1, disjoint_iff.2 hsetup.decomp.2.2.2.2⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hsetup.isCoatom, hsd⟩
  have hplane : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane⟩
  have hEM : E ≤ M := hsetup.decomp.2.1
  have hAcard : Nat.card ↥A = p ^ 2 := hplane.isElementaryAbelianPlane.natCard'
  have hPM : P ≤ M := hPU.trans (hUE.trans hEM)
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hPsyl
  have hpA : p ∣ Nat.card ↥A := by rw [hAcard]; exact dvd_pow_self p two_ne_zero
  have hodd : Odd p := hG.odd_natCard.of_dvd_nat (hpA.trans A.card_subgroup_dvd_card)
  have hfacteq : (Nat.card ↥M).factorization p = (Nat.card G).factorization p := by
    refine le_antisymm ((Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1
      ((Nat.ordProj_dvd _ _).trans M.card_subgroup_dvd_card)) ?_
    refine (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 ?_
    rw [← hPsyl]
    exact Subgroup.card_dvd_of_le hPM
  have hPsylM : _root_.CFSG.FeitThompson.IsSylowIn p M P :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hPM).2 (by rw [hPsyl, hfacteq])
  obtain ⟨-, -, hsylclause, A₁, hA₁A, hA₁card, hA₁C⟩ := h₇ G hGosm p M A hplane
  obtain ⟨hAtors, hNS⟩ := (hsylclause P hPsylM).2 hAP
  have h3 : 3 ∉ elementaryAbelianRanks p ↥P := by
    intro hmem
    obtain ⟨H, -, hexp, hcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hp).1 hmem
    have hBle : H.map P.subtype ≤ A := by
      rintro x ⟨y, hy, rfl⟩
      have hy1 : ((y : G)) ^ p = 1 := congrArg (Subgroup.subtype P) (hexp y hy)
      have hmemA : (y : G) ∈ (A : Set G) := by rw [hAtors]; exact ⟨y.2, hy1⟩
      exact hmemA
    have hBcard : Nat.card ↥(H.map P.subtype) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective P.subtype_injective, hcard]
    have hdvd := Subgroup.card_dvd_of_le hBle
    rw [hBcard, hAcard] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
    omega
  have hreg : ∀ B : Subgroup G, B ≤ P → Nat.card ↥B = p →
      sigmaCore M ⊓ centralizer (B : Set G) ≠ ⊥ → normalizer (B : Set G) ≤ M :=
    fun B hBP hBcard hBC =>
      (FNI_nonregular_plane_line_unique_centralizer h₅ h₆ G hGosm p M A E B hplane hsc
        hsetup.le_E_A (hBP.trans (hPU.trans hUE)) hBcard hBC).2
  have hA₁P : A₁ ≤ P := hA₁A.trans hAP
  have hPnt : P ≠ ⊥ := by
    intro hb
    rw [hb, le_bot_iff] at hAP
    rw [hAP, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1, rfl⟩⟩] at hAcard
    exact absurd hAcard.symm (by simpa using (Nat.one_lt_pow two_ne_zero hp.one_lt).ne')
  have key : (∃ Z : Subgroup G, Z ≤ P ∧ IsCyclic ↥Z ∧ (Z.subgroupOf U).Normal ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥P ∧
      ∀ z ∈ Z, z ≠ 1 → sigmaCore M ⊓ centralizer ({z} : Set G) = ⊥) →
      ∃ Z : Subgroup G, Z ≤ P ∧ IsCyclic ↥Z ∧ U ≤ Subgroup.normalizer (Z : Set G) ∧
        Monoid.exponent ↥Z = Monoid.exponent ↥P ∧
        ∀ z ∈ Z, z ≠ 1 → CFSG.FeitThompson.Prep03.cent1
          (sigmaCore M) z = ⊥ := by
    rintro ⟨Z, hZP, hZcyc, hZnorm, hZexp, hZfree⟩
    exact ⟨Z, hZP, hZcyc, le_normalizer_of_normal_subgroupOf (hZP.trans hPU) hZnorm, hZexp, hZfree⟩
  by_cases hcen : P ≤ CFSG.FeitThompson.Prep03.cent U (U : Set G)
  ·
    exact key (exists_cyclic_normal_exponent_eq hp
      (le_map_center_iff_le_inf_centralizer.2 hcen) hPnt hPp h3 hNS hreg hA₁P hA₁card hA₁C)
  ·
    obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hGosm M E hsc
    have hdec : CFSG.FeitThompson.IsTauHallDecomposition
        M E E₁ E₂ E₃ (E₂ ⊔ E₃) :=
      ⟨hsplit.le_E₁, hsplit.le_E₂, hsplit.le_E₃, hsplit.isHall_E₁, hsplit.isHall_E₂,
        hsplit.isHall_E₃, hsplit.outer, hsplit.inner, rfl⟩
    have hAsetup : CFSG.FeitThompson.IsAbelianAmbientSetup M p A E P :=
      ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane,
        hsetup.decomp.2.1, hsd, hsetup.le_E_A, hPab,
        ⟨Sylow.ofCard P hPsyl, Sylow.coe_ofCard _ _⟩, hAP⟩
    obtain ⟨hNAP, -, -, -, hENA, -, -⟩ := FBG_abelian_ambient_normalizer_chain h₁ h₂ h₅ h₇ h₈ G
      hGfbg M p A E P E₁ E₂ E₃ (E₂ ⊔ E₃) hAsetup hdec
    have hUN : U ≤ normalizer (P : Set G) := hUE.trans (hNAP ▸ hENA)
    obtain ⟨P₀, P₁, hP₀nt, hP₁nt, hP₀P, hP₁P, hN₀, hN₁, hsup, hdisj⟩ :=
      FNI_abelian_normal_hall_noncentral_action_split h₁ h₂ h₃ h₄ h₅ h₇ h₈ h₉ G hG p M A E K U P
        hsetup hK hKE hUE hEUK hPsyl hPab hAP hPU hcen
    exact key (exists_cyclic_normal_exponent_eq_of_sup_eq hp hodd hPU hPab hPp h3 hNS hreg
      (normal_subgroupOf_of_le_normalizer hPU hUN) hsup hdisj hP₀nt hP₁nt
      (normal_subgroupOf_of_le_normalizer (hP₀P.trans Subgroup.le_normalizer) hN₀)
      (normal_subgroupOf_of_le_normalizer (hP₁P.trans Subgroup.le_normalizer) hN₁))

end

end CFSG.FeitThompson.Proofs
