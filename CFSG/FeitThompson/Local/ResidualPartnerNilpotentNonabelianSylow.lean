module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.ResidualNormalizerSingleRankTwoPrime
import CFSG.FeitThompson.Local.KappaNontrivialComplementStructure
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.CommonPrimeFixedCoreFittingEnvelope
import CFSG.FeitThompson.Local.SigmaCoreComplementFixedInDerived
import CFSG.FeitThompson.Local.KappaPositiveMultipleCoreTrivialResidual
import CFSG.FeitThompson.Local.TauTwoAbelianSylowPropagation
import CFSG.FeitThompson.Local.SharedSigmaSylowSetup
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
import CFSG.FeitThompson.Local.MaximalSubgroupTypeDichotomy
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.FittingEqualsChiefActionKernel
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.PLengthOneSylowNormalizerDerivedTransfer
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
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

universe u

variable {G : Type u} [Group G] [Finite G] {q : ℕ}

theorem commutator_inf_eq_bot_of_isMulCommutative_of_normal_sylow {X : Type*} [Group X] [Finite X]
    [Group.IsNilpotent X] (hq : q.Prime) {Q : Subgroup X} [Q.Normal]
    (hQcard : Nat.card ↥Q = q ^ (Nat.card X).factorization q) (hQab : IsMulCommutative ↥Q) :
    _root_.commutator X ⊓ Q = ⊥ := by
  have _i : Fact q.Prime := ⟨hq⟩
  have hQp : IsPGroup q ↥Q := IsPGroup.of_card hQcard
  have hcore : pCore q X ≤ Q :=
    le_of_isPGroup_of_normal_of_natCard_eq hq hQcard (isPGroup_pCore hq X)
  have hAn := pCore_normal q X
  have hBn := pComplCore_normal q X
  have hinf : pComplCore q X ⊓ pCore q X = ⊥ := inf_pComplCore_eq_bot (isPGroup_pCore hq X)
  have hAab : IsMulCommutative ↥(pCore q X) := isMulCommutative_of_le hcore
  have hcomm : ∀ a ∈ pCore q X, ∀ b ∈ pComplCore q X, Commute a b := fun a ha b hb =>
    (Subgroup.commute_of_normal_of_disjoint _ _ hBn hAn (disjoint_iff.2 hinf) b a hb ha).symm
  have hAA : ⁅pCore q X, pCore q X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (hAab.is_comm.comm (⟨y, hy⟩ : ↥(pCore q X)) ⟨x, hx⟩)
  have hle : _root_.commutator X ≤ pComplCore q X := by
    refine le_trans (commutator_le_sup_commutator_commutator
      (pCore_sup_pComplCore_eq_top hq X) hcomm) ?_
    rw [hAA, bot_sup_eq]
    exact Subgroup.commutator_le_self _
  have hQinf : pComplCore q X ⊓ Q = ⊥ := inf_pComplCore_eq_bot hQp
  exact le_bot_iff.1 (hQinf ▸ le_inf (inf_le_left.trans hle) inf_le_right)

omit [Finite G] in
theorem map_subtype_commutator (S : Subgroup G) :
    (_root_.commutator ↥S).map S.subtype = ⁅S, S⁆ := by
  rw [commutator_def, Subgroup.map_commutator]
  congr 1 <;> rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem inf_commutator_eq_bot_of_isMulCommutative (hq : q.Prime) {S Q : Subgroup G}
    (hnil : Group.IsNilpotent ↥S) (hQS : Q ≤ S) (hnorm : S ≤ normalizer (Q : Set G))
    (hQcard : Nat.card ↥Q = q ^ (Nat.card ↥S).factorization q)
    (hQab : IsMulCommutative ↥Q) : ⁅S, S⁆ ⊓ Q = ⊥ := by
  have _n := hnil
  have _hN : (Q.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hcard : Nat.card ↥(Q.subgroupOf S) = q ^ (Nat.card ↥S).factorization q := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv, hQcard]
  have hab : IsMulCommutative ↥(Q.subgroupOf S) :=
    have e := subgroupOfEquivOfLe hQS
    ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hQab.is_comm.comm _ _)⟩⟩
  have hkey := commutator_inf_eq_bot_of_isMulCommutative_of_normal_sylow hq hcard hab
  have hmap : ((_root_.commutator ↥S) ⊓ Q.subgroupOf S).map S.subtype = ⊥ := by
    rw [hkey, Subgroup.map_bot]
  rwa [Subgroup.map_inf _ _ _ S.subtype_injective, map_subtype_commutator,
    Subgroup.map_subgroupOf_eq_of_le hQS] at hmap

theorem partner_structure_of_kappa_residual
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_residual_rank_two_plane_partner_fitting.{u})
    (hG : Prep08.IsMinimalSimpleOddOrder G)
    {M K U A Mstar R H : Subgroup G} {r : ℕ}
    (hsetup : Prep08.IsKappaResidualSetup M K U A Mstar R H r)
    (hne : (tauTwoPrimes H).Nonempty) :
    Group.IsNilpotent ↥(sigmaCore Mstar) ∧
      FreeCore.IsInternalSemidirectProduct Mstar (sigmaCore Mstar) A ∧
      ⁅Mstar, Mstar⁆ = sigmaCore Mstar ∧
      IsHallPiSubgroupOf (sigmaPrimes Mstar) (sigmaCore Mstar) Mstar ∧
      Nat.card ↥K ∈ sigmaPrimes Mstar ∧
      ((pCoreOf (Nat.card ↥K) Mstar).subgroupOf Mstar).Normal ∧
      Nat.card ↥(pCoreOf (Nat.card ↥K) Mstar)
        = Nat.card ↥K ^ (Nat.card ↥Mstar).factorization (Nat.card ↥K) ∧
      K ≤ sigmaCore Mstar ∧ K ≤ ⁅sigmaCore Mstar, sigmaCore Mstar⁆ := by
  have _f : Fintype G := Fintype.ofFinite G
  have hsimple := hG.isSimpleGroup
  have hamb7 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hamb2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  set q := Nat.card ↥K with hqdef
  have hq : q.Prime := (h₆ G hG M K U A Mstar R H r hsetup).1
  have _i : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, -, hβ⟩ :=
    FTS_residual_normalizer_single_rank_two_prime h₅ h₆ h₉ G hG M K U A Mstar R H r hsetup hne
  have hkappa : Prep03.IsKappaSetup G M K A (K ⊔ A) :=
    { ambient := ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative,
        hG.isSolvable_of_ne_top⟩
      isCoatom := hsetup.isCoatom_M
      kappa_nonempty := hsetup.kappa_nonempty
      isHall_K := by
        obtain ⟨hKM, hHall⟩ := hsetup.isHall_K
        rw [isHallPiSubgroup_iff] at hHall
        refine ⟨hKM, fun s hs => hHall.1 s ?_, fun s hs => hHall.2 s hs⟩
        rwa [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv]
      A_eq := hsetup.A_eq
      Z_eq := rfl }
  obtain ⟨Mstar', -, huniq, -, hAne, hAhall', hCA, -⟩ := h₃ G M K A (K ⊔ A) hkappa
  have hMstar : Mstar' = Mstar :=
    (huniq Mstar hsetup.isCoatom_Mstar hsetup.exists_prime_order_le_K).symm
  rw [hMstar] at hAhall' hCA
  have hAhall : IsHallPiSubgroupOf (kappaPrimes Mstar) A Mstar :=
    isHallPiSubgroupOf_of_isHallPiOf hAhall' (fun _ _ => Iff.rfl)
  have hKS : K ≤ sigmaCore Mstar := by rw [← hCA]; exact inf_le_left
  have hqσ : q ∈ sigmaPrimes Mstar :=
    mem_sigmaPrimes_of_prime_dvd_natCard_sigmaCore hq (hqdef ▸ Subgroup.card_dvd_of_le hKS)
  have hσβ : sigmaPrimes Mstar ≠ betaPrimes ↥Mstar := fun h => hβ (h ▸ hqσ)
  have hκ : (kappaPrimes Mstar).Nonempty :=
    kappaPrimes_nonempty_of_ne_bot hAhall.1 hAhall.2 hAne
  have hsemi : FreeCore.IsInternalSemidirectProduct Mstar (sigmaCore Mstar) A :=
    isInternalSemidirectProduct_sigmaCore_of_sigmaPrimes_ne_betaPrimes
      (FBG_kappa_nontrivial_complement_structure h₂ h₄ h₅ h₇ h₈) h₄ hG.odd_natCard
      hG.isSimpleGroup hG.not_isMulCommutative hG.isSolvable_of_ne_top hsetup.isCoatom_Mstar
      hκ hσβ hAhall
  have hkappa2 : Prep03.IsKappaSetup G Mstar A (Prep03.cent (sigmaCore Mstar) (A : Set G))
      (A ⊔ Prep03.cent (sigmaCore Mstar) (A : Set G)) :=
    { ambient := ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative,
        hG.isSolvable_of_ne_top⟩
      isCoatom := hsetup.isCoatom_Mstar
      kappa_nonempty := hκ
      isHall_K := hAhall'
      A_eq := rfl
      Z_eq := rfl }
  obtain ⟨-, -, hderived⟩ := FNI_kappa_derived_complement h₃ h₄ G Mstar A _ _ hkappa2
  have hMs' : ⁅Mstar, Mstar⁆ = sigmaCore Mstar := by
    have hh1 : Prep03.IsSemidirect Mstar (sigmaCore Mstar) (⊥ ⊔ A) := by
      rw [bot_sup_eq]; exact isSemidirect_of_isInternalSemidirectProduct hsemi
    have hh2 : Prep03.IsSemidirect ((⊥ : Subgroup G) ⊔ A) ⊥ A :=
      ⟨bot_le, le_sup_right, fun x _ => Subgroup.mem_normalizer_iff.2 (by simp), rfl, by simp⟩
    have hh3 := hderived ⊥ hh1 hh2
    rwa [sup_bot_eq] at hh3
  have hCAcard : Nat.card ↥(sigmaCore Mstar ⊓ centralizer (A : Set G)) = q := by
    rw [show sigmaCore Mstar ⊓ centralizer (A : Set G)
      = Prep03.cent (sigmaCore Mstar) (A : Set G) from rfl, hCA]
  obtain ⟨hQnormal, hQsylow, -, hnilImp⟩ :=
    FTS_common_prime_fixed_core_fitting_envelope h₁ h₄ G hamb7 Mstar hsetup.isCoatom_Mstar hκ
      A hAhall q hq hCAcard
  have hnil : Group.IsNilpotent ↥(sigmaCore Mstar) := by
    by_contra hc
    exact hβ (hnilImp hc)
  have hKder : K ≤ ⁅sigmaCore Mstar, sigmaCore Mstar⁆ := by
    rw [← hCA]
    exact FTS_complement_fixed_core_contained_derived G hamb7 Mstar hsetup.isCoatom_Mstar A
      hAhall.1 hsemi
  have hSHall : IsHallPiSubgroupOf (sigmaPrimes Mstar) (sigmaCore Mstar) Mstar :=
    (h₂ G hamb2 Mstar hsetup.isCoatom_Mstar).1
  exact ⟨hnil, hsemi, hMs', hSHall, hqσ, hQnormal, hQsylow.2, hKS, hKder⟩

theorem not_isMulCommutative_pCoreOf_and_isSylow (hq : q.Prime) {Mstar : Subgroup G}
    (hSHall : IsHallPiSubgroupOf (sigmaPrimes Mstar) (sigmaCore Mstar) Mstar)
    (hqσ : q ∈ sigmaPrimes Mstar)
    (hQnormal : ((pCoreOf q Mstar).subgroupOf Mstar).Normal)
    (hQsylow : Nat.card ↥(pCoreOf q Mstar) = q ^ (Nat.card ↥Mstar).factorization q)
    (hnil : Group.IsNilpotent ↥(sigmaCore Mstar))
    {K : Subgroup G} (hKcard : Nat.card ↥K = q) (hKS : K ≤ sigmaCore Mstar)
    (hKder : K ≤ ⁅sigmaCore Mstar, sigmaCore Mstar⁆) :
    ¬ IsMulCommutative ↥(pCoreOf q Mstar) ∧
      Mstar ≤ normalizer ((pCoreOf q Mstar : Subgroup G) : Set G) ∧
      Prep08.IsSylowOf q (pCoreOf q Mstar) Mstar ∧ Prep08.IsSylowOf q (pCoreOf q Mstar) ⊤ := by
  have _i : Fact q.Prime := ⟨hq⟩
  have _hN := hQnormal
  have hQle : pCoreOf q Mstar ≤ Mstar := pCoreOf_le q Mstar
  have hnormQ : Mstar ≤ normalizer ((pCoreOf q Mstar : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (hK := hQnormal) hQle
  have hSylowM : Prep08.IsSylowOf q (pCoreOf q Mstar) Mstar :=
    (Prep08.isSylowOf_iff_natCard hq hQle).2 hQsylow
  have hSylowG : Prep08.IsSylowOf q (pCoreOf q Mstar) ⊤ := by
    refine (Prep08.isSylowOf_iff_natCard hq le_top).2 ?_
    rw [hQsylow, Subgroup.card_top]
    exact congrArg (q ^ ·) (factorization_eq_of_mem_sigmaPrimes hqσ)
  refine ⟨?_, hnormQ, hSylowM, hSylowG⟩
  intro hQab
  have hQp : IsPGroup q ↥(pCoreOf q Mstar) := hSylowM.isPGroup
  have hQS : pCoreOf q Mstar ≤ sigmaCore Mstar :=
    le_sigmaCore_of_isPGroup hq hSHall hqσ hQle hQp
  have hfac : (Nat.card ↥Mstar).factorization q = (Nat.card ↥(sigmaCore Mstar)).factorization q :=
    factorization_natCard_eq_of_isHallPiSubgroup_subgroupOf hq hSHall.1 hSHall.2 hqσ
  have hQcard : Nat.card ↥(pCoreOf q Mstar)
      = q ^ (Nat.card ↥(sigmaCore Mstar)).factorization q := by rw [hQsylow, hfac]
  have hnormS : sigmaCore Mstar ≤ normalizer ((pCoreOf q Mstar : Subgroup G) : Set G) :=
    le_trans (sigmaCore_le Mstar) hnormQ
  have hbot := inf_commutator_eq_bot_of_isMulCommutative hq hnil hQS hnormS hQcard hQab
  have hKQ : K ≤ pCoreOf q Mstar := by
    have hKM : K ≤ Mstar := hKS.trans (sigmaCore_le Mstar)
    have h1 : K.subgroupOf Mstar ≤ (pCoreOf q Mstar).subgroupOf Mstar := by
      refine le_of_isPGroup_of_normal_of_natCard_eq (L := ↥Mstar) hq ?_ ?_
      · rw [Nat.card_congr (subgroupOfEquivOfLe hQle).toEquiv, hQsylow]
      · exact IsPGroup.of_card (n := 1)
          (by rw [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv, hKcard, pow_one])
    have h2 := Subgroup.map_mono (f := Mstar.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hKM, Subgroup.map_subgroupOf_eq_of_le hQle] at h2
  have hKbot : K = ⊥ := le_bot_iff.1 (hbot ▸ le_inf hKder hKQ)
  rw [hKbot, Subgroup.card_bot] at hKcard
  exact hq.ne_one hKcard.symm

theorem FTS_residual_partner_nilpotent_nonabelian_sylow
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_residual_rank_two_plane_partner_fitting.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_residual_partner_nilpotent_nonabelian_sylow.{u} := by
  intro G _ _ hG M K U A Mstar R H r hsetup hne
  have hq : (Nat.card ↥K).Prime := (h₆ G hG M K U A Mstar R H r hsetup).1
  obtain ⟨hnil, hsemi, hMs', hSHall, hqσ, hQnormal, hQsylow, hKS, hKder⟩ :=
    partner_structure_of_kappa_residual h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ hG hsetup hne
  obtain ⟨hQnonab, hQnorm, hQM, hQG⟩ :=
    not_isMulCommutative_pCoreOf_and_isSylow hq hSHall hqσ hQnormal hQsylow hnil rfl hKS hKder
  exact ⟨hnil, hsemi, hMs', hQnonab, hQnorm, hQM, hQG⟩

end

end CFSG.FeitThompson.Proofs
