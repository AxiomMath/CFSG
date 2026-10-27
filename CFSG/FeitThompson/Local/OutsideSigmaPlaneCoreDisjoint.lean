module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PlaneMaximalOvergroupUniqueExceptional
import CFSG.FeitThompson.Local.OppositeSigmaPlaneCoreIntersection
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Local.NormalPrimeProductCommutator
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
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

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup

universe u

variable {G : Type u} [Group G]

theorem commutator_le_of_le_normalizer_sup_of_coprime [Finite G] {p n : ℕ} (hp : p.Prime)
    {L N A Y : Subgroup G} (hNL : N ≤ L) (hAL : A ≤ L) (hYL : Y ≤ L)
    (hLN : L ≤ normalizer ((N : Subgroup G) : Set G))
    (hLNA : L ≤ normalizer ((N ⊔ A : Subgroup G) : Set G))
    (hN : (Nat.card ↥N).Coprime p) (hA : Nat.card ↥A = p ^ n)
    (hY : (Nat.card ↥Y).Coprime p) (hAY : A ≤ normalizer ((Y : Subgroup G) : Set G)) :
    ⁅Y, A⁆ ≤ N := by
  have hnorm : (N.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hNL hLN
  have hnorm2 : ((N ⊔ A).subgroupOf L).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hNL hAL) hLNA
  rw [Subgroup.subgroupOf_sup hNL hAL] at hnorm2
  have hcardN : Nat.card ↥(N.subgroupOf L) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hcardA : Nat.card ↥(A.subgroupOf L) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hcardY : Nat.card ↥(Y.subgroupOf L) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv
  have hcomm := commutator_le_of_sup_normal_of_coprime (X := ↥L) hp
    (N := N.subgroupOf L) (A := A.subgroupOf L) (Y := Y.subgroupOf L)
    (by rw [hcardN]; exact hN) (by rw [hcardA]; exact hA) hnorm2
    (by rw [hcardY]; exact hY) (le_normalizer_subgroupOf hAY)
  rw [commutator_subgroupOf hYL hAL] at hcomm
  exact le_of_subgroupOf_le
    ((Subgroup.le_normalizer_iff_commutator_le_left.1 hAY).trans hYL) hcomm

theorem coprime_natCard_sigmaCore [Finite G] {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hpσ : p ∉ sigmaPrimes M) : (Nat.card ↥(sigmaCore M)).Coprime p :=
  Nat.coprime_comm.1 ((hp.coprime_iff_not_dvd).2 fun hdvd => hpσ
    (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩)))

theorem sigmaCore_inf_eq_bot_of_isOutsideSigmaPlane [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G) {p : ℕ} {M A L : Subgroup G}
    (hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A) (hL : IsCoatom L) (hLM : L ≠ M)
    (hAL : A ≤ L) : sigmaCore M ⊓ L = ⊥ := by
  have := hG.isSimpleGroup
  have hp : p.Prime := hosp.prime
  have hM : IsCoatom M := hosp.isCoatom
  have hAM : A ≤ M := hosp.le
  have hAcard : Nat.card ↥A = p ^ 2 := hosp.isElementaryAbelianPlane.natCard'
  have hApg : IsPGroup p ↥A := IsPGroup.of_card hAcard
  have hMin8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hFT : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hplane8 : Prep08.IsPlaneAt p A :=
    ⟨isElementaryAbelian_of_nonempty_mulEquiv_pi hosp.isElementaryAbelianPlane, hAcard⟩
  have hplane7 : IsElementaryAbelianPlane p A := hosp.isElementaryAbelianPlane
  obtain ⟨-, hcentM, -⟩ := h₂ G hMin8 M A p hM hp hosp.notMem_sigmaPrimes hAM hplane8
  obtain ⟨A₀, hA₀A, hA₀card, hA₀norm⟩ :=
    (h₃ G hMin8 M A p hM hp hAM hplane8).2 hosp.notMem_sigmaPrimes
  obtain ⟨P, hAP, hP⟩ := exists_isSylowSubgroupOf_ge hp hAM hApg
  have hconfig : IsExceptionalPlaneConfig p M A₀ A P :=
    ⟨hM, hp, hosp.notMem_sigmaPrimes, hA₀A, hAP, hP.1, hA₀card, hplane7, hP, hA₀norm⟩
  have hsep : sigmaCore M ⊓ sigmaCore L = ⊥ := by
    by_contra hne
    exact hLM (FTS_exceptional_core_overgroup_uniqueness h₁ h₄ G hFT p M A₀ A P hconfig L hL
      hAL hne)
  suffices hJ : sigmaCore M ⊓ L ≤ centralizer ((A : Subgroup G) : Set G) from
    le_bot_iff.1 (hcentM.le.trans' (le_inf inf_le_left hJ))
  by_cases hpL : p ∈ sigmaPrimes L
  ·
    have hAS : A ≤ sigmaCore L ⊓ M :=
      le_inf (le_sigmaCore_of_isPlaneAt hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hL hpL hAL hplane8) hAM
    exact (sigmaCore_inf_le_centralizer_of_inf_sigmaCore_eq_bot hsep).trans
      (Subgroup.centralizer_le hAS)
  ·
    obtain ⟨-, -, hnormLA⟩ := h₂ G hMin8 L A p hL hp hpL hAL hplane8
    have hAJ : A ≤ normalizer ((sigmaCore M ⊓ L : Subgroup G) : Set G) :=
      le_trans (le_inf (hAM.trans (le_normalizer_sigmaCore M)) (hAL.trans Subgroup.le_normalizer))
        Subgroup.inf_normalizer_le_normalizer_inf
    have hJcop : (Nat.card ↥(sigmaCore M ⊓ L : Subgroup G)).Coprime p :=
      (coprime_natCard_sigmaCore hp hosp.notMem_sigmaPrimes).coprime_dvd_left
        (Subgroup.card_dvd_of_le inf_le_left)
    have hcomm : ⁅(sigmaCore M ⊓ L : Subgroup G), A⁆ ≤ sigmaCore L :=
      commutator_le_of_le_normalizer_sup_of_coprime hp (sigmaCore_le L) hAL inf_le_right
        (le_normalizer_sigmaCore L) hnormLA (coprime_natCard_sigmaCore hp hpL) hAcard hJcop hAJ
    have hcomm' : ⁅(sigmaCore M ⊓ L : Subgroup G), A⁆ ≤ sigmaCore M :=
      (Subgroup.le_normalizer_iff_commutator_le_left.1 hAJ).trans inf_le_left
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (le_bot_iff.1 (hsep.le.trans' (le_inf hcomm' hcomm)))

theorem FNI_outside_sigma_plane_core_disjoint
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u} := by
  intro G _ _ hG p M A L hosp hL hLM hAL
  exact sigmaCore_inf_eq_bot_of_isOutsideSigmaPlane h₁ h₂ h₃ h₄ hG hosp hL hLM hAL

end

end CFSG.FeitThompson.Proofs
