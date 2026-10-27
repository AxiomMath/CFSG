module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NormalizerIntersectionSylow
import CFSG.FeitThompson.Local.NoncyclicSigmaNormalizer
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormality
import CFSG.FeitThompson.Local.OppositeSigmaPlaneCoreIntersection
import CFSG.FeitThompson.Local.OutsideSigmaNormalizerRankTwoPlane
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.SecondCenterTorsionNoncyclic
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.HighRankCentralTorsionLine
import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson.Prep08

universe u

variable {G : Type*} [Group G]

theorem inf_left_eq_right_of_isInternalSemidirectProduct {X S E M : Subgroup G}
    (hX : FreeCore.IsInternalSemidirectProduct X S E) (hEM : E ≤ M) (hSM : S ⊓ M = ⊥) :
    M ⊓ X = E := by
  refine le_antisymm (fun x hx => ?_) (le_inf hEM hX.right_le)
  obtain ⟨s, hs, e, he, rfl⟩ := hX.exists_mul (Subgroup.mem_inf.1 hx).2
  have hsM : s ∈ M := by
    rw [show s = s * e * e⁻¹ by group]
    exact mul_mem (Subgroup.mem_inf.1 hx).1 (inv_mem (hEM he))
  have hs1 : s = 1 := Subgroup.mem_bot.1 (hSM ▸ Subgroup.mem_inf.2 ⟨hs, hsM⟩)
  simpa [hs1] using he

theorem FTS_normalizer_complement_plane_assembly
    (h₁ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FTS_normalizer_complement_plane_assembly.{u} := by
  intro G _ _ hG M N Q q hM hN hMN hqM hQM hQcard hNQ hqN
  have := hG.isSimpleGroup
  have hq : q.Prime := prime_of_mem_sigmaPrimes hqM
  have hQN : Q ≤ N := le_trans Subgroup.le_normalizer hNQ
  have hQMN : Q ≤ M ⊓ N := le_inf hQM hQN
  have hQcardsub : Nat.card ↥(Q.subgroupOf (M ⊓ N)) = q ^ 1 := by
    rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMN).toEquiv, hQcard]
  obtain ⟨S, hS⟩ := (IsPGroup.of_card hQcardsub).exists_le_sylow
  set T : Subgroup G := (S : Subgroup ↥(M ⊓ N)).map (M ⊓ N).subtype with hTdef
  have hTsylow : IsSylowOf q T (M ⊓ N) := ⟨S, rfl⟩
  have hQT : Q ≤ T := by
    rw [hTdef, ← Subgroup.map_subgroupOf_eq_of_le hQMN]; exact Subgroup.map_mono hS
  obtain ⟨-, hTN⟩ := FTS_normalizer_intersection_sylow h₂ G hG M N Q T q hM hN hMN hqM hQM hQcard
    hNQ hTsylow hQT
  have hTp : IsPGroup q ↥T := hTsylow.isPGroup
  have hQTcard : Nat.card ↥(Q.subgroupOf T) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv, hQcard]
  rcases characteristic_or_exists_isElementaryAbelian_natCard_eq_sq hq hTp hQTcard with
    hchar | ⟨A0, -, hA0ea, hA0card⟩
  ·
    exfalso
    have h := normalizer_le_normalizer_map_subtype T (Q.subgroupOf T)
    rw [Subgroup.map_subgroupOf_eq_of_le hQT] at h
    obtain ⟨S', hS'⟩ := hTN
    refine hqN (mem_sigmaPrimes_iff.2 ⟨hq, hQcard ▸ Subgroup.card_dvd_of_le hQN, S', ?_⟩)
    rw [hS']
    exact h.trans hNQ
  ·
    set A : Subgroup G := A0.map T.subtype with hAdef
    have hAT : A ≤ T := Subgroup.map_subtype_le _
    have hAea : IsElementaryAbelian q A := hA0ea.map_subtype
    have hAcard : Nat.card ↥A = q ^ 2 := by rw [hAdef, Subgroup.card_subtype, hA0card]
    have hplane : IsPlaneAt q A := ⟨hAea, hAcard⟩
    have hAMN : A ≤ M ⊓ N := hAT.trans hTsylow.le
    have hAM : A ≤ M := hAMN.trans inf_le_left
    have hAN : A ≤ N := hAMN.trans inf_le_right
    have hsolvN : Group.IsSolvable ↥N := hG.isSolvable_of_ne_top N hN.1
    have hApi : IsPiSubgroup (sigmaPrimes N)ᶜ (A.subgroupOf N) := by
      refine isPiSubgroup_iff.2 fun r hr => ?_
      have hcard : Nat.card ↥(A.subgroupOf N) = q ^ 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hAcard]
      rw [hcard, Nat.primeFactors_pow _ two_ne_zero, hq.primeFactors] at hr
      simpa [Finset.mem_singleton.1 hr] using hqN
    obtain ⟨H, hHhall, hAH⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hApi
    set E : Subgroup G := H.map N.subtype with hEdef
    have hEN : E ≤ N := Subgroup.map_subtype_le _
    have hEsub : E.subgroupOf N = H :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    have hAE : A ≤ E := by
      rw [hEdef, ← Subgroup.map_subgroupOf_eq_of_le hAN]; exact Subgroup.map_mono hAH
    have hHallS : IsHallSubgroup (sigmaPrimes N) ((sigmaCore N).subgroupOf N) :=
      isHallSubgroup_subgroupOf_sigmaCore hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hN
    obtain ⟨hsup, hinf⟩ := sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl (sigmaCore_le N) hEN
      hHallS (hEsub ▸ hHhall) (hEN.trans (le_normalizer_sigmaCore N))
    have hsemi : FreeCore.IsInternalSemidirectProduct N (sigmaCore N) E :=
      ⟨hsup, le_normalizer_sigmaCore N, disjoint_iff.2 hinf⟩
    have hEnormA : E ≤ normalizer ((A : Subgroup G) : Set G) :=
      FTS_outside_sigma_plane_complement_normality h₁ G hG N A E q hN hq hqN hAN hplane hEN
        hsemi hAE
    have hAnc : ¬ IsCyclic ↥A :=
      not_isCyclic_of_natCard_eq_sq_of_exponent hq hAcard fun x hx => hAea.pow_eq_one hx
    have hEM : E ≤ M :=
      hEnormA.trans (FTS_noncyclic_sigma_normalizer h₂ G hG M A q hM hqM hAM hAea.isPGroup hAnc)
    have hcore : sigmaCore N ⊓ M = ⊥ :=
      FTS_opposite_sigma_plane_core_intersection h₁ G hG M N A q hM hN hqM hqN hAMN hplane
    rw [inf_left_eq_right_of_isInternalSemidirectProduct hsemi hEM hcore]
    exact hsemi

end

end CFSG.FeitThompson.Proofs
