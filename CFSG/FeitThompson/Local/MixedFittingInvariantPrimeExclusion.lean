module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.CentralRankThreeConstrainedTransitivity
import CFSG.FeitThompson.Local.SubnormalConstrainedTransitivity
import CFSG.FeitThompson.Local.FiniteNilpotentSubnormal
import CFSG.FeitThompson.Local.MaximalNormalizedPSubgroupSingletonTrivial

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] [Finite G] {p q : ℕ} {M E : Subgroup G}

theorem exists_maximalNormalizedPSubgroups_eq_singleton_of_constrainedCentralizerCore_eq_bot
    {A : Subgroup G} (hK : constrainedCentralizerCore A = ⊥)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    ∃ Q : Subgroup G, maximalNormalizedPSubgroups A q = {Q} := by
  obtain ⟨Q, hQ⟩ := maximalNormalizedPSubgroups_nonempty A q
  refine ⟨Q, Set.eq_singleton_iff_unique_mem.2 ⟨hQ, fun R hR => ?_⟩⟩
  obtain ⟨k, hk, hkeq⟩ := hconj Q hQ R hR
  rw [hK, Subgroup.mem_bot] at hk
  subst hk
  simpa using hkeq.symm

theorem natCard_mixedFitting (M : Subgroup G) :
    Nat.card ↥(mixedFitting M) = Nat.card ↥(fittingRaw ↥M) := by
  rw [mixedFitting_eq]
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).toEquiv).symm

namespace IsMixedFittingSetup

variable (h : IsMixedFittingSetup p M E)

include h

theorem subgroupPrimeSupport_mixedFittingCentralizer :
    subgroupPrimeSupport (mixedFittingCentralizer M E)
      = subgroupPrimeSupport (mixedFitting M) := by
  rw [subgroupPrimeSupport_def, subgroupPrimeSupport_def, h.primeFactors_mixedFittingCentralizer]

theorem mixedFittingCentralizer_ne_bot : mixedFittingCentralizer M E ≠ ⊥ := by
  intro hb
  have h2 := h.two_le_card_primeFactors
  rw [← h.primeFactors_mixedFittingCentralizer, hb] at h2
  simp at h2

theorem bot_lt_mixedFittingCentralizer : ⊥ < mixedFittingCentralizer M E :=
  bot_lt_iff_ne_bot.2 h.mixedFittingCentralizer_ne_bot

theorem mixedFitting_lt_top : mixedFitting M < ⊤ :=
  lt_of_le_of_lt (mixedFitting_le M) (lt_top_iff_ne_top.2 h.ne_top)

theorem mixedFittingCentralizer_lt_top : mixedFittingCentralizer M E < ⊤ :=
  lt_of_le_of_lt (mixedFittingCentralizer_le M E) h.mixedFitting_lt_top

theorem isPiSubgroup_mixedFitting :
    IsPiSubgroup (subgroupPrimeSupport (mixedFittingCentralizer M E)) (mixedFitting M) := by
  rw [h.subgroupPrimeSupport_mixedFittingCentralizer]
  exact isPiSubgroup_subgroupPrimeSupport _

theorem exists_le_inf_centralizer_mulEquiv_cube :
    ∃ D : Subgroup G, D ≤ mixedFittingCentralizer M E ⊓
        centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G) ∧
      Nonempty (↥D ≃* Multiplicative (Fin 3 → ZMod p)) := by
  obtain ⟨H, ⟨f⟩⟩ := mem_elementaryAbelianRanks.1 h.three_mem_ranks
  refine ⟨H.map E.subtype, ?_, ⟨?_⟩⟩
  · rw [← centreIn_eq]
    exact (Subgroup.map_subtype_le H).trans h.le_centreIn_mixedFittingCentralizer
  · exact ((Subgroup.equivMapOfInjective H E.subtype E.subtype_injective).symm.trans f).trans
      (MulEquiv.piMultiplicative _).symm

theorem constrainedCentralizerCore_eq_bot [IsSimpleGroup G] :
    constrainedCentralizerCore (mixedFittingCentralizer M E) = ⊥ := by
  rw [constrainedCentralizerCore_eq, subgroupPrimeSupportCompl_mixedFittingCentralizer h,
    h.piCore_centralizer_eq_bot, Subgroup.map_bot]

theorem exists_mem_constrainedCentralizerCore_conj_inv_smul_eq [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hq : q ∈ subgroupPrimeSupportCompl (mixedFitting M)) :
    ∀ Q₁ ∈ maximalNormalizedPSubgroups (mixedFittingCentralizer M E) q,
      ∀ Q₂ ∈ maximalNormalizedPSubgroups (mixedFittingCentralizer M E) q,
        ∃ k ∈ constrainedCentralizerCore (mixedFittingCentralizer M E),
          (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂ := by
  obtain ⟨D, hD, hDcube⟩ := h.exists_le_inf_centralizer_mulEquiv_cube
  intro Q₁ hQ₁ Q₂ hQ₂
  refine exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_rank_three_le_centre
    hsolv h.bot_lt_mixedFittingCentralizer h.mixedFittingCentralizer_lt_top
    (h.isConstrained_mixedFittingCentralizer hna hodd hsolv)
    (mem_subgroupPrimeSupportCompl_iff.1 hq).1 ?_ h.prime hD hDcube hQ₁ hQ₂
  rw [h.subgroupPrimeSupport_mixedFittingCentralizer]
  exact (mem_subgroupPrimeSupportCompl_iff.1 hq).2

theorem exists_maximalNormalizedPSubgroups_eq_singleton [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hq : q ∈ subgroupPrimeSupportCompl (mixedFitting M)) :
    ∃ Q : Subgroup G, maximalNormalizedPSubgroups (mixedFittingCentralizer M E) q = {Q} :=
  exists_maximalNormalizedPSubgroups_eq_singleton_of_constrainedCentralizerCore_eq_bot
    h.constrainedCentralizerCore_eq_bot
    (h.exists_mem_constrainedCentralizerCore_conj_inv_smul_eq hna hodd hsolv hq)

theorem maximalNormalizedPSubgroups_mixedFitting_subset [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hq : q ∈ subgroupPrimeSupportCompl (mixedFitting M)) {Q : Subgroup G}
    (hsing : maximalNormalizedPSubgroups (mixedFittingCentralizer M E) q = {Q})
    (hcon : IsConstrained (mixedFittingCentralizer M E)) :
    maximalNormalizedPSubgroups (mixedFitting M) q
      ⊆ maximalNormalizedPSubgroups (mixedFittingCentralizer M E) q := by
  have hqT : q ∉ subgroupPrimeSupport (mixedFittingCentralizer M E) := by
    rw [h.subgroupPrimeSupport_mixedFittingCentralizer]
    exact (mem_subgroupPrimeSupportCompl_iff.1 hq).2
  refine maximalNormalizedPSubgroups_subset_of_isSubnormal hna hsolv
    h.bot_lt_mixedFittingCentralizer hcon (mem_subgroupPrimeSupportCompl_iff.1 hq).1 hqT
    (mixedFittingCentralizer_le M E) h.mixedFitting_lt_top h.isPiSubgroup_mixedFitting
    (isSubnormal_of_finite_of_isNilpotent _) fun Q₁ hQ₁ Q₂ hQ₂ => ?_
  rw [hsing, Set.mem_singleton_iff] at hQ₁ hQ₂
  exact ⟨1, one_mem _, by simp [hQ₁, hQ₂]⟩

theorem eq_bot_of_isPGroup_of_le_normalizer_mixedFittingCentralizer [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hq : q ∈ subgroupPrimeSupportCompl (mixedFitting M)) {Q : Subgroup G} (hQ : IsPGroup q ↥Q)
    (hTQ : mixedFittingCentralizer M E ≤ normalizer (Q : Set G)) : Q = ⊥ := by
  have hqp := (mem_subgroupPrimeSupportCompl_iff.1 hq).1
  have hcon := h.isConstrained_mixedFittingCentralizer hna hodd hsolv
  obtain ⟨Q₀, hsing⟩ := h.exists_maximalNormalizedPSubgroups_eq_singleton hna hodd hsolv hq
  have hsub := h.maximalNormalizedPSubgroups_mixedFitting_subset hna hsolv hq hsing hcon
  have hFsing : maximalNormalizedPSubgroups (mixedFitting M) q = {Q₀} := by
    obtain ⟨R, hR⟩ := maximalNormalizedPSubgroups_nonempty (mixedFitting M) q
    refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun S hS => ?_⟩
    · have hRQ : R = Q₀ := by have := hsub hR; rwa [hsing, Set.mem_singleton_iff] at this
      exact hRQ ▸ hR
    · have := hsub hS; rwa [hsing, Set.mem_singleton_iff] at this
  have hqF : ¬ q ∣ Nat.card ↥(fittingRaw ↥M) := by
    rw [← natCard_mixedFitting]
    exact fun hdvd => (mem_subgroupPrimeSupportCompl_iff.1 hq).2
      (mem_subgroupPrimeSupport_iff.2 (Nat.mem_primeFactors.2 ⟨hqp, hdvd, Nat.card_pos.ne'⟩))
  have hQ₀ : Q₀ = ⊥ := eq_bot_of_maximalNormalizedPSubgroups_eq_singleton hna hqp h.isCoatom
    (le_normalizer_mixedFitting M) hqF hFsing
  obtain ⟨R, hR, hQR⟩ := exists_mem_maximalNormalizedPSubgroups_ge hQ hTQ
  rw [hsing, Set.mem_singleton_iff] at hR
  exact le_bot_iff.1 (hQR.trans (hR ▸ hQ₀).le)

end IsMixedFittingSetup

end

end CFSG.FeitThompson
