module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TypeINonfrobeniusWitness
import CFSG.FeitThompson.Representations.TypeISupportingCaseContradiction
import CFSG.FeitThompson.Representations.TypeIWitnessSupportingFrobenius
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow
import CFSG.FeitThompson.OddOrder.TypeISmallerPrimeFrobenius
import CFSG.FeitThompson.OddOrder.FullExponentSubgroupCyclicSylow

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem dvd_natCard_hallCoreOf_of_two_le_elementaryAbelianPRank
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPF_non_type_i_supporting_maximum_exclusion.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (G : Type u) [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) :
    ∀ p : ℕ, p.Prime → ∀ Y : Subgroup G, IsCoatom Y → IsTypeI Y →
      2 ≤ elementaryAbelianPRank p ↥Y → p ∣ Nat.card ↥(hallCoreOf Y) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp Y hY hYI hYrank
    by_contra hpK
    obtain ⟨P, hPY, hPcard⟩ := exists_subgroup_le_natCard_eq_pow_factorization hp Y
    obtain ⟨hPcomm, hPrank, L, hL, x, hxP, hxord, hPsig, hCK, hnorm, hcent⟩ :=
      FPF_type_i_nonfrobenius_witness h₇ h₉ G hG Y hY hYI p hp hYrank hpK P ⟨hPY, hPcard⟩
    have hx1 : x ≠ 1 := by
      intro h; rw [h, orderOf_one] at hxord; exact hp.one_lt.ne' hxord.symm
    by_cases hLI : IsTypeI L
    ·
      exact FPF_type_i_supporting_case_contradiction h₂ h₄ h₅ h₆ h₇ h₈ h₉ G hG p hp
        (fun q hq hqp Z hZ hZI hZrank => ih q hqp hq Z hZ hZI hZrank) Y L hY hL hYI hLI hpK
        P hPcomm ⟨hPY, hPcard⟩ hPrank hPsig x hxP hxord hCK hnorm hcent
    ·
      have hGA : IsFBGAmbient G :=
        ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
      obtain ⟨i, hi, -⟩ := (h₁ G hGA).1 L hL
      have htypes : IsTypeII L ∨ IsTypeIII L ∨ IsTypeIV L ∨ IsTypeV L := by
        match i, hi with
        | 0, hi => exact absurd hi hLI
        | 1, hi => exact Or.inl hi
        | 2, hi => exact Or.inr (Or.inl hi)
        | 3, hi => exact Or.inr (Or.inr (Or.inl hi))
        | 4, hi => exact Or.inr (Or.inr (Or.inr hi))
      exact h₃ G hG L hL htypes p ((Nat.card ↥Y).factorization p) hp P hPsig hPcard
        (not_isCyclic_of_elementaryAbelianPRank_eq_two hp hPrank) x hxP hx1 hcent

theorem exists_free_complement_of_isTypeI {G : Type u} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → ∀ Y : Subgroup G, IsCoatom Y → IsTypeI Y →
      2 ≤ elementaryAbelianPRank q ↥Y → q ∣ Nat.card ↥(hallCoreOf Y))
    {L : Subgroup G} (hL : IsCoatom L) (hLI : IsTypeI L) :
    ∃ E : Subgroup G, E ≤ L ∧ E ≠ ⊥ ∧
      FreeCore.IsInternalSemidirectProduct L (hallCoreOf L) E ∧
      IsFixedPointFreeOn (hallCoreOf L) E := by
  have hoddL : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  obtain ⟨E, hE⟩ := hLI.exists_frobenius
  obtain ⟨E₀, hE₀E, hexp, hfree⟩ := hE.exists_exponent_eq
  have hsmall : ∀ q : ℕ, q.Prime → q < Nat.card ↥E + 1 →
      2 ∈ elementaryAbelianRanks q ↥L → q ∣ Nat.card ↥(hallCore ↥L) := by
    intro q hq _ hplane
    have h := hrank q hq L hL hLI (le_elementaryAbelianPRank hq.one_lt hplane)
    rwa [natCard_hallCoreOf_eq] at h
  have hlt : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E → q < Nat.card ↥E + 1 := fun q _ hqE =>
    Nat.lt_succ_of_le (Nat.le_of_dvd Nat.card_pos hqE)
  have _hZ : IsZGroup ↥E := isZGroup_of_forall_prime_lt hoddL hE.coprime_card hlt hsmall
  have hexpU0 : Monoid.exponent ↥(E₀.subgroupOf E) = Monoid.exponent ↥E := by
    rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE₀E)]
    exact hexp
  have hEE₀ : E ≤ E₀ := Subgroup.subgroupOf_eq_top.mp (eq_top_of_exponent_eq_of_isZGroup hexpU0)
  exact ⟨E.map L.subtype, Subgroup.map_subtype_le _, map_subtype_ne_bot_of_ne_bot hE.ne_bot,
    isInternalSemidirectProduct_hallCoreOf_map hE.isComplement',
    isFixedPointFreeOn_map_subtype (fun u hu hu1 => hfree u (hEE₀ hu) hu1)⟩

theorem FPF_type_I_frobenius
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPF_non_type_i_supporting_maximum_exclusion.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u} := by
  intro G _ _ hG L hL hLI
  exact exists_free_complement_of_isTypeI hG.odd_natCard
    (dvd_natCard_hallCoreOf_of_two_le_elementaryAbelianPRank h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ G hG)
    hL hLI

end CFSG.FeitThompson.Proofs

end
