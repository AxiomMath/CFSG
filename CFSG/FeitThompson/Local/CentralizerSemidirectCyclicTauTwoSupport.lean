module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaHallCentralizerExcludesKappa
import CFSG.FeitThompson.Local.OutsideSigmaKappaCoreFixerCyclic
import CFSG.FeitThompson.Local.SignalizerRegularActionFromBase
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

theorem le_normalizer_sigmaCore_inf_centralizer (M H : Subgroup G) :
    M ⊓ centralizer (H : Set G) ≤
      normalizer ((sigmaCore M ⊓ centralizer (H : Set G) : Subgroup G) : Set G) :=
  le_trans
    (le_inf (inf_le_left.trans (le_normalizer_sigmaCore M))
      (inf_le_right.trans le_normalizer))
    (normalizer_inf_le_normalizer_inf _ _)

theorem isHallSubgroup_subgroupOf_sigmaCore_inf_centralizer
    (hS : IsHallPiSubgroup (sigmaPrimes M) (sigmaCore M)) :
    IsHallSubgroup (sigmaPrimes M) ((sigmaCore M ⊓ centralizer (H : Set G)).subgroupOf
      (M ⊓ centralizer (H : Set G))) := by
  have hSM : sigmaCore M ≤ M := sigmaCore_le M
  have hDeq : sigmaCore M ⊓ centralizer (H : Set G)
      = sigmaCore M ⊓ (M ⊓ centralizer (H : Set G)) := by rw [← inf_assoc, inf_eq_left.2 hSM]
  have hDC : sigmaCore M ⊓ centralizer (H : Set G) ≤ M ⊓ centralizer (H : Set G) := by
    rw [hDeq]; exact inf_le_right
  constructor
  · rw [natCard_subgroupOf_of_le hDC]
    exact isPiNumber_iff.2 fun p hp => isPiSubgroup_iff.1 hS.isPiSubgroup p
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hp)
  · refine isPiNumber_iff.2 fun p hp => ?_
    have hdvd : (sigmaCore M ⊓ (M ⊓ centralizer (H : Set G))).relIndex
        (M ⊓ centralizer (H : Set G)) ∣ (sigmaCore M).index :=
      relIndex_inf_dvd_index hSM inf_le_left
    rw [← hDeq] at hdvd
    exact hS.notMem_of_mem_primeFactors_index p
      (Nat.primeFactors_mono hdvd Subgroup.index_ne_zero_of_finite hp)

theorem exists_isCyclic_tauTwoPrimes_internalSemidirectProduct_centralizer
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₆ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsOddOrderMinimalSimple G)
    {M H : Subgroup G} {π : Set ℕ} (hM : IsCoatom M) (hHbot : H ≠ ⊥)
    (hHall : IsHallPiSubgroupOf π H (sigmaCore M)) :
    ∃ X : Subgroup G, X ≤ M ⊓ centralizer (H : Set G) ∧ IsCyclic ↥X ∧
      IsPiSubgroup (tauTwoPrimes M) X ∧
      FreeCore.IsInternalSemidirectProduct (M ⊓ centralizer (H : Set G))
        (sigmaCore M ⊓ centralizer (H : Set G)) X := by
  have _i := hG.isSimpleGroup
  have hsolv := hG.isSolvable_of_ne_top
  obtain ⟨-, hSHallG, -⟩ := @h₁ G _ (Fintype.ofFinite G) hG M hM
  have hSM : sigmaCore M ≤ M := sigmaCore_le M
  set C : Subgroup G := M ⊓ centralizer (H : Set G) with hCdef
  have hCM : C ≤ M := inf_le_left
  have hCtop : C ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hCM))
  have _i : Group.IsSolvable ↥C := hsolv _ hCtop
  have hDeq : sigmaCore M ⊓ centralizer (H : Set G) = sigmaCore M ⊓ C := by
    rw [hCdef, ← inf_assoc, inf_eq_left.2 hSM]
  have hDC : sigmaCore M ⊓ centralizer (H : Set G) ≤ C := by rw [hDeq]; exact inf_le_right
  have hHallD := isHallSubgroup_subgroupOf_sigmaCore_inf_centralizer (H := H) hSHallG
  obtain ⟨X₀, hX₀⟩ := exists_isHallSubgroup (X := ↥C) (sigmaPrimes M)ᶜ
  set X : Subgroup G := X₀.map C.subtype with hXdef
  have hXC : X ≤ C := Subgroup.map_subtype_le _
  have hXsub : X.subgroupOf C = X₀ :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective X₀
  obtain ⟨hsup, hinf⟩ := sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl hDC hXC hHallD
    (by rw [hXsub]; exact hX₀) (hXC.trans (le_normalizer_sigmaCore_inf_centralizer M H))
  have hsemi : FreeCore.IsInternalSemidirectProduct C
      (sigmaCore M ⊓ centralizer (H : Set G)) X :=
    ⟨hsup, le_normalizer_sigmaCore_inf_centralizer M H, disjoint_iff.2 hinf⟩
  have hXσ : ∀ p ∈ (Nat.card ↥X).primeFactors, p ∉ sigmaPrimes M := fun p hp =>
    isPiNumber_iff.1 hX₀.natCard p (by rwa [← hXsub, natCard_subgroupOf_of_le hXC])
  have hXκ : ∀ p ∈ (Nat.card ↥X).primeFactors, p ∉ kappaPrimes M := fun p hp =>
    @FBG_sigma_hall_centralizer_excludes_kappa h₁ h₃ h₄ h₆ G _ (Fintype.ofFinite G) hG M hM π H
      hHbot hHall p (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hXC) Nat.card_pos.ne' hp)
  have hXπ : IsPiSubgroup ((sigmaPrimes M ∪ kappaPrimes M)ᶜ) X :=
    isPiSubgroup_iff.2 fun p hp => by
      simp only [Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨hXσ p hp, hXκ p hp⟩
  have hHX : H ≤ sigmaCore M ⊓ centralizer (X : Set G) :=
    le_inf hHall.le (le_centralizer_of_le_centralizer
      (hXC.trans (inf_le_right : C ≤ centralizer (H : Set G))))
  have hCX : sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥ := fun h =>
    hHbot (le_bot_iff.1 (h ▸ hHX))
  obtain ⟨hXcyc, hXτ⟩ := isCyclic_and_isPiSubgroup_tauTwoPrimes h₂ h₅ hG hM
    (hXC.trans hCM) hXπ hCX
  exact ⟨X, hXC, hXcyc, hXτ, hsemi⟩

theorem FBG_sigma_hall_centralizer_cyclic_complement
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₆ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FBG_sigma_hall_centralizer_cyclic_complement.{u} := by
  intro G _ _ hG M hM π H hHbot hHall
  exact exists_isCyclic_tauTwoPrimes_internalSemidirectProduct_centralizer h₁ h₂ h₃ h₄ h₅ h₆ hG
    hM hHbot hHall

end

end CFSG.FeitThompson.Proofs
