module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
import CFSG.FeitThompson.Local.FiveTypeLocalClassification
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem centralizerWithin_eq_inf (X Y : Subgroup G) :
    centralizerWithin X Y = X ⊓ centralizer (Y : Set G) := (rfl)

theorem sup_eq_and_disjoint_of_isHallPiSubgroup [Finite G] {π : Set ℕ} {M K N : Subgroup G}
    (hKM : K ≤ M) (hNM : N ≤ M) (hnorm : K ≤ normalizer (N : Set G))
    (hHall : IsHallPiSubgroup π (K.subgroupOf M))
    (hcard : Nat.card ↥M = Nat.card ↥N * Nat.card ↥K) :
    N ⊔ K = M ∧ Disjoint N K := by
  have hidx : (K.subgroupOf M).index = Nat.card ↥N := by
    have h := Subgroup.card_mul_index (K.subgroupOf M)
    rw [natCard_subgroupOf hKM] at h
    have h2 : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥K * Nat.card ↥N := by
      rw [h, hcard, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥N) := by
    have h := hHall.coprime_natCard_index
    rwa [natCard_subgroupOf hKM, hidx] at h
  have hinf : N ⊓ K = ⊥ := by
    have hd1 : Nat.card ↥(N ⊓ K) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_right
    have hd2 : Nat.card ↥(N ⊓ K) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le inf_le_left
    exact Subgroup.card_eq_one.1 ((Nat.Coprime.coprime_dvd_left hd1 hcop).eq_one_of_dvd hd2)
  have hcoe : ((N ⊔ K : Subgroup G) : Set G) = (N : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm
  refine ⟨?_, disjoint_iff.2 hinf⟩
  have hset : Nat.card ↥(N ⊔ K : Subgroup G) = Nat.card ↥M := by
    have h := natCard_mul_mul_natCard_inf N K
    rw [hinf, ← hcoe] at h
    simpa [hcard] using h
  exact Subgroup.eq_of_le_of_card_ge (sup_le hNM hKM) (le_of_eq hset.symm)

theorem sup_commutator_eq_of_isHall [Finite G] {M W : Subgroup G} (hWM : W ≤ M)
    (hHall : IsHallPiSubgroup (kappaPrimes M) (W.subgroupOf M))
    (hcard : Nat.card ↥M = Nat.card ↥(⁅M, M⁆ : Subgroup G) * Nat.card ↥W) :
    ⁅M, M⁆ ⊔ W = M ∧ Disjoint (⁅M, M⁆ : Subgroup G) W :=
  sup_eq_and_disjoint_of_isHallPiSubgroup hWM (Subgroup.commutator_le_self M)
    (le_normalizer_commutator_self (le_trans hWM Subgroup.le_normalizer)) hHall hcard

theorem natCard_eq_natCard_commutator_mul [Finite G] {M K U : Subgroup G}
    (h : IsLocalKappaSetup M K U)
    (hprod : ((⁅M, M⁆ : Subgroup G) : Set G) = (sigmaCore M : Set G) * (U : Set G)) :
    Nat.card ↥M = Nat.card ↥(⁅M, M⁆ : Subgroup G) * Nat.card ↥K := by
  have hinf : sigmaCore M ⊓ U = ⊥ :=
    le_bot_iff.1 (le_trans (inf_le_inf_left _ le_sup_left)
      (le_of_eq h.semidirect_M.inf_eq_bot))
  have hq := natCard_mul_mul_natCard_inf (sigmaCore M) U
  rw [hinf, ← hprod] at hq
  simp only [Subgroup.card_bot, mul_one] at hq
  have hq' : Nat.card ↥(⁅M, M⁆ : Subgroup G) = Nat.card ↥(sigmaCore M) * Nat.card ↥U := by
    simpa using hq
  rw [CFSG.FeitThompson.Proofs.natCard_eq_of_isLocalKappaSetup h, hq', mul_assoc]

theorem natCard_eq_of_isHallPiSubgroupOf [Finite G] {π : Set ℕ} {A B M : Subgroup G}
    (hA : IsHallPiSubgroupOf π A M) (hB : IsHallPiSubgroupOf π B M) :
    Nat.card ↥A = Nat.card ↥B := by
  have h := CFSG.FeitThompson.Proofs.natCard_eq_of_isHallPiSubgroup hA.2 hB.2
  rwa [natCard_subgroupOf hA.1, natCard_subgroupOf hB.1] at h

theorem conj_smul_conjSubgroup (Y : Subgroup G) (g : G) :
    MulAut.conj g • conjSubgroup Y g = Y := by
  ext x
  rw [mem_conj_smul_iff, mem_conjSubgroup]
  refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hyx⟩
  exact mul_left_cancel (mul_right_cancel hyx) ▸ hy

theorem kappaPrimes_nonempty_of_ne_bot [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    (hHall : IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M)) (hKbot : K ≠ ⊥) :
    (kappaPrimes M).Nonempty := by
  rcases Set.eq_empty_or_nonempty (kappaPrimes M) with hemp | h
  · refine absurd (Subgroup.card_eq_one.1 ?_) hKbot
    have h1 : (Nat.card ↥(K.subgroupOf M)).primeFactors = ∅ := by
      ext p
      simp only [Finset.notMem_empty, iff_false]
      intro hp
      have hmem := isPiSubgroup_iff.1 hHall.isPiSubgroup p hp
      rw [hemp] at hmem
      exact hmem
    rcases Nat.primeFactors_eq_empty.1 h1 with h | h
    · exact absurd h Nat.card_pos.ne'
    · rwa [natCard_subgroupOf hKM] at h
  · exact h

theorem typeIIToV_of_existsUnique_localTypes [Finite G] {M : Subgroup G}
    (h : ∃! i : Fin 5, localTypes M i) (hI : ¬ IsTypeI M) :
    IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M := by
  obtain ⟨i, hi, -⟩ := h
  fin_cases i
  · exact absurd hi hI
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (Or.inl hi))
  · exact Or.inr (Or.inr (Or.inr hi))

theorem exists_isLocalKappaSetup [Finite G]
    (h₁ : CFSG.FeitThompson.Statements.FBG_kappa_complement_structure.{u})
    (hamb : IsFBGAmbient G) {M : Subgroup G} (hM : IsCoatom M) :
    ∃ K U : Subgroup G, IsLocalKappaSetup M K U ∧ IsCyclic ↥K := by
  obtain ⟨K, U, hKM, hcyc, hhall, hUM, hsemiM, hsemiUK, -, -⟩ := h₁ G hamb M hM
  exact ⟨K, U, ⟨hM, hKM, hhall, hUM, hsemiUK.right_le_normalizer, hsemiM, hsemiUK⟩, hcyc⟩

theorem isOddOrderMinimalSimple_of_isFBGAmbient [Finite G] (hamb : IsFBGAmbient G) :
    IsOddOrderMinimalSimple G :=
  ⟨hamb.odd_natCard, hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.isSolvable⟩

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
  Pointwise

universe u

theorem FBG_maximal_type_dichotomy
    (h₁ : Statements.FBG_kappa_complement_structure.{u})
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₆ : Statements.FBG_local_p_trivial_U_alternative.{u})
    (h₇ : Statements.FBG_local_type_I_alternative.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) :
    Statements.FBG_maximal_type_dichotomy.{u} := by
  intro G _ _ hamb
  have hFin : Fintype G := Fintype.ofFinite G
  have hoo : IsOddOrderMinimalSimple G := isOddOrderMinimalSimple_of_isFBGAmbient hamb
  have hcls := Proofs.FBG_five_type_local_classification.{u} h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ G hamb
  refine ⟨hcls.1, ?_⟩
  by_cases hall : ∀ M : Subgroup G, IsCoatom M → IsTypeI M
  · exact Or.inl hall
  refine Or.inr ?_
  simp only [not_forall] at hall
  obtain ⟨M, hM, hMI⟩ := hall
  obtain ⟨K, U, hsetup, hKcyc⟩ := exists_isLocalKappaSetup h₁ hamb hM
  have hKbot : K ≠ ⊥ := fun hk => hMI ((hcls.2 M K U hsetup).1.2 hk)
  obtain ⟨hKstarbot, hKstarcyc, -, -, hM'prod, -⟩ := h₄ G hamb M K U hsetup hKbot
  obtain ⟨Ms, hMs, hMsne, hKstarhall, -, hinf, hdir, hcycW, hTI, hexh, hlast⟩ :=
    h₈ G hoo M hM K U ⟨hsetup.le_M_K, hsetup.hall_K⟩ hsetup.le_M_U hsetup.semidirect_M
      hsetup.semidirect_UK hsetup.le_normalizer_U hKbot (centralizerWithin (sigmaCore M) K)
      (centralizerWithin_eq_inf _ _)
  obtain ⟨K', U', hsetup', -⟩ := exists_isLocalKappaSetup h₁ hamb hMs
  have hcardK' : Nat.card ↥K' = Nat.card ↥(centralizerWithin (sigmaCore M) K) :=
    natCard_eq_of_isHallPiSubgroupOf ⟨hsetup'.le_M_K, hsetup'.hall_K⟩ hKstarhall
  have hK'bot : K' ≠ ⊥ := by
    intro h
    refine hKstarbot (Subgroup.card_eq_one.1 ?_)
    rw [← hcardK', h, Subgroup.card_bot]
  obtain ⟨-, -, -, -, hMs'prod, -⟩ := h₄ G hamb Ms K' U' hsetup' hK'bot
  refine ⟨M, Ms, K, centralizerWithin (sigmaCore M) K, ?_⟩
  have hsupM := sup_commutator_eq_of_isHall hsetup.le_M_K hsetup.hall_K
    (natCard_eq_natCard_commutator_mul hsetup hM'prod)
  have hsupMs := sup_commutator_eq_of_isHall hKstarhall.1 hKstarhall.2
    (by rw [natCard_eq_natCard_commutator_mul hsetup' hMs'prod, hcardK'])
  refine
  { odd_natCard := hamb.odd_natCard
    isSimpleGroup := hamb.isSimpleGroup
    not_isMulCommutative := hamb.not_isMulCommutative
    isSolvable := hamb.isSolvable
    isCoatom_left := hM
    isCoatom_right := hMs
    ne := fun h => hMsne 1 (by rw [← h, conjSubgroup_one])
    ne_bot_left := hKbot
    ne_bot_right := hKstarbot
    isCyclic_left := hKcyc
    isCyclic_right := hKstarcyc
    isInternalDirectProduct := hinf ▸ hdir
    isCyclic_sup := hinf ▸ hcycW
    sup_commutator_left := hsupM.1
    disjoint_commutator_left := hsupM.2
    sup_commutator_right := hsupMs.1
    disjoint_commutator_right := hsupMs.2
    inf_eq := hinf
    isTIWithNormalizer := hinf ▸ hTI
    typeIIToV_left := typeIIToV_of_existsUnique_localTypes (hcls.1 M hM) hMI
    typeIIToV_right := typeIIToV_of_existsUnique_localTypes (hcls.1 Ms hMs)
      (fun h => hK'bot ((hcls.2 Ms K' U' hsetup').1.1 h))
    typeII := ?_
    conj_of_not_isTypeI := ?_ }
  · rcases hlast with hU | ⟨K'', U'', hK''hall, hU''Ms, hsemi1, hsemi2, hnorm2, hU''bot⟩
    · exact Or.inl ((hcls.2 M K U hsetup).2.1.2 ⟨hKbot, hU⟩)
    · have hsetup'' : IsLocalKappaSetup Ms K'' U'' :=
        ⟨hMs, hK''hall.1, hK''hall.2, hU''Ms, hnorm2, hsemi1, hsemi2⟩
      refine Or.inr ((hcls.2 Ms K' U' hsetup').2.1.2 ⟨hK'bot, ?_⟩)
      exact fun h => hU''bot
        ((CFSG.FeitThompson.Proofs.eq_bot_U_iff_of_isLocalKappaSetup hsetup' hsetup'').1 h)
  · intro L hL hLI
    obtain ⟨KL, UL, hsetupL, -⟩ := exists_isLocalKappaSetup h₁ hamb hL
    have hKLbot : KL ≠ ⊥ := fun hk => hLI ((hcls.2 L KL UL hsetupL).1.2 hk)
    have hκL := kappaPrimes_nonempty_of_ne_bot hsetupL.le_M_K hsetupL.hall_K hKLbot
    rcases hexh L hL hκL with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact Or.inl ⟨g, by rw [hg, conj_smul_conjSubgroup]⟩
    · exact Or.inr ⟨g, by rw [hg, conj_smul_conjSubgroup]⟩

end

end CFSG.FeitThompson.Proofs
