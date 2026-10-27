module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaCandidatePrimeCollapse
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Local.ZGroupSubgroupQuotient
import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct
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

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem coprime_natCard_of_isHallPiOf_compl [Finite G] {π : Set ℕ} {X Y Z : Subgroup G}
    (hX : Prep03.IsHallPiOf πᶜ X Z) (hY : Prep03.IsHallPiOf π Y Z) :
    (Nat.card ↥X).Coprime (Nat.card ↥Y) := by
  rw [← Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne', Finset.disjoint_left]
  intro r hr hr'
  exact hX.2.1 r hr (hY.2.1 r hr')

theorem isCyclic_of_isPGroup_of_isHallPiOf_kappaPrimes [Finite G] {q : ℕ} {W X Q : Subgroup G}
    (h : Prep03.IsHallPiOf (kappaPrimes W) X W) (hq : q.Prime) (hQX : Q ≤ X)
    (hQ : IsPGroup q ↥Q) : IsCyclic ↥Q := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hQb : Q = ⊥
  · rw [hQb]; infer_instance
  · have hdvd : q ∣ Nat.card ↥X := by
      obtain ⟨n, hn⟩ := hQ.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hQb (Subgroup.card_eq_one.1 (by simpa using hn))
      refine dvd_trans ?_ (Subgroup.card_dvd_of_le hQX)
      rw [hn]
      exact dvd_pow_self q hn0
    have hqk : q ∈ kappaPrimes W :=
      h.2.1 q (Nat.mem_primeFactors.2 ⟨hq, hdvd, Nat.card_pos.ne'⟩)
    exact isCyclic_of_isPGroup_of_mem_kappaPrimes hq hqk (hQX.trans h.1) hQ

theorem isZGroup_of_isHallPiOf_kappaPrimes [Finite G] {W X : Subgroup G}
    (h : Prep03.IsHallPiOf (kappaPrimes W) X W) : IsZGroup ↥X := by
  rw [isZGroup_iff]
  intro q hq P
  have : Fact q.Prime := ⟨hq⟩
  have hmapP : IsPGroup q ↥((P : Subgroup ↥X).map X.subtype) :=
    P.isPGroup'.of_equiv
      (Subgroup.equivMapOfInjective (P : Subgroup ↥X) X.subtype X.subtype_injective)
  have hle : (P : Subgroup ↥X).map X.subtype ≤ X := map_subtype_le _
  exact (isCyclic_map_subtype_iff _).1
    (isCyclic_of_isPGroup_of_isHallPiOf_kappaPrimes h hq hle hmapP)

theorem isCyclic_of_isDirect [Finite G] {X Y W : Subgroup G} (h : Prep03.IsDirect X Y W)
    (hY : IsCyclic ↥Y) (hW : IsCyclic ↥W) (hcop : (Nat.card ↥Y).Coprime (Nat.card ↥W)) :
    IsCyclic ↥X := by
  obtain ⟨-, -, hsup, hinf, hcomm⟩ := h
  have hc : ∀ x ∈ Y, ∀ y ∈ W, Commute x y := by
    intro x hx y hy
    exact ((mem_centralizer_iff.1
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) hx)) y hy).symm
  have hcoe : (X : Set G) = (Y : Set G) * (W : Set G) := by
    rw [← hsup]; exact coe_sup_eq_mul_of_commute hc
  have : IsCyclic (↥Y × ↥W) := Group.isCyclic_prod_iff.2 ⟨hY, hW, hcop⟩
  exact (MulEquiv.isCyclic (mulEquivProdOfCoeEqMul hcoe hinf hc)).1 inferInstance

theorem FNI_kappa_candidate_cyclic_torus
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_candidate_family_common_factors.{u})
    (h₃ : Statements.FNI_kappa_candidate_has_nontrivial_residual.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_kappa_candidate_cyclic_torus.{u} := by
  intro G _ _ M K A Z I KT hsetup
  obtain ⟨V, hVI, W, hWI, hVW, hIeq, U, hU, hsemiV, hsemiUK, hKVprime, hnil, hAWeq, hAVeq⟩ :=
    FNI_kappa_candidate_prime_collapse h₁ h₂ h₃ h₄ h₅ h₆ h₇ G M K A Z I KT hsetup
  obtain ⟨-, -, hfam, -⟩ := h₂ G M K A Z I hsetup.base hsetup.I_eq
  obtain ⟨-, hAprops, -⟩ := hfam KT hsetup.KT_self hsetup.KT_hall
  have hMI : M ∈ I := by rw [hsetup.I_eq]; exact Or.inl rfl
  have hA : A = Prep03.kappaA KT M := by
    rw [Prep03.kappaA, hsetup.KT_self, hsetup.base.A_eq]
  have : Fact (Nat.card ↥(KT V)).Prime := ⟨hKVprime⟩
  have hKVcyc : IsCyclic ↥(KT V) := isCyclic_of_prime_card rfl
  have hAVnil : Group.IsNilpotent ↥(Prep03.kappaA KT V) :=
    isNilpotent_of_le_of_isNilpotent inf_le_left hnil
  have hAVcyc : IsCyclic ↥(Prep03.kappaA KT V) :=
    isZGroup_iff_isCyclic_of_isNilpotent.1
      (by rw [hAVeq]; exact isZGroup_of_isHallPiOf_kappaPrimes (isHallPiOf_KT hsetup hWI))
  have hVpack := hAprops V hVI
  have hZcyc : IsCyclic ↥Z :=
    isCyclic_of_isDirect hVpack.2.1 hKVcyc hAVcyc
      (coprime_natCard_of_isHallPiOf_compl hVpack.2.2.2.2.1 hVpack.2.2.2.2.2.2.1)
  have hMpack := hAprops M hMI
  have hKZ : K ≤ Z := by
    have h := hMpack.2.1.1
    rwa [hsetup.KT_self] at h
  have hAZ : A ≤ Z := by rw [hA]; exact hMpack.2.1.2.1
  refine ⟨hZcyc, Subgroup.isCyclic_of_le hKZ, Subgroup.isCyclic_of_le hAZ, ?_, ?_⟩
  ·
    rw [hIeq] at hMI
    rcases hMI with hMV | hMW
    · refine ⟨W, by rw [hIeq, hMV], ?_, ?_, Or.inl ⟨U, hU, ?_, ?_⟩⟩
      · rw [hA, hMV, hAVeq]
      · rw [hAWeq, ← hMV, hsetup.KT_self]
      · rw [← hMV, hsetup.KT_self] at hsemiV; exact hsemiV
      · rw [← hMV, hsetup.KT_self] at hsemiUK; exact hsemiUK
    · rw [Set.mem_singleton_iff] at hMW
      refine ⟨V, by rw [hIeq, hMW, Set.pair_comm], ?_, ?_, Or.inr ⟨U, hU, hsemiV, hsemiUK⟩⟩
      · rw [hA, hMW, hAWeq]
      · rw [hAVeq, ← hMW, hsetup.KT_self]
  ·
    intro hno
    have hMV : M ≠ V := by
      rintro rfl
      rw [hsetup.KT_self] at hsemiV hsemiUK
      exact hno ⟨U, hU, hsemiV, hsemiUK⟩
    have hMW : M = W := by
      rw [hIeq] at hMI
      rcases hMI with h | h
      · exact absurd h hMV
      · exact Set.mem_singleton_iff.1 h
    rw [hA, hMW, hAWeq]
    exact hKVprime

end

end CFSG.FeitThompson.Proofs
