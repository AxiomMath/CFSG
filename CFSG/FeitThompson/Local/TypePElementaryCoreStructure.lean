module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Representations.TypeThreeFourInnerComplementCyclic
import CFSG.FeitThompson.Representations.TypeVMaximalExclusion
import CFSG.FeitThompson.Local.TypeIIIIVChiefData
import CFSG.FeitThompson.OddOrder.PConfigComplementCentralizer

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05

universe u

theorem FNI_type_p_elementary_core_structure
    (_h₁ : Statements.FBG_five_type_local_classification.{u})
    (_h₂ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : Statements.FNI_type_p_prime_factors.{u})
    (h₄ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₅ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₆ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₇ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₈ : Statements.FPF_type_iii_v_second_factor_prime.{u})
    (_h₉ : Statements.FTS_type_I_core_kappa_identity.{u}) :
    Statements.FNI_type_p_elementary_core_structure.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hc p q hp hq
  obtain ⟨hpp, hqp, hop, hoq, hne, -, -, -, -, -, -, -, htypes, -⟩ :=
    h₃ G hG M U W₁ W₂ hM hc p q hp hq
  subst hp hq
  haveI : Fintype G := Fintype.ofFinite G
  have hG6 : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have htype : IsTypeII M ∨ IsTypeIII M := by
    rcases htypes with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (FPF_type_iii_iv_inner_complement_cyclic h₄ h₅ h₆ h₇ h₈ G hG6 M U W₁ W₂ hM
        (Or.inr h) hc).2.2
    · exact absurd h (FPF_type_v_exclusion h₆ h₇ h₈ G hG6 M hM)
  obtain ⟨hcII, hUne, hUab, hiso, hcard, hCU⟩ :
      IsPConfigurationIIToIV M U W₁ W₂ ∧ U ≠ ⊥ ∧ IsMulCommutative ↥U ∧
        Nonempty (↥(hallCoreOf M) ≃*
          (Fin (Nat.card ↥W₁) → Multiplicative (ZMod (Nat.card ↥W₂)))) ∧
        Nat.card ↥(hallCoreOf M) = Nat.card ↥W₂ ^ Nat.card ↥W₁ ∧
        centralizerIn (hallCoreOf M) U = ⊥ := by
    rcases htype with h | h
    · obtain ⟨h1, h2, h3, -⟩ := h.clauses_of_isWitnessedPConfiguration_of_minimalSimple
        hG.isSimpleGroup hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hM hc
      obtain ⟨hc1, hc2⟩ := h.core_elementary_abelian_of_isWitnessedPConfiguration
        hG.isSimpleGroup hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hM hc hpp
      exact ⟨h1, h2, h3, hc2, hc1,
        h.inf_centralizer_hallCore_eq_bot_of_isWitnessedPConfiguration
          hG.isSimpleGroup hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hM hc⟩
    · obtain ⟨h1, h2, h3, -⟩ := h.clauses_of_isWitnessedPConfiguration_of_minimalSimple
        hG.isSimpleGroup hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hM hc
      obtain ⟨hi, hcd, -, hcu, -⟩ := h₄ G hG6 M U W₁ W₂ hM (Or.inl h) hc
      exact ⟨h1, h2, h3, hi, hcd, hcu⟩
  have hqprime : (Nat.card ↥W₁).Prime := hqp
  have hUle : U ≤ M := hc.le_M_E
  have hW₁le : W₁ ≤ M := hc.le_M_W₁
  have hsup : hallCoreOf M ⊔ (U ⊔ W₁) = M := by
    rw [hallCoreOf_eq, ← sup_assoc, hc.sup_hallCore_E, hc.sup_commutator_W₁]
  have hmul : ((U ⊔ W₁ : Subgroup G) : Set G) = (U : Set G) * (W₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U W₁ hc.le_normalizer_E
  have hdisjHU : Disjoint ((hallCore ↥M).map M.subtype) U := hc.disjoint_hallCore_E
  have hdisj : Disjoint (hallCoreOf M) (U ⊔ W₁) := by
    rw [hallCoreOf_eq, Subgroup.disjoint_def]
    intro x hxH hxUW
    have hx : x ∈ (U : Set G) * (W₁ : Set G) :=
      hmul ▸ (hxUW : x ∈ ((U ⊔ W₁ : Subgroup G) : Set G))
    obtain ⟨u, hu, w, hw, hxeq⟩ := hx
    have hxeq' : u * w = x := hxeq
    have hxM' : x ∈ (⁅M, M⁆ : Subgroup G) := hc.hallCore_le_commutator hxH
    have hwM' : w ∈ (⁅M, M⁆ : Subgroup G) := by
      have h := (⁅M, M⁆ : Subgroup G).mul_mem
        (Subgroup.inv_mem _ (hc.le_commutator_E hu)) hxM'
      rw [← hxeq'] at h
      simpa [mul_assoc] using h
    have hw1 : w = 1 := Subgroup.disjoint_def.1 hc.disjoint_commutator_W₁ hwM' hw
    have hxu : x = u := by rw [← hxeq', hw1, mul_one]
    rw [hxu] at hxH
    exact hxu.trans (Subgroup.disjoint_def.1 hdisjHU hxH hu)
  have hcfg := hc.isPTypeConfig hsolvM hqprime hUne
  have hcardH : Nat.card ↥(hallCoreOf M) = Nat.card ↥(hallCore ↥M) := by
    rw [hallCoreOf_eq]
    exact Subgroup.card_map_of_injective M.subtype_injective
  have hcardUW : Nat.card ↥(U.subgroupOf M ⊔ W₁.subgroupOf M) = Nat.card ↥(U ⊔ W₁) := by
    rw [← Subgroup.subgroupOf_sup hUle hW₁le]
    exact natCard_subgroupOf (sup_le hUle hW₁le)
  have hcop : Nat.Coprime (Nat.card ↥(hallCoreOf M)) (Nat.card ↥(U ⊔ W₁)) := by
    rw [hcardH, ← hcardUW]
    exact hcfg.coprime_natCard_H_sup
  have hfpf : IsFixedPointFreeOn U W₁ := by
    intro b hb hb1
    rw [centralizerIn_eq, centralizer_coe_eq_centralizer_singleton (rfl : zpowers b = zpowers b)]
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.1 hx
    have h1 : x ∈ (⁅M, M⁆ : Subgroup G) ⊓ centralizer ({b} : Set G) :=
      Subgroup.mem_inf.2 ⟨hc.le_commutator_E hxU, hxc⟩
    rw [hc.inf_centralizer_eq_W₂ b hb hb1] at h1
    exact Subgroup.mem_bot.2
      (Subgroup.disjoint_def.1 hdisjHU (hc.le_hallCore_W₂ h1) hxU)
  have hcentH : centralizerIn (hallCoreOf M) W₁ = W₂ := by
    rw [centralizerIn_eq, hallCoreOf_eq]
    refine le_antisymm ?_ (le_inf hc.le_hallCore_W₂ hc.le_centralizer_W₁)
    calc (hallCore ↥M).map M.subtype ⊓ centralizer (W₁ : Set G)
        ≤ (⁅M, M⁆ : Subgroup G) ⊓ centralizer (W₁ : Set G) :=
          inf_le_inf_right _ hc.hallCore_le_commutator
      _ = W₂ := hc.inf_centralizer_W₁_eq_W₂
  obtain ⟨hClt, hIDP, hnormC⟩ := chiefData_fitting_product hsolvM hqprime hUne hc
  have hHcomm : ∀ a ∈ hallCoreOf M, ∀ b ∈ hallCoreOf M, Commute a b := by
    intro a ha b hb
    obtain ⟨e⟩ := hiso
    have h : (⟨a, ha⟩ : ↥(hallCoreOf M)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      e.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hUab.is_comm.comm (⟨a, ha⟩ : ↥U) ⟨b, hb⟩)
  have hFab : IsMulCommutative ↥(fittingOf M) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hx : (x : G) ∈ (fittingOf M : Set G) := x.2
    have hy : (y : G) ∈ (fittingOf M : Set G) := y.2
    rw [hIDP.coe_eq_mul] at hx hy
    obtain ⟨a, ha, c, hc', hxe⟩ := hx
    obtain ⟨b, hb, d, hd, hye⟩ := hy
    change (x : G) * y = y * x
    rw [← hxe, ← hye]
    have hcU : c ∈ U := centralizerIn_le _ _ hc'
    have hdU : d ∈ U := centralizerIn_le _ _ hd
    exact (Commute.mul_left (Commute.mul_right (hHcomm a ha b hb) (hIDP.commute ha hd))
      (Commute.mul_right (hIDP.commute hb hc').symm (hUcomm c hcU d hdU))).eq
  have hminimal : ∀ N : Subgroup G, N ≤ hallCoreOf M → M ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = hallCoreOf M := by
    intro N hNH hNn
    by_cases hNeq : N = hallCoreOf M
    · exact Or.inr hNeq
    left
    set s : Set (Subgroup G) :=
      {K | M ≤ normalizer (K : Set G) ∧ N ≤ K ∧ K < hallCoreOf M} with hs
    have hsne : s.Nonempty := ⟨N, hNn, le_rfl, lt_of_le_of_ne hNH hNeq⟩
    obtain ⟨K, hKmax⟩ := s.toFinite.exists_maximal hsne
    obtain ⟨hKn, hNK, hKlt⟩ := hKmax.prop
    have hlayer : IsChiefLayer M K (hallCoreOf M) := by
      refine ⟨hKn, hKlt, fun L hLn hKL hLH => ?_⟩
      by_cases hLeq : L = hallCoreOf M
      · exact Or.inr hLeq
      · exact Or.inl (le_antisymm
          (hKmax.le_of_ge ⟨hLn, hNK.trans hKL, lt_of_le_of_ne hLH hLeq⟩ hKL) hKL)
    obtain ⟨⟨-, -, -, hrel⟩, -⟩ := chiefData_layer_elementary hsolvM hqprime hpp hUne hc _ _
      rfl rfl K (by rw [hCU]; exact bot_le) hlayer
    have hKbot : K = ⊥ := by
      have h1 := (K.subgroupOf (hallCoreOf M)).card_mul_index
      rw [natCard_subgroupOf hKlt.le] at h1
      change Nat.card ↥K * K.relIndex (hallCoreOf M) = _ at h1
      rw [hrel, hcard] at h1
      have hpos : 0 < Nat.card ↥W₂ ^ Nat.card ↥W₁ := pow_pos hpp.pos _
      exact Subgroup.card_eq_one.1 (Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact h1))
    rw [hKbot] at hNK
    exact le_bot_iff.1 hNK
  haveI : Fact (Nat.card ↥W₂).Prime := ⟨hpp⟩
  refine ⟨htype, hpp, hqp, hop, hoq, hne, hUne, hUab,
    { sup_eq := hsup
      le_normalizer := by
        rw [hallCoreOf_eq]; exact le_normalizer_map_subtype_hallCore M
      disjoint := hdisj },
    { sup_eq := rfl
      le_normalizer := sup_le Subgroup.le_normalizer hc.le_normalizer_E
      disjoint := hc.disjoint_commutator_W₁.mono_left hc.le_commutator_E },
    Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le le_sup_left) hcop)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le le_sup_right) hcop),
    hfpf, ?_, hcard, hCU, hcentH, hc.hallCore_ne_bot, hminimal, hClt, hnormC, hIDP, hFab, ?_, ?_⟩
  · obtain ⟨e⟩ := hiso
    refine ⟨ULift.{u} (Fin (Nat.card ↥W₁) → ZMod (Nat.card ↥W₂)), inferInstance, inferInstance,
      ?_, ⟨e.trans ((MulEquiv.funMultiplicative _ _).symm.trans
        (AddEquiv.toMultiplicative AddEquiv.ulift.symm))⟩⟩
    rw [LinearEquiv.finrank_eq ULift.moduleEquiv, Module.finrank_fin_fun]
  · rw [coe_hallCoreOf_sdiff]
    exact isTIWithNormalizer_hallCoreSharp_of_fittingRawSharp
      hcII.isTIWithNormalizer_fittingRawSharp hc.hallCoreSharp_nonempty
  · have h := hcII.isTIWithNormalizer_fittingRawSharp
    rwa [fittingRawSharp_eq, ← fittingOf_eq] at h

end CFSG.FeitThompson.Proofs

end
