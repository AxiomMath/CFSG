module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.OppositeSupportingKernelNormBound
import CFSG.FeitThompson.Local.OrderedFieldPairOrderEstimates
import CFSG.FeitThompson.Local.TypeIISupportingMaximumExcludesPair
import CFSG.FeitThompson.Local.OppositeKernelNumericalContradiction
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace OppositeSupportingKernelEquality

open Subgroup _root_.CFSG.FeitThompson

universe u

theorem main
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_type_II_supporting_maximal_configuration.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FCH_actual_paired_support_saturation.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_opposite_supporting_kernel_equality.{u} := by
  intro G _ _ hG S T U V W₁ W₂ p q hpair M hM hVM
  have _iF : Fintype G := Fintype.ofFinite G
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG5 : Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsetup := hpair.base
  have hp : Nat.card ↥W₂ = p := hsetup.natCard_W₂
  have hq : Nat.card ↥W₁ = q := hsetup.natCard_W₁
  set K := hallCoreIn M with hKdef
  obtain ⟨hMI, hVK, -, -, -, -, hgrowth⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_opposite_supporting_kernel_growth h₂ h₅ h₆ G hG S T U V W₁ W₂
      p q hpair M hM hVM
  obtain ⟨-, -, -, -, hu2q, hv2p, -, -, hvpq⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_ordered_field_pair_order_estimates h₅ h₆ G hG S T U V W₁ W₂
      p q hsetup
  have hKV : K = V := by
    rcases eq_or_lt_of_le hVK with h | hlt
    · exact h.symm
    · exfalso
      obtain ⟨hk, -, -⟩ := hgrowth hlt
      have hnb := _root_.CFSG.FeitThompson.Proofs.FBG_opposite_supporting_kernel_norm_bound
        h₂ h₃ h₄ h₅ h₆ G hG S T U V W₁ W₂ p q hpair M hM hVM hlt
      have hu0 : (0 : ℝ) < (Nat.card ↥U : ℝ) := by
        exact_mod_cast Nat.card_pos (α := ↥U)
      have hv0 : (0 : ℝ) < (Nat.card ↥V : ℝ) := by
        exact_mod_cast Nat.card_pos (α := ↥V)
      have hk0 : (0 : ℝ) < (Nat.card ↥K : ℝ) := by
        exact_mod_cast Nat.card_pos (α := ↥K)
      have huR : 2 * (q : ℝ) < (Nat.card ↥U : ℝ) := by exact_mod_cast hu2q
      have hvR : 2 * (p : ℝ) < (Nat.card ↥V : ℝ) := by exact_mod_cast hv2p
      have hvpqR : (p : ℝ) * q + 1 ≤ (Nat.card ↥V : ℝ) := by exact_mod_cast hvpq
      have hkR : 2 * (p : ℝ) * (Nat.card ↥V : ℝ) < (Nat.card ↥K : ℝ) := by exact_mod_cast hk
      have hnum := oppositeKernel_numerical_contradiction hsetup.prime_p hsetup.prime_q
        hsetup.odd_p hsetup.odd_q hsetup.lt hu0 hv0 hk0 huR hvR hvpqR hkR
      have hnbR : 1 / (p : ℝ) + 1 / (q : ℝ) ≤
          (p : ℝ) * q / (Nat.card ↥K : ℝ) + 2 / ((p : ℝ) * q) +
            1 / ((Nat.card ↥U : ℝ) * q) + 1 / ((Nat.card ↥V : ℝ) * p) := by
        have h' := (Rat.cast_le (K := ℝ)).2 hnb
        push_cast at h'
        exact h'
      linarith
  have hcov : ∀ L : Subgroup G, IsCoatom L → ¬ IsTypeI L →
      (∃ g : G, L = conjSubgroup T g) ∨ (∃ g : G, L = conjSubgroup S g) := by
    intro L hL hLI
    rcases hpair.conj_of_not_isTypeI L hL hLI with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact Or.inr ⟨g⁻¹, by
        rw [← hg, _root_.CFSG.FeitThompson.Proofs.conjSubgroup_conjSubgroup_inv]⟩
    · exact Or.inl ⟨g⁻¹, by
        rw [← hg, _root_.CFSG.FeitThompson.Proofs.conjSubgroup_conjSubgroup_inv]⟩
  obtain ⟨-, ⟨E, hEne, hsdE, hfreeE⟩, -, hcompl⟩ :=
    h₂ G hG2 T S V U W₂ W₁ hsetup.isCoatom_T hsetup.isCoatom_S (Ne.symm hsetup.ne)
      hsetup.pconfig_T hsetup.pconfig_S hpair.isTypeII_T
      (by rw [sup_comm]; exact hpair.isCyclic_sup)
      (by rw [inf_comm, hpair.inf_eq, sup_comm]) hcov
      M hM hVM (hallCoreIn T) (hallCoreIn S) K rfl rfl rfl
      (Nat.card ↥W₁) (Nat.card ↥W₂) rfl rfl
  have hVT : V ≤ T := hsetup.pconfig_T.le_M_E
  have hW₂T : W₂ ≤ T := hsetup.pconfig_T.le_M_W₁
  obtain ⟨y, hyP, hcM⟩ : ∃ y ∈ hallCoreIn S,
      FreeCore.IsInternalSemidirectProduct M K (W₂ ⊔ conjSubgroup W₁ y) := by
    rcases hcompl with hc | hc
    · exfalso
      have hMT : M ≤ T := by rw [← hc.sup_eq]; exact sup_le (hKV ▸ hVT) hW₂T
      have hMeqT : M = T := by
        rcases eq_or_lt_of_le hMT with h' | h'
        · exact h'
        · exact absurd (hM.2 T h') hsetup.isCoatom_T.1
      obtain ⟨i, -, huniq⟩ := (h₁ G hG).1 T hsetup.isCoatom_T
      have h0 : localTypes T 0 := by rw [localTypes_zero]; exact hMeqT ▸ hMI
      have h1 : localTypes T 1 := by rw [localTypes_one]; exact hpair.isTypeII_T
      have hcontra : (0 : Fin 5) = 1 := by rw [huniq 0 h0, huniq 1 h1]
      exact absurd hcontra (by decide)
    · exact hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcW₁, -, -, -, -, hdpS, habS, -⟩ :=
    h₆ G hG5 S U W₁ W₂ hsetup.isCoatom_S hsetup.pconfig_S (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  have hW₂P : W₂ ≤ Prep05.hallCoreOf S := by rw [← hcW₁]; exact inf_le_left
  have habF := isMulCommutative_iff_of_setLike.1 habS
  have hPF : Prep05.hallCoreOf S ≤ Prep05.fittingOf S := hdpS.left_le
  have hyP' : y ∈ Prep05.hallCoreOf S := by
    rwa [Prep05.hallCoreOf_eq, ← hallCoreIn_eq]
  have hyc : ∀ w ∈ W₂, y * w = w * y := fun w hw =>
    habF y (hPF hyP') w (hPF (hW₂P hw))
  have heq : W₂ ⊔ conjSubgroup W₁ y = conjSubgroup (W₁ ⊔ W₂) y := by
    rw [_root_.CFSG.FeitThompson.Proofs.OppositeSupportingKernelGrowth.conjSubgroup_sup,
      _root_.CFSG.FeitThompson.Proofs.OppositeSupportingKernelGrowth.conjSubgroup_eq_self_of_forall_commute
        hyc, sup_comm]
  have hcard : Nat.card ↥(W₂ ⊔ conjSubgroup W₁ y : Subgroup G) = p * q := by
    rw [heq, _root_.CFSG.FeitThompson.Proofs.natCard_conjSubgroup,
      hsetup.pconfig_S.isInternalDirectProduct_sup.card_eq_mul, hq, hp, Nat.mul_comm]
  have he : K.relIndex M = p * q := by
    rw [relIndex_eq_natCard_of_isInternalSemidirectProduct hcM, hcard]
  have hKM : K ≤ M := hallCoreIn_le M
  have hMnK : M ≤ normalizer (K : Set G) := le_normalizer_map_subtype_hallCore M
  have hnK : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMnK
  have hfree : ∀ w ∈ (W₂ ⊔ conjSubgroup W₁ y : Subgroup G), w ≠ 1 →
      centralizerWithinElem V w = ⊥ := by
    intro w hw hw1
    have hwK : w ∉ K := by
      intro hwK
      have hmem : w ∈ K ⊓ (W₂ ⊔ conjSubgroup W₁ y) := ⟨hwK, hw⟩
      rw [hcM.inf_eq_bot, Subgroup.mem_bot] at hmem
      exact hw1 hmem
    have := hnK
    rw [centralizerWithinElem_eq, ← hKV]
    exact inf_centralizer_singleton_eq_bot_of_mem_of_notMem (E := E)
      hsdE.coe_eq_mul.symm hsdE.inf_eq_bot hfreeE (hcM.right_le hw) hwK
  exact ⟨hMI, hKV, he, y, hyP, hKV ▸ hcM, hfree⟩

end OppositeSupportingKernelEquality

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

universe u

theorem FBG_opposite_supporting_kernel_equality
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_type_II_supporting_maximal_configuration.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FCH_actual_paired_support_saturation.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_opposite_supporting_kernel_equality.{u} :=
  CFSG.FeitThompson.OppositeSupportingKernelEquality.main.{u} h₁ h₂ h₃ h₄ h₅ h₆

end

end CFSG.FeitThompson.Proofs
