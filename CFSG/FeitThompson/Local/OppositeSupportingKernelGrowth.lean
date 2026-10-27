module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.OrderedFieldPairOrderEstimates
import CFSG.FeitThompson.Local.TypeIISupportingMaximumExcludesPair
import CFSG.FeitThompson.Local.AllTypeIKernelPartition
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

universe u

namespace OppositeSupportingKernelGrowth

variable {G : Type*} [Group G]

theorem conjSubgroup_eq_self_of_forall_commute {Y : Subgroup G} {y : G}
    (h : ∀ w ∈ Y, y * w = w * y) : conjSubgroup Y y = Y := by
  ext x
  rw [mem_conjSubgroup]
  refine ⟨?_, fun hx => ⟨x, hx, ?_⟩⟩
  · rintro ⟨w, hw, rfl⟩
    have hc : y⁻¹ * w * y = w := by
      calc y⁻¹ * w * y = y⁻¹ * (w * y) := by group
        _ = y⁻¹ * (y * w) := by rw [← h w hw]
        _ = w := by group
    rwa [hc]
  · calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x) := by rw [← h x hx]
      _ = x := by group

theorem conjSubgroup_sup (Y Z : Subgroup G) (g : G) :
    conjSubgroup (Y ⊔ Z) g = conjSubgroup Y g ⊔ conjSubgroup Z g := by
  rw [conjSubgroup_eq, conjSubgroup_eq, conjSubgroup_eq, Subgroup.map_sup]

end OppositeSupportingKernelGrowth

open OppositeSupportingKernelGrowth

theorem FBG_opposite_supporting_kernel_growth
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_type_II_supporting_maximal_configuration.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_opposite_supporting_kernel_growth.{u} := by
  intro G _ _ hG S T U V W₁ W₂ p q hpair M hM hVM
  have _iF : Fintype G := Fintype.ofFinite G
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG5 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsetup := hpair.base
  have hp : Nat.card ↥W₂ = p := hsetup.natCard_W₂
  have hq : Nat.card ↥W₁ = q := hsetup.natCard_W₁
  set K := hallCoreIn M with hKdef
  have hcov : ∀ L : Subgroup G, IsCoatom L → ¬ IsTypeI L →
      (∃ g : G, L = conjSubgroup T g) ∨ (∃ g : G, L = conjSubgroup S g) := by
    intro L hL hLI
    rcases hpair.conj_of_not_isTypeI L hL hLI with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact Or.inr ⟨g⁻¹, by rw [← hg, conjSubgroup_conjSubgroup_inv]⟩
    · exact Or.inl ⟨g⁻¹, by rw [← hg, conjSubgroup_conjSubgroup_inv]⟩
  obtain ⟨hMI, ⟨E, hEne, hsdE, hfreeE⟩, hVK, hcompl⟩ :=
    h₁ G hG2 T S V U W₂ W₁ hsetup.isCoatom_T hsetup.isCoatom_S (Ne.symm hsetup.ne)
      hsetup.pconfig_T hsetup.pconfig_S hpair.isTypeII_T
      (by rw [sup_comm]; exact hpair.isCyclic_sup)
      (by rw [inf_comm, hpair.inf_eq, sup_comm]) hcov
      M hM hVM (hallCoreIn T) (hallCoreIn S) K rfl rfl rfl
      (Nat.card ↥W₁) (Nat.card ↥W₂) rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcW₁, -, -, -, -, hdpS, habS, -⟩ :=
    h₃ G hG5 S U W₁ W₂ hsetup.isCoatom_S hsetup.pconfig_S (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  have hW₂P : W₂ ≤ CFSG.FeitThompson.Prep05.hallCoreOf S := by rw [← hcW₁]; exact inf_le_left
  have habF := isMulCommutative_iff_of_setLike.1 habS
  have hPF : CFSG.FeitThompson.Prep05.hallCoreOf S ≤ CFSG.FeitThompson.Prep05.fittingOf S := hdpS.left_le
  have key : ∃ C : Subgroup G, FreeCore.IsInternalSemidirectProduct M K C ∧
      W₂ ≤ C ∧ (Nat.card ↥C = p ∨ Nat.card ↥C = p * q) := by
    rcases hcompl with hc | ⟨y, hyQ, hc⟩
    · exact ⟨W₂, hc, le_rfl, Or.inl hp⟩
    · refine ⟨W₂ ⊔ conjSubgroup W₁ y, hc, le_sup_left, Or.inr ?_⟩
      have hyc : ∀ w ∈ W₂, y * w = w * y := fun w hw => habF y (hPF hyQ) w (hPF (hW₂P hw))
      have heq : W₂ ⊔ conjSubgroup W₁ y = conjSubgroup (W₁ ⊔ W₂) y := by
        rw [conjSubgroup_sup, conjSubgroup_eq_self_of_forall_commute hyc, sup_comm]
      rw [heq, natCard_conjSubgroup,
        hsetup.pconfig_S.isInternalDirectProduct_sup.card_eq_mul, hq, hp, Nat.mul_comm]
  obtain ⟨C, hsdC, hW₂C, hCcard⟩ := key
  have he : K.relIndex M = Nat.card ↥C := relIndex_eq_natCard_of_isInternalSemidirectProduct hsdC
  have hKM : K ≤ M := hallCoreIn_le M
  have hMnK : M ≤ normalizer (K : Set G) := le_normalizer_map_subtype_hallCore M
  have hnK : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMnK
  have hW₂M : W₂ ≤ M := hW₂C.trans hsdC.right_le
  have hfreeW₂ : ∀ w ∈ W₂, w ≠ 1 → K ⊓ centralizer ({w} : Set G) = ⊥ := by
    intro w hw hw1
    have hwK : w ∉ K := by
      intro hwK
      have hmem : w ∈ K ⊓ C := ⟨hwK, hW₂C hw⟩
      rw [hsdC.inf_eq_bot, Subgroup.mem_bot] at hmem
      exact hw1 hmem
    have := hnK
    exact inf_centralizer_singleton_eq_bot_of_mem_of_notMem (E := E)
      hsdE.coe_eq_mul.symm hsdE.inf_eq_bot hfreeE (hW₂M hw) hwK
  have hfreeW₂' : ∀ w ∈ W₂, w ≠ 1 → centralizer ({w} : Set G) ⊓ K = ⊥ := by
    intro w hw hw1; rw [inf_comm]; exact hfreeW₂ w hw hw1
  have hW₂nV : W₂ ≤ normalizer (V : Set G) := hsetup.pconfig_T.le_normalizer_E
  refine ⟨hMI, hVK, by rw [he]; exact hCcard, hW₂M.trans hMnK, hW₂nV,
    fun w hw hw1 => hfreeW₂ w hw hw1, fun hlt => ?_⟩
  have hk : 2 * p * Nat.card ↥V < Nat.card ↥K :=
    two_mul_mul_natCard_lt_natCard hG.odd_natCard hsetup.prime_p hsetup.odd_p hlt
      (hW₂M.trans hMnK) hW₂nV hp hfreeW₂'
  have hepos : 0 < Nat.card ↥C := Nat.card_pos
  have hele : Nat.card ↥C ≤ p * q := by
    rcases hCcard with h | h
    · rw [h]
      have := hsetup.prime_q.one_lt
      nlinarith [hsetup.prime_p.pos]
    · rw [h]
  have hR := sub_one_div_lt_sub_one_div hG.odd_natCard hsetup.prime_p hsetup.odd_p
    hsetup.prime_q hsetup.odd_q hsetup.lt hlt (hW₂M.trans hMnK) hW₂nV hp hfreeW₂' hepos hele
  obtain ⟨-, -, -, -, -, -, -, hUV, -⟩ :=
    FBG_ordered_field_pair_order_estimates h₂ h₃ G hG S T U V W₁ W₂ p q hsetup
  refine ⟨hk, hUV, ?_⟩
  rw [he]
  have hcast : ((((Nat.card ↥V : ℚ) - 1) / (p : ℚ) : ℚ) : ℝ) <
      ((((Nat.card ↥K : ℚ) - 1) / (Nat.card ↥C : ℚ) : ℚ) : ℝ) := by
    push_cast
    exact hR
  exact_mod_cast hcast

end

end CFSG.FeitThompson.Proofs
