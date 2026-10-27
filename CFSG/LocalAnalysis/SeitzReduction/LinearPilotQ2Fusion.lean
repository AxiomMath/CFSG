module

public import CFSG.LocalAnalysis.SeitzReduction.FusionGenericAutU2
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwo
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvection
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_transvection_twoSided_two (hset : SeitzSetting G L) {n : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃ (x : G) (z : L), x⁻¹ * t * x = t * (z : G) ∧ IsInvolutionClass 1 (e z) ∧
      (z : G) ∈ CFSG.conjugate L x ∧
      (∃ hz : x * (z : G) * x⁻¹ ∈ L, IsInvolutionClass 1 (e ⟨x * (z : G) * x⁻¹, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * (z : G)⁻¹ := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  have hKt := inf_centralizer_eq_zpowers hset e hK1 hn htC ht
  have hOut := (SeitzQ2.card_outer_le_two_of_mulEquiv_PSL_two (by omega) hK e).2
  have hU : ∀ (U : Sylow 2 L) {z : L}, z ≠ 1 → (∀ u ∈ (U : Subgroup L), u * z = z * u) →
      IsInvolutionClass 1 (e z) := fun U _ hz1 hz =>
    isInvolutionClass_one_of_commute_sylow_of_mulEquiv (by omega) e U hz1 hz
  have hnot := not_forall_commute_sylow_of_isInvolutionClass_one hset hn hK1 e hU htC ht
  obtain ⟨x, z, ⟨hzL, hzLx⟩, hxz, hz1, ⟨U, hUz⟩, ⟨U', hU'z⟩, hact⟩ :=
    SeitzQ2.exists_conj_eq_mul_twoCentral_twoSided hset.standardSetting hOut ht hKt hnot
      (fun U β hβ => mem_range_conj_of_fix_sylow_of_mulEquiv (by omega) e U β hβ)
  have hzL1 : (⟨z, hzL⟩ : L) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hxzL : x * z * x⁻¹ ∈ L := SeitzQ2.mem_conjugate_iff_conj_mem.1 hzLx
  set e' : CFSG.conjugate L x ≃* projectiveSL n K := (conjugateMulEquiv L x).symm.trans e
    with he'
  have he'z : e' ⟨z, hzLx⟩ = e ⟨x * z * x⁻¹, hxzL⟩ := by
    rw [he', MulEquiv.trans_apply]
    congr 1
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_conjugateMulEquiv]
    group
  have hz'1 : (⟨z, hzLx⟩ : CFSG.conjugate L x) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hcl' := isInvolutionClass_one_of_commute_sylow_of_mulEquiv (by omega) e' U' hz'1
    (fun u hu => Subtype.ext (hU'z u hu))
  rw [he'z] at hcl'
  exact ⟨x, ⟨z, hzL⟩, hxz, hU U hzL1 (fun u hu => Subtype.ext (hUz u hu)), hzLx,
    ⟨hxzL, hcl'⟩, hact⟩

end CFSG.SeitzReduction.LinearPilot
