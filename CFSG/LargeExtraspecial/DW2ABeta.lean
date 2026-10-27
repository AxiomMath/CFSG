module

public import CFSG.LargeExtraspecial.DW2ASp
public import CFSG.LargeExtraspecial.DW2ATwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem finrank_le_width_of_le_perp {W : Submodule (ZMod 2) S.Qt} (hWW : W ≤ perp S W) :
    finrank (ZMod 2) W ≤ S.width := by
  have h := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  rw [S.finrank_Qt_eq_two_mul_width] at h
  change finrank (ZMod 2) (perp S W) = _ at h
  have := Submodule.finrank_mono hWW
  omega

variable [IsSimpleGroup G]

theorem width_le_finrank_spanD_of_nondeg (hn : 2 ≤ S.width) (hP : NondegWeaklyClosed S)
    (hWs : ∀ v ∈ spanD S, S.q v = 0) {g₀ : G}
    (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG) (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z) :
    S.width ≤ finrank (ZMod 2) (spanD S) := by
  by_contra hlt
  push Not at hlt
  by_cases hsp : finrank (ZMod 2) (spanD S) ≤ finrank (ZMod 2) (axisD S g₀) + 1
  · refine false_of_sp_of_nondeg hWs (fun h hQ hz => ?_) hn hP hlt hg₀Q hg₀
    rw [← finrank_axisD_eq hWs hg₀Q hg₀ hQ hz]
    exact hsp
  have h1 := (finrank_axisD_le_one_or hWs hlt hg₀Q hg₀).resolve_right hsp
  refine false_of_axisD_eq_span_of_nondeg hn hP hWs hlt ?_ (fun h hQ hz => ?_) hg₀Q hg₀
  · have hne : axisD S g₀ ≠ ⊥ := (Submodule.ne_bot_iff _).mpr
      ⟨_, cl_mem_axisD_self hg₀Q, (cl_ne_zero_iff hg₀Q).mpr hg₀⟩
    have hpos := Submodule.one_le_finrank_iff.mpr hne
    omega
  · have hdim : finrank (ZMod 2) (axisD S h) ≤ 1 := by
      rw [← finrank_axisD_eq hWs hg₀Q hg₀ hQ hz]
      exact h1
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact cl_mem_axisD_self hQ
    · rw [finrank_span_singleton ((cl_ne_zero_iff hQ).mpr hz)]
      exact hdim

theorem perp_spanD_eq_of_nondeg (hn : 2 ≤ S.width) (hP : NondegWeaklyClosed S)
    (hWs : ∀ v ∈ spanD S, S.q v = 0) {g₀ : G}
    (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG) (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z) :
    perp S (spanD S) = spanD S := by
  have hD := width_le_finrank_spanD_of_nondeg hn hP hWs hg₀Q hg₀
  have h := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (spanD S)
  rw [S.finrank_Qt_eq_two_mul_width] at h
  change finrank (ZMod 2) (perp S (spanD S)) = _ at h
  refine (Submodule.eq_of_le_of_finrank_le (le_perp_of_forall_q hWs) ?_).symm
  omega

theorem finrank_eq_width_of_spanD_singular_of_nondeg (hn : 2 ≤ S.width)
    (hP : NondegWeaklyClosed S)
    (hWs : ∀ v ∈ spanD S, S.q v = 0) {g₀ : G} (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG)
    (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z) {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W)
    (hWsing : ∀ v ∈ W, S.q v = 0) (hW0 : W ≠ ⊥) : finrank (ZMod 2) W = S.width := by
  have hWW : W ≤ perp S W := le_perp_of_forall_q hWsing
  refine le_antisymm (finrank_le_width_of_le_perp hWW) ?_
  by_contra hlt
  push Not at hlt
  have hDW : spanD S ≤ perp S W := by
    rw [spanD, Submodule.span_le]
    rintro _ ⟨h, hQ, rfl⟩
    exact cl_conj_mem_perp hW hWW hlt hQ
  have hWD : W ≤ spanD S := by
    have := LinearMap.BilinForm.orthogonal_le (B := S.q.polarBilin) hDW
    change perp S (perp S W) ≤ perp S (spanD S) at this
    rwa [perp_perp, perp_spanD_eq_of_nondeg hn hP hWs hg₀Q hg₀] at this
  have heq := eq_spanD_of_isMbarInvariant isMbarInvariant_spanD hDQ_spanD hWs hW hWD hW0
  have hD := width_le_finrank_spanD_of_nondeg hn hP hWs hg₀Q hg₀
  rw [← heq] at hD
  omega

end CFSG.LargeExtraspecial.DW
