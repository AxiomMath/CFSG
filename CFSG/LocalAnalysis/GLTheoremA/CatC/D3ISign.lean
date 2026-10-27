module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Lang.D4Three.BorelLayers
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FCoord

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
open scoped commutatorElement

section Sign

variable {K : Type} [Field K] [Finite K]


theorem borelScalar_s_eq {g : ModGL Tag.D4 K} (hg : BorelScalar g) {α : D4Vec}
    (hα : IsRoot Tag.D4 α ∧ 0 < height α) :
    hg.s α = rootCoord hα (g * pinnedX Tag.D4 K α 1 * g⁻¹) := by
  have h := hg.spec.2 α hα (pinnedX Tag.D4 K α 1) (pinnedX_mem_heightSeries_height hα 1)
  rw [h, rootCoord_self hα, mul_one]

theorem borelScalar_sq {g : ModGL Tag.D4 K} (hg : BorelScalar g) (hg2 : g * g = 1) {α : D4Vec}
    (hα : IsRoot Tag.D4 α ∧ 0 < height α) : hg.s α * hg.s α = 1 := by
  set x := pinnedX Tag.D4 K α 1 with hx
  have hxm : x ∈ heightSeries Tag.D4 K (height α) := pinnedX_mem_heightSeries_height hα 1
  have hym : g * x * g⁻¹ ∈ heightSeries Tag.D4 K (height α) :=
    (Subgroup.mem_normalizer_iff.1 (hg.1 (height α)) x).1 hxm
  have h1 := hg.spec.2 α hα (g * x * g⁻¹) hym
  have h2 := hg.spec.2 α hα x hxm
  have hginv : g⁻¹ = g := (eq_inv_of_mul_eq_one_left hg2).symm
  have h3 : g * (g * x * g⁻¹) * g⁻¹ = x := by
    rw [hginv]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg2]; simp
  rw [h3, h2, rootCoord_self hα] at h1
  linear_combination -h1

theorem pc_conj_pinnedX {g : ModGL Tag.D4 K} (hg : BorelScalar g) {γ γ' : D4Vec}
    (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ) (hγ' : γ' ∈ d4RootsAt (height γ)) :
    pc γ' (g * pinnedX Tag.D4 K γ 1 * g⁻¹) = if γ' = γ then hg.s γ else 0 := by
  obtain ⟨h1, h2⟩ := mem_d4RootsAt.1 hγ'
  have hpos : IsRoot Tag.D4 γ' ∧ 0 < height γ' := ⟨h1, by rw [h2]; exact hγ.2⟩
  have hxm : pinnedX Tag.D4 K γ 1 ∈ heightSeries Tag.D4 K (height γ') := by
    rw [h2]; exact pinnedX_mem_heightSeries_height hγ 1
  rw [pc_of_pos hpos, hg.spec.2 γ' hpos _ hxm]
  by_cases hc : γ' = γ
  · subst hc
    rw [rootCoord_self hpos, if_pos rfl, mul_one]
  · rw [if_neg hc, rootCoord_pinnedX_of_ne hpos hγ (by rw [h2]) (Ne.symm hc), mul_zero]

theorem borelScalar_add {g : ModGL Tag.D4 K} (hg : BorelScalar g) {γ δ : D4Vec}
    (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ) (hδ : IsRoot Tag.D4 δ ∧ 0 < height δ)
    (hβ : IsRoot Tag.D4 (γ + δ)) : hg.s (γ + δ) = hg.s γ * hg.s δ := by
  have hβ' : IsRoot Tag.D4 (γ + δ) ∧ 0 < height (γ + δ) :=
    ⟨hβ, by rw [d4_height_add]; have := hγ.2; have := hδ.2; omega⟩
  have hτ : Tag.D4 = .D4 ∨ Tag.D4 = .E6 ∨ Tag.D4 = .E7 ∨ Tag.D4 = .E8 := Or.inl rfl
  have hne : γ ≠ δ := fun h => by
    subst h
    exact d4_not_isRoot_double hγ.1 hβ
  have hneg : γ ≠ -δ := fun h => by
    have h1 := hγ.2
    have h2 := hδ.2
    rw [h, height_neg] at h1
    omega
  obtain ⟨h1, -⟩ := simply_laced_root_commutator_unit.{0} Tag.D4 hτ hγ.1 hδ.1 hne hneg
  obtain ⟨hC, -⟩ := h1 hβ
  have hCne : (commConst Tag.D4 γ δ (1, 1) : K) ≠ 0 := by
    rcases hC with h | h <;> rw [h] <;> simp
  set X := pinnedX Tag.D4 K γ 1 with hX
  set Y := pinnedX Tag.D4 K δ 1 with hY
  have hXm : X ∈ heightSeries Tag.D4 K (height γ) := pinnedX_mem_heightSeries_height hγ 1
  have hYm : Y ∈ heightSeries Tag.D4 K (height δ) := pinnedX_mem_heightSeries_height hδ 1
  have hcomm : ⁅X, Y⁆ ∈ heightSeries Tag.D4 K (height (γ + δ)) := by
    rw [d4_height_add]
    exact commutator_heightSeries_le K _ _ (Subgroup.commutator_mem_commutator hXm hYm)
  have hcoord : rootCoord hβ' ⁅X, Y⁆ = (commConst Tag.D4 γ δ (1, 1) : K) := by
    have := rootCoord_commutator_pinnedX_d4 hγ hδ hβ' (by rw [d4_height_add]) (1 : K) 1
    rw [if_pos rfl] at this
    simpa using this
  have hL := hg.spec.2 (γ + δ) hβ' ⁅X, Y⁆ hcomm
  rw [hcoord] at hL
  have hconj : g * ⁅X, Y⁆ * g⁻¹ = ⁅g * X * g⁻¹, g * Y * g⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hconj] at hL
  have hzm : g * X * g⁻¹ ∈ heightSeries Tag.D4 K (height γ) :=
    (Subgroup.mem_normalizer_iff.1 (hg.1 _) X).1 hXm
  have hwm : g * Y * g⁻¹ ∈ heightSeries Tag.D4 K (height δ) :=
    (Subgroup.mem_normalizer_iff.1 (hg.1 _) Y).1 hYm
  have hpair := rootCoord_commutator_pair (K := K) hγ.2 hδ.2 hzm hwm hβ' (d4_height_add γ δ)
  rw [hpair] at hL
  have hγm : γ ∈ d4RootsAt (height γ) := mem_d4RootsAt.2 ⟨hγ.1, rfl⟩
  have hδm : δ ∈ d4RootsAt (height δ) := mem_d4RootsAt.2 ⟨hδ.1, rfl⟩
  rw [Finset.sum_eq_single γ (fun γ' hγ' hne' => by
      refine Finset.sum_eq_zero fun δ' _ => ?_
      rw [pc_conj_pinnedX hg hγ hγ', if_neg hne']
      simp) (fun h => absurd hγm h),
    Finset.sum_eq_single δ (fun δ' hδ' hne' => by
      rw [pc_conj_pinnedX hg hδ hδ', if_neg hne']
      simp) (fun h => absurd hδm h),
    pc_conj_pinnedX hg hγ hγm, pc_conj_pinnedX hg hδ hδm] at hL
  simp only [if_true] at hL
  have : (commConst Tag.D4 γ δ (1, 1) : K) * (hg.s (γ + δ) - hg.s γ * hg.s δ) = 0 := by
    linear_combination -hL
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hCne)

end Sign

end CFSG.LocalAnalysis.GLTheoremA
