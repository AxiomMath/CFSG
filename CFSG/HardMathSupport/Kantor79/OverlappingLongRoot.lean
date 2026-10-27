module

public import CFSG.HardMathSupport.Kantor79.LongRootGroup
public import CFSG.ClassicalGroups.Orthogonal.RootGroupChar

public section

namespace CFSG.HardMathSupport.Kantor79

open CFSG.HardMathSupport.GuralnickMalle
open CFSG.ClassicalGroups.Orthogonal QuadraticMap LinearMap Module

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

theorem siegelEquiv_apply_eq_self_of_mem_span {Q : QuadraticForm K E} {a b u : E}
    (ha : Q a = 0) (hb : Q b = 0) (hab : QuadraticMap.polarBilin Q a b = 0)
    (humem : u ∈ Submodule.span K ({a, b} : Set E)) (c : K) :
    siegelEquiv Q a b ha hb hab c u = u := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp humem
  rw [map_add, map_smul, map_smul, siegelEquiv_apply, siegelEquiv_apply,
    siegelLin_apply_self_left Q a b ha hab c, siegelLin_apply_self_right Q a b hb hab c]

theorem siegelEquiv_mem_orthogonalGroup {Q : QuadraticForm K E} {a b : E}
    (ha : Q a = 0) (hb : Q b = 0) (hab : QuadraticMap.polarBilin Q a b = 0) (c : K) :
    siegelEquiv Q a b ha hb hab c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [siegelEquiv_apply]
  exact siegelLin_isometry Q a b ha hb hab c x

theorem siegelEquiv_apply_sub_self {Q : QuadraticForm K E} {a b : E}
    (ha : Q a = 0) (hb : Q b = 0) (hab : QuadraticMap.polarBilin Q a b = 0) (c : K) (v : E) :
    siegelEquiv Q a b ha hb hab c v - v =
      c • (polar Q v b • a) + c • (polar Q v a • b) := by
  rw [siegelEquiv_apply, siegelLin_apply]
  change v + c • (polar Q v b • a) + c • (polar Q v a • b) - v =
    c • (polar Q v b • a) + c • (polar Q v a • b)
  abel


theorem siegelEquiv_mem_rootGroup [FiniteDimensional K E] {Q : QuadraticForm K E}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {a b u : E} (ha : Q a = 0) (hb : Q b = 0)
    (hab : QuadraticMap.polarBilin Q a b = 0) (hu : Q u = 0) (hu0 : u ≠ 0)
    (humem : u ∈ Submodule.span K ({a, b} : Set E)) (c : K) :
    siegelEquiv Q a b ha hb hab c ∈ rootGroup Q u := by
  rw [mem_rootGroup_iff hQ hu hu0]
  refine ⟨siegelEquiv_mem_orthogonalGroup ha hb hab c,
    siegelEquiv_apply_eq_self_of_mem_span ha hb hab humem c, ?_⟩
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp humem
  have hu' : α • a + β • b ≠ 0 := hu0
  intro v hv
  have hv' : α * polar Q v a + β * polar Q v b = 0 := by
    have h := hv
    rw [polar_add_right, polar_smul_right, polar_smul_right] at h
    simpa [smul_eq_mul] using h
  have hform := siegelEquiv_apply_sub_self ha hb hab c v
  by_cases hα : α = 0
  · have hβ : β ≠ 0 := by
      intro hβ
      apply hu'
      rw [hα, hβ, zero_smul, zero_smul, add_zero]
    have hvb : polar Q v b = 0 := by
      have h := hv'
      rw [hα, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hβ
    refine ⟨c * (polar Q v a / β), ?_⟩
    rw [hform, hvb, hα]
    simp only [zero_smul, smul_zero, zero_add]
    rw [smul_smul, smul_smul]
    congr 1
    field_simp [hβ]
  · have hva : polar Q v a = (β / α) * polar Q v b := by
      have h : α * polar Q v a = β * polar Q v b := by
        have h := hv'
        have := eq_neg_of_add_eq_zero_left h
        rwa [CharTwo.neg_eq] at this
      field_simp [hα]
      rw [mul_comm (polar Q v a) α]
      exact h
    refine ⟨c * (polar Q v b / α), ?_⟩
    rw [hform, hva, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    · field_simp [hα]
    · field_simp [hα]

theorem longRootGroup_le_rootGroup [FiniteDimensional K E] {Q : QuadraticForm K E}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {a b u : E} (ha : Q a = 0) (hb : Q b = 0)
    (hab : QuadraticMap.polarBilin Q a b = 0) (hu : Q u = 0) (hu0 : u ≠ 0)
    (humem : u ∈ Submodule.span K ({a, b} : Set E)) :
    longRootGroup Q a b ha hb hab ≤ rootGroup Q u := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_longRootGroup_iff.mp hg
  exact siegelEquiv_mem_rootGroup hQ ha hb hab hu hu0 humem c

theorem longRootGroup_comm_of_common [FiniteDimensional K E] {Q : QuadraticForm K E}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {a b a' b' u : E}
    (ha : Q a = 0) (hb : Q b = 0) (hab : QuadraticMap.polarBilin Q a b = 0)
    (ha' : Q a' = 0) (hb' : Q b' = 0) (hab' : QuadraticMap.polarBilin Q a' b' = 0)
    (hu : Q u = 0) (hu0 : u ≠ 0) (humem : u ∈ Submodule.span K ({a, b} : Set E))
    (humem' : u ∈ Submodule.span K ({a', b'} : Set E)) {g h : E ≃ₗ[K] E}
    (hg : g ∈ longRootGroup Q a b ha hb hab) (hh : h ∈ longRootGroup Q a' b' ha' hb' hab') :
    g * h = h * g :=
  rootGroup_commute (longRootGroup_le_rootGroup hQ ha hb hab hu hu0 humem hg)
    (longRootGroup_le_rootGroup hQ ha' hb' hab' hu hu0 humem' hh)

end CFSG.HardMathSupport.Kantor79
