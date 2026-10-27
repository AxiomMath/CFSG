module

public import CFSG.CharacterTheory.DihedralTIFusion.SupportSum
public import CFSG.CharacterTheory.OddOrderBasics.Induction

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

open TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem ti_conj_not_mem {D : Set G} {L : Subgroup G} (hTI : IsTISubset D L) :
    ∀ d ∈ D, ∀ c : G, c ∉ L → c⁻¹ * d * c ∉ D := by
  intro d hd c hc hcd
  apply hc
  have hmem := ti_mem_of_conj_mem hTI hd (g := c⁻¹) (by simpa using hcd)
  simpa using L.inv_mem hmem

theorem inducedFunction_eq_zero_off_conjugates {D : Set G} {L : Subgroup G} {α : L → ℂ}
    (hαD : ∀ x : L, (x : G) ∉ D → α x = 0) {g : G}
    (hg : g ∉ ⋃ a : G, (fun y => a⁻¹ * y * a) '' D) : inducedFunction L α g = 0 :=
  inducedFunction_eq_zero_of_support_avoids_conjugates L D α hαD g fun c hc =>
    hg (mem_iUnion_conj_image_iff.mpr ⟨c⁻¹, by simpa using hc⟩)

theorem inducedFunction_eq_of_mem_ti {D : Set G} {L : Subgroup G} (hTI : IsTISubset D L)
    {α : L → ℂ} (hα : BlocksIsClassFunction α) (hαD : ∀ x : L, (x : G) ∉ D → α x = 0)
    (d : L) (hd : (d : G) ∈ D) : inducedFunction L α d = α d :=
  inducedFunction_eq_on_trivial_intersection_support L D α (fun x c => hα x c) hαD
    (ti_conj_not_mem hTI) d hd

theorem inducedFunction_isClassFunction (L : Subgroup G) (α : L → ℂ) :
    BlocksIsClassFunction (inducedFunction L α) :=
  fun g h => inducedFunction_conjugate L α g h

theorem ti_supported_induction_isometry {D : Set G} {L : Subgroup G} (hTI : IsTISubset D L)
    {α β : L → ℂ} (hα : BlocksIsClassFunction α) (hβ : BlocksIsClassFunction β)
    (hαD : ∀ x : L, (x : G) ∉ D → α x = 0) (hβD : ∀ x : L, (x : G) ∉ D → β x = 0) :
    (∀ g ∉ ⋃ a : G, (fun y => a⁻¹ * y * a) '' D, inducedFunction L α g = 0) ∧
      (∀ d : L, (d : G) ∈ D → inducedFunction L α d = α d) ∧
      BlocksInnerProduct (inducedFunction L α) (inducedFunction L β) =
        BlocksInnerProduct α β := by
  refine ⟨fun g hg => inducedFunction_eq_zero_off_conjugates hαD hg,
    inducedFunction_eq_of_mem_ti hTI hα hαD, ?_⟩
  rw [blocksInnerProduct_inducedFunction_left L α _ (inducedFunction_isClassFunction L β)]
  unfold BlocksInnerProduct
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : (x : G) ∈ D
  · simp only [inducedFunction_eq_of_mem_ti hTI hβ hβD x hx]
  · rw [hαD x hx, zero_mul, zero_mul]

theorem supported_virtual_induction_data {D : Set G} {H : Subgroup G} (hTI : IsTISubset D H)
    {φ : H → ℂ} (hφ : φ ∈ BlocksVChar H) (hφD : ∀ x : H, (x : G) ∉ D → φ x = 0) :
    inducedFunction H φ ∈ BlocksVChar G ∧
      (∀ g ∉ ⋃ a : G, (fun y => a⁻¹ * y * a) '' D, inducedFunction H φ g = 0) ∧
      BlocksInnerProduct (inducedFunction H φ) (inducedFunction H φ) =
        BlocksInnerProduct φ φ ∧
      BlocksInnerProduct (inducedFunction H φ) 1 = BlocksInnerProduct φ 1 := by
  have hclass := blocksVChar_isClassFunction hφ
  obtain ⟨h1, -, h3⟩ := ti_supported_induction_isometry hTI hclass hclass hφD hφD
  refine ⟨(OddOrderBasics.induction_preserves_characters H).2 φ hφ, h1, h3, ?_⟩
  rw [blocksInnerProduct_inducedFunction_left H φ 1 (fun _ _ => rfl)]
  rfl

end CFSG.DihedralTIFusion
