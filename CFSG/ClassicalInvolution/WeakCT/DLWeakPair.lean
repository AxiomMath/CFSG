module

public import CFSG.ClassicalInvolution.WeakCT.DLWeakAgree
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.Assembly.LowTwoRank (StatedSp)

variable {K : Type} [Field K] {X : Type} [Group X]

theorem symplecticBlockPair_le_sup {W U V : Subgroup X} (h : SymplecticBlockPair K W U V) :
    W ≤ U ⊔ V := by
  obtain ⟨θ, c, hrange, -, -, hU, hV⟩ := h
  have h01 : (0 : Fin 2) ≠ 1 := zero_ne_one
  have htop : (longBlock K 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (shortBlock K h01).range.map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, sup_comm, shortBlock_sup_longBlock_eq_suppGroup h01,
      suppGroup_coords_zero_union_one]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  rw [← hrange, MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, hU, hV]

theorem symplecticBlockPair_map {Y : Type} [Group Y] {W U V : Subgroup X}
    (h : SymplecticBlockPair K W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    SymplecticBlockPair K (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, hinjL, hU, hV⟩ := h
  refine ⟨φ.comp θ, c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · exact hφ.comp hinjL
  · rw [← Subgroup.map_map, hU]
  · rw [← Subgroup.map_map, hV]

theorem symplecticBlockPair_subgroupOf {W U V J : Subgroup X} (hW : W ≤ J)
    (h : SymplecticBlockPair K W U V) :
    SymplecticBlockPair K (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  obtain ⟨θ, c, hrange, hker, hinjL, hU, hV⟩ := h
  have hJ : ∀ g, θ g ∈ J := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  refine ⟨θ.codRestrict J hJ, c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hrange]
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.codRestrict_apply, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, h⟩
      exact ⟨a, Subtype.ext h⟩
  · intro x hx
    apply hker
    simpa [MonoidHom.mem_ker, Subtype.ext_iff] using hx
  · intro x y hxy
    apply hinjL
    have := congrArg Subtype.val hxy
    simpa using this
  · rw [map_codRestrict_eq, hU]
  · rw [map_codRestrict_eq, hV]

end CFSG.ClassicalInvolution.Models.SymplecticPairs
