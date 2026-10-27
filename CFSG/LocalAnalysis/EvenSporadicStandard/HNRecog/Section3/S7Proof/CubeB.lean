module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.CubeBE

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_cube_B {a z : G} (H : S7Hyps a z) {E : Subgroup G} (hE : IsElemTwo 3 E)
    (hV : ∃ u ∈ E, ∃ v ∈ E, u ≠ v ∧ IsConj a u ∧ IsConj a v ∧ IsConj a (u * v)) :
    (∀ w ∈ E, w ≠ 1 → IsConj a w ∨ IsConj z w) ∧
    ({w : G | w ∈ E ∧ IsConj z w}.ncard = 1 ∨ {w : G | w ∈ E ∧ IsConj z w}.ncard = 3) := by
  obtain ⟨g, b, t, hb, ht, ht2, ht1, hmap⟩ := H.pic.self.cube_conj E hE hV
  obtain ⟨hcl, hcard⟩ := s7_cubeB_explicit H hb ht ht2 ht1
  let φ : G ≃* G := MulAut.conj g
  have hφinj : Function.Injective φ := φ.injective
  have hmem : ∀ w : G, w ∈ E ↔ φ w ∈ Subgroup.closure ({a, b, t} : Set G) := by
    intro w
    rw [← hmap, Subgroup.mem_map]
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨x, hx, hxw⟩
      have : x = w := hφinj hxw
      rwa [this] at hx
  have hconj : ∀ w : G, IsConj w (φ w) := fun w => isConj_iff.mpr ⟨g, rfl⟩
  constructor
  · intro w hwE hw1
    have hwcl : φ w ∈ Subgroup.closure ({a, b, t} : Set G) := (hmem w).mp hwE
    have hwne : φ w ≠ 1 := by
      intro h
      exact hw1 (hφinj (by rw [h, map_one]))
    rcases hcl (φ w) hwcl hwne with ha | hz
    · exact Or.inl (ha.trans (IsConj.symm (hconj w)))
    · exact Or.inr (hz.trans (IsConj.symm (hconj w)))
  · have himg : φ '' {w : G | w ∈ E ∧ IsConj z w} =
        {w : G | w ∈ Subgroup.closure ({a, b, t} : Set G) ∧ IsConj z w} := by
      ext y
      constructor
      · rintro ⟨w, ⟨hwE, hzw⟩, rfl⟩
        exact ⟨(hmem w).mp hwE, hzw.trans (hconj w)⟩
      · rintro ⟨hycl, hzy⟩
        refine ⟨φ.symm y, ⟨?_, ?_⟩, φ.apply_symm_apply y⟩
        · rw [hmem, φ.apply_symm_apply]
          exact hycl
        · exact hzy.trans (IsConj.symm (isConj_iff.mpr ⟨g, φ.apply_symm_apply y⟩))
    have hS : {w : G | w ∈ E ∧ IsConj z w}.ncard =
        {w : G | w ∈ Subgroup.closure ({a, b, t} : Set G) ∧ IsConj z w}.ncard := by
      rw [← himg, Set.ncard_image_of_injective _ hφinj]
    rcases hcard with h | h
    · exact Or.inl (by rw [hS, h])
    · exact Or.inr (by rw [hS, h])

end CFSG.EvenSporadicStandard.HNRecog.Section3
