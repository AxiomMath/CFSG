module

public import CFSG.CharacterTheory.Wreathed.CentralProduct

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem four_smul_eq_zero_iff_quarterScale (l : ℕ) (hl : 0 < l)
    (c : ZMod (4 * l)) :
    4 • c = 0 ↔ ∃ i : ZMod 4, quarterScale l i = c := by
  let : NeZero (4 * l) := ⟨by omega⟩
  constructor
  · intro hc
    have heq : 4 • c = ((4 * c.val : ℕ) : ZMod (4 * l)) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
    rw [heq, ZMod.natCast_eq_zero_iff,
      Nat.mul_dvd_mul_iff_left (by decide : 0 < (4 : ℕ))] at hc
    obtain ⟨a, ha⟩ := hc
    refine ⟨(a : ZMod 4), ?_⟩
    rw [quarterScale_natCast, ← ZMod.natCast_zmod_val c, ha, Nat.mul_comm a l]
  · rintro ⟨i, rfl⟩
    rw [← map_nsmul]
    have hi : 4 • i = 0 := by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hi, map_zero]

theorem twice_quarterScale_cases (l : ℕ) (i : ZMod 4) :
    2 • quarterScale l i = 0 ∨ 2 • quarterScale l i = (2 * l : ℕ) := by
  have hi : 2 • i = 0 ∨ 2 • i = 2 :=
    (show ∀ i : ZMod 4, 2 • i = 0 ∨ 2 • i = 2 by decide) i
  rw [← map_nsmul]
  rcases hi with hi | hi
  · rw [hi, map_zero]
    exact Or.inl rfl
  · rw [hi, quarterScale_two]
    exact Or.inr rfl

theorem double_difference_iff_quarterScale (l : ℕ) (hl : 0 < l)
    (c : ZMod (4 * l)) :
    (2 • c = 0 ∨ 2 • c = (2 * l : ℕ)) ↔ ∃ i : ZMod 4, quarterScale l i = c := by
  constructor
  · intro hc
    apply (four_smul_eq_zero_iff_quarterScale l hl c).mp
    have hfour : 4 • c = 2 • (2 • c) := by rw [smul_smul]; rfl
    rw [hfour]
    rcases hc with hc | hc
    · rw [hc, smul_zero]
    · rw [hc, two_nsmul]
      exact twice_quarter_add_self l
  · rintro ⟨i, rfl⟩
    exact twice_quarterScale_cases l i

theorem element_mem_v_normalizer_iff (l : ℕ) (a b : ZMod (4 * l)) (e : ZMod 2) :
    element (4 * l) a b e ∈ Subgroup.normalizer (vSubgroup l : Set (Wreath (4 * l))) ↔
      2 • (a - b) = 0 ∨ 2 • (a - b) = (2 * l : ℕ) := by
  constructor
  · intro hg
    have hz : element (4 * l) 0 0 1 ∈ vSubgroup l := by simp
    have hp := (Subgroup.mem_normalizer_iff.mp hg (element (4 * l) 0 0 1)).mp hz
    rcases swap_exponent_cases e with rfl | rfl
    · rw [conjugate_swap_by_base] at hp
      have hdiff : 0 + a - b - (0 + b - a) = 2 • (a - b) := by
        rw [two_nsmul]
        abel
      simpa only [element_mem_v, hdiff] using hp
    · rw [conjugate_swap_by_swap] at hp
      have hdiff : 0 + a - b - (0 + b - a) = 2 • (a - b) := by
        rw [two_nsmul]
        abel
      simpa only [element_mem_v, hdiff] using hp
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro g
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
    change element (4 * l) c d f ∈ vSubgroup l ↔
      element (4 * l) a b e * element (4 * l) c d f *
        (element (4 * l) a b e)⁻¹ ∈ vSubgroup l
    have hneg (u : ZMod (4 * l)) :
        (u = 0 ∨ u = (2 * l : ℕ)) ↔ (-u = 0 ∨ -u = (2 * l : ℕ)) := by
      constructor
      · exact half_difference_neg l u
      · intro hu
        simpa only [neg_neg] using half_difference_neg l (-u) hu
    have hadd (u : ZMod (4 * l)) :
        (u = 0 ∨ u = (2 * l : ℕ)) ↔
        (2 • (a - b) + u = 0 ∨ 2 • (a - b) + u = (2 * l : ℕ)) := by
      constructor
      · exact half_difference_add l _ _ hg
      · intro hu
        have hsub := half_difference_add l _ _ (half_difference_neg l _ hg) hu
        simpa only [neg_add_cancel_left] using hsub
    rcases swap_exponent_cases e with rfl | rfl <;>
      rcases swap_exponent_cases f with rfl | rfl
    · rw [conjugate_base_by_base, element_mem_v]
    · rw [conjugate_swap_by_base, element_mem_v, element_mem_v]
      have hdiff : c + a - b - (d + b - a) = 2 • (a - b) + (c - d) := by
        rw [two_nsmul]
        abel
      rw [hdiff]
      exact hadd (c - d)
    · rw [conjugate_base_by_swap, element_mem_v, element_mem_v]
      have hdiff : d - c = -(c - d) := by abel
      rw [hdiff]
      exact hneg (c - d)
    · rw [conjugate_swap_by_swap, element_mem_v, element_mem_v]
      have hdiff : d + a - b - (c + b - a) = 2 • (a - b) + -(c - d) := by
        rw [two_nsmul]
        abel
      rw [hdiff]
      exact (hneg (c - d)).trans (hadd (-(c - d)))

theorem element_mem_v_normalizer_iff_quarterScale (l : ℕ) (hl : 0 < l)
    (a b : ZMod (4 * l)) (e : ZMod 2) :
    element (4 * l) a b e ∈ Subgroup.normalizer (vSubgroup l : Set (Wreath (4 * l))) ↔
      ∃ i : ZMod 4, quarterScale l i = a - b := by
  rw [element_mem_v_normalizer_iff, double_difference_iff_quarterScale l hl]

@[expose] def vNormalizerCoordinateMap (l : ℕ) (c : ZMod (4 * l) × ZMod 4 × ZMod 2) :
    Subgroup.normalizer (vSubgroup l : Set (Wreath (4 * l))) :=
  ⟨element (4 * l) (c.1 + quarterScale l c.2.1) c.1 c.2.2, by
    rw [element_mem_v_normalizer_iff]
    simpa only [add_sub_cancel_left] using twice_quarterScale_cases l c.2.1⟩

theorem vNormalizerCoordinateMap_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (vNormalizerCoordinateMap l) := by
  rintro ⟨a, b, e⟩ ⟨c, d, f⟩ heq
  have hcoord := (element_eq_iff _ _ _ _ _ _ _).mp (congrArg Subtype.val heq)
  have hac : a = c := hcoord.2.1
  have hef : e = f := hcoord.2.2
  subst c
  subst f
  have hbd : b = d := quarterScale_injective l hl (add_left_cancel hcoord.1)
  rw [hbd]

theorem vNormalizerCoordinateMap_surjective (l : ℕ) (hl : 0 < l) :
    Function.Surjective (vNormalizerCoordinateMap l) := by
  intro g
  obtain ⟨⟨a, b, e⟩, heq⟩ := (coordinateEquiv (4 * l)).symm.surjective g.val
  change element (4 * l) a b e = g.val at heq
  have hg : element (4 * l) a b e ∈
      Subgroup.normalizer (vSubgroup l : Set (Wreath (4 * l))) := heq ▸ g.property
  obtain ⟨i, hi⟩ := (element_mem_v_normalizer_iff_quarterScale l hl a b e).mp hg
  refine ⟨(b, i, e), ?_⟩
  apply Subtype.ext
  change element (4 * l) (b + quarterScale l i) b e = g.val
  rw [← heq, hi]
  congr 1
  abel

@[expose] def vNormalizerCoordinateEquiv (l : ℕ) (hl : 0 < l) :
    ZMod (4 * l) × ZMod 4 × ZMod 2 ≃
      Subgroup.normalizer (vSubgroup l : Set (Wreath (4 * l))) :=
  Equiv.ofBijective (vNormalizerCoordinateMap l)
    ⟨vNormalizerCoordinateMap_injective l hl, vNormalizerCoordinateMap_surjective l hl⟩

theorem card_v_normalizer (l : ℕ) (hl : 0 < l) :
    Nat.card (Subgroup.normalizer (vSubgroup l : Set (Wreath (4 * l)))) = 8 * (4 * l) := by
  rw [← Nat.card_congr (vNormalizerCoordinateEquiv l hl), Nat.card_prod, Nat.card_prod,
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod]
  ring

theorem v_normalizer_index_two (l : ℕ) (hl : 0 < l) :
    (vSubgroup l).relIndex (Subgroup.normalizer (vSubgroup l : Set (Wreath (4 * l)))) = 2 := by
  have hmul := (vSubgroup l).relIndex_mul_card
    (Subgroup.normalizer (vSubgroup l : Set (Wreath (4 * l))))
  rw [inf_eq_left.mpr (vSubgroup l).le_normalizer, card_vSubgroup l hl,
    card_v_normalizer l hl] at hmul
  nlinarith

end CFSG.Wreathed
