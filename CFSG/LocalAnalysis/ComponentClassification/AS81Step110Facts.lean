module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Z4

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {K : Type} [Group K] [Finite K] {z : K} [(zpowers z).Normal] {X T : Subgroup K} {g : K}

theorem Hyp19K.false_of_tim77Facts (hH : Hyp19K K z X T) (hX : 128 ≤ Nat.card X)
    (hT : Tim77Facts (X.map (barMap z)) (barMap z g)) : False := by
  have hzX := hH.extra.mem
  have hc := hH.conf110 (hT.config111 hzX)
  have hXc : Nat.card X = Nat.card (zpowers z) * Nat.card (X.map (barMap z)) := by
    rw [← card_comap_barMap, comap_map_barMap hzX]
  have hBc : Nat.card (tim77B X g) =
      Nat.card (zpowers z) * Nat.card (tim77B (X.map (barMap z)) (barMap z g)) := by
    rw [← comap_tim77B hzX, card_comap_barMap]
  have hDc : Nat.card (tim77D X g) =
      Nat.card (zpowers z) * Nat.card (tim77D (X.map (barMap z)) (barMap z g)) := by
    rw [← comap_tim77D hzX, card_comap_barMap]
  have hIc : Nat.card (tim77I X g) =
      Nat.card (zpowers z) * Nat.card (tim77I (X.map (barMap z)) (barMap z g)) := by
    rw [← comap_tim77I hzX, card_comap_barMap]
  refine hc.false_of_tim77Facts hX ?_ ?_ ?_ ?_
  · rw [hBc, hDc, hT.card_eq]
  · intro d hd hdI x hx hxd
    rw [← comap_tim77B hzX, mem_comap]
    rw [← comap_tim77D hzX, mem_comap] at hd
    rw [← comap_tim77I hzX, mem_comap] at hdI hxd
    exact hT.fixD _ hd hdI _ ⟨x, hx, rfl⟩ (by simpa [map_mul, map_inv] using hxd)
  · have hle : tim77B X g ≤ X := inf_le_left
    refine lt_of_le_of_ne hle fun he => hT.lt_B.ne ?_
    rw [← map_comap_barMap (tim77B _ _), comap_tim77B hzX, he]
  · rcases hT.cases with h2 | h4
    · left
      rw [hBc, hXc, ← h2]
      ring
    · right
      rw [hIc, hDc]
      calc 4 * (Nat.card (zpowers z) * Nat.card (tim77I (X.map (barMap z)) (barMap z g)))
          = Nat.card (zpowers z) * (4 * Nat.card (tim77I (X.map (barMap z)) (barMap z g))) := by
            ring
        _ ≤ _ := Nat.mul_le_mul_left _ h4

end CFSG.ComponentClassification.AS81
