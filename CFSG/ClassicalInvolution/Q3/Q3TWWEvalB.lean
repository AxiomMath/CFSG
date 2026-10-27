module

public import CFSG.ClassicalInvolution.Q3.Q3TWCollB

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.ClassicalInvolution.Q3.Q3Z

section Glue

variable {G : Type*}

@[expose] def gOfB (fA : Fin 6 → G) (fC : Fin 8 → G) : Fin 12 → G :=
  ![fC 0, fC 1, fC 4, fC 5, fA 0, fA 1, fA 2, fA 3, fC 6, fA 4, fA 5, fC 7]

theorem gOfB_a2Idx (fA : Fin 6 → G) (fC : Fin 8 → G) : gOfB fA fC ∘ a2Idx = fA := by
  funext j
  fin_cases j <;> rfl

variable [Group G]

theorem relsHold_a2PartB (fA : Fin 6 → G) (fC : Fin 8 → G) (hA : RelsHold fA a2Words) :
    RelsHold (gOfB fA fC) (a2Words.map (mapWord a2Idx)) :=
  relsHold_map_mapWord a2Idx _ _ (by rw [gOfB_a2Idx]; exact hA)

theorem relsHold_commWordsB (g : Fin 12 → G) (h43 : g 4 * g 3 = g 3 * g 4)
    (h48 : g 4 * g 8 = g 8 * g 4) (h53 : g 5 * g 3 = g 3 * g 5) (h58 : g 5 * g 8 = g 8 * g 5) :
    RelsHold g commWordsB := by
  have key : ∀ x y : G, x * y = y * x → x⁻¹ * (y⁻¹ * (x * (y * 1))) = 1 := by
    intro x y h
    rw [mul_one, h, inv_mul_cancel_left, inv_mul_cancel]
  intro w hw
  simp only [commWordsB, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · simpa [evalW] using key _ _ h43
  · simpa [evalW] using key _ _ h48
  · simpa [evalW] using key _ _ h53
  · simpa [evalW] using key _ _ h58

theorem relsHold_b3Glued (fA : Fin 6 → G) (fC : Fin 8 → G) (hA : RelsHold fA a2Words)
    (hC : RelsHold fC c2Words) (a b : List (Fin 12 × Bool))
    (ha : evalW (gOfB fA fC) a = fC 2) (hb : evalW (gOfB fA fC) b = fC 3)
    (h43 : fA 0 * fC 5 = fC 5 * fA 0) (h48 : fA 0 * fC 6 = fC 6 * fA 0)
    (h53 : fA 1 * fC 5 = fC 5 * fA 1) (h58 : fA 1 * fC 6 = fC 6 * fA 1) :
    RelsHold (gOfB fA fC) (b3GluedWords a b) := by
  unfold b3GluedWords
  rw [relsHold_append, relsHold_append]
  refine ⟨⟨relsHold_a2PartB fA fC hA, ?_⟩, relsHold_commWordsB _ h43 h48 h53 h58⟩
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  rw [evalW_flatMap_substLetter, evalW_mapWord]
  have hsub : substAssign (gOfB fA fC) a b ∘ b2Idx = fC := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact ha
    · exact hb
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hsub]
  exact hC v hv

end Glue

end CFSG.ClassicalInvolution.Q3.Q3TW
