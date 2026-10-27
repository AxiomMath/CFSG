module

public import CFSG.ClassicalInvolution.Q3.Q3TWCollTD

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.ClassicalInvolution.Q3.Q3Z

section Glue

variable {G : Type*}

@[expose] def gOfD (fA : Fin 6 → G) (fC : Fin 12 → G) : Fin 16 → G :=
  ![fC 0, fC 1, fC 4, fC 5, fA 0, fA 1, fA 2, fA 3, fC 6, fA 4, fA 5, fC 7, fC 8, fC 9, fC 10,
    fC 11]

theorem gOfD_a2Idx16 (fA : Fin 6 → G) (fC : Fin 12 → G) : gOfD fA fC ∘ a2Idx16 = fA := by
  funext j
  fin_cases j <;> rfl

variable [Group G]

@[expose] def substAssign16 (g : Fin 16 → G) (a b : List (Fin 16 × Bool)) : Fin 16 → G :=
  fun i => if i = 9 then evalW g a else if i = 10 then evalW g b else g i

theorem evalW_flatMap_substLetter16 (g : Fin 16 → G) (a b : List (Fin 16 × Bool))
    (w : List (Fin 16 × Bool)) :
    evalW g (w.flatMap (substLetter16 a b)) = evalW (substAssign16 g a b) w := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rw [List.flatMap_cons, evalW_append, ih, evalW_cons]
    congr 1
    obtain ⟨i, s⟩ := p
    by_cases h1 : i = 9
    · subst h1
      cases s <;> simp [substLetter16, substAssign16, evalW_invWord]
    · by_cases h2 : i = 10
      · subst h2
        have h12 : (10 : Fin 16) ≠ 9 := by decide
        cases s <;> simp [substLetter16, substAssign16, evalW_invWord, h12]
      · cases s <;> simp [substLetter16, substAssign16, h1, h2]

theorem relsHold_a2PartD (fA : Fin 6 → G) (fC : Fin 12 → G) (hA : RelsHold fA a2Words) :
    RelsHold (gOfD fA fC) (a2Words.map (mapWord a2Idx16)) :=
  relsHold_map_mapWord a2Idx16 _ _ (by rw [gOfD_a2Idx16]; exact hA)

theorem relsHold_commWordsTD (g : Fin 16 → G) (h48 : g 4 * g 8 = g 8 * g 4)
    (h4b : g 4 * g 11 = g 11 * g 4) (h4c : g 4 * g 12 = g 12 * g 4)
    (h4d : g 4 * g 13 = g 13 * g 4) (h58 : g 5 * g 8 = g 8 * g 5)
    (h5b : g 5 * g 11 = g 11 * g 5) (h5c : g 5 * g 12 = g 12 * g 5)
    (h5d : g 5 * g 13 = g 13 * g 5) : RelsHold g commWordsTD := by
  have key : ∀ x y : G, x * y = y * x → x⁻¹ * (y⁻¹ * (x * (y * 1))) = 1 := by
    intro x y h
    rw [mul_one, h, inv_mul_cancel_left, inv_mul_cancel]
  intro w hw
  simp only [commWordsTD, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [evalW] using key _ _ h48
  · simpa [evalW] using key _ _ h4b
  · simpa [evalW] using key _ _ h4c
  · simpa [evalW] using key _ _ h4d
  · simpa [evalW] using key _ _ h58
  · simpa [evalW] using key _ _ h5b
  · simpa [evalW] using key _ _ h5c
  · simpa [evalW] using key _ _ h5d

theorem relsHold_td4Glued (fA : Fin 6 → G) (fC : Fin 12 → G) (hA : RelsHold fA a2Words)
    (hC : RelsHold fC su4Words) (a b : List (Fin 16 × Bool))
    (ha : evalW (gOfD fA fC) a = fC 2) (hb : evalW (gOfD fA fC) b = fC 3)
    (h46 : fA 0 * fC 6 = fC 6 * fA 0) (h47 : fA 0 * fC 7 = fC 7 * fA 0)
    (h48 : fA 0 * fC 8 = fC 8 * fA 0) (h49 : fA 0 * fC 9 = fC 9 * fA 0)
    (h56 : fA 1 * fC 6 = fC 6 * fA 1) (h57 : fA 1 * fC 7 = fC 7 * fA 1)
    (h58 : fA 1 * fC 8 = fC 8 * fA 1) (h59 : fA 1 * fC 9 = fC 9 * fA 1) :
    RelsHold (gOfD fA fC) (td4GluedWords a b) := by
  unfold td4GluedWords
  rw [relsHold_append, relsHold_append]
  refine ⟨⟨relsHold_a2PartD fA fC hA, ?_⟩,
    relsHold_commWordsTD _ h46 h47 h48 h49 h56 h57 h58 h59⟩
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  rw [evalW_flatMap_substLetter16, evalW_mapWord]
  have hsub : substAssign16 (gOfD fA fC) a b ∘ su4Idx = fC := by
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
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hsub]
  exact hC v hv

end Glue

end CFSG.ClassicalInvolution.Q3.Q3TW
