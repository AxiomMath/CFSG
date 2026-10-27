module

public import CFSG.ClassicalInvolution.Q3.Q3ZEval

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

section Hom

variable {m : ℕ} {G H : Type*} [Group G] [Group H]

theorem evalW_hom (θ : G →* H) (f : Fin m → G) (w : List (Fin m × Bool)) :
    evalW (fun i => θ (f i)) w = θ (evalW f w) := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rw [evalW_cons, evalW_cons, ih, map_mul]
    congr 1
    split_ifs <;> simp

theorem relsHold_hom (θ : G →* H) {f : Fin m → G} {ws : List (List (Fin m × Bool))}
    (h : RelsHold f ws) : RelsHold (fun i => θ (f i)) ws := by
  intro w hw
  rw [evalW_hom, h w hw, map_one]

end Hom

section Glue

variable {G : Type*}

@[expose] def gOf (fA : Fin 6 → G) (fC : Fin 8 → G) : Fin 12 → G :=
  ![fC 0, fC 1, fC 2, fC 3, fA 0, fA 1, fA 2, fA 3, fC 4, fA 4, fA 5, fC 7]

theorem gOf_a2Idx (fA : Fin 6 → G) (fC : Fin 8 → G) : gOf fA fC ∘ a2Idx = fA := by
  funext j
  fin_cases j <;> rfl

theorem gOf_c2Idx (fA : Fin 6 → G) (fC : Fin 8 → G) (h45 : fA 4 = fC 5) (h56 : fA 5 = fC 6) :
    gOf fA fC ∘ c2Idx = fC := by
  funext j
  fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h45
  · exact h56
  · rfl

variable [Group G]

theorem relsHold_a2Part (fA : Fin 6 → G) (fC : Fin 8 → G) (hA : RelsHold fA a2Words) :
    RelsHold (gOf fA fC) (a2Words.map (mapWord a2Idx)) :=
  relsHold_map_mapWord a2Idx _ _ (by rw [gOf_a2Idx]; exact hA)

theorem relsHold_commWords (g : Fin 12 → G) (h42 : g 4 * g 2 = g 2 * g 4)
    (h43 : g 4 * g 3 = g 3 * g 4) (h52 : g 5 * g 2 = g 2 * g 5) (h53 : g 5 * g 3 = g 3 * g 5) :
    RelsHold g commWords := by
  have key : ∀ x y : G, x * y = y * x → x⁻¹ * (y⁻¹ * (x * (y * 1))) = 1 := by
    intro x y h
    rw [mul_one, h, inv_mul_cancel_left, inv_mul_cancel]
  intro w hw
  simp only [commWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · simpa [evalW] using key _ _ h42
  · simpa [evalW] using key _ _ h43
  · simpa [evalW] using key _ _ h52
  · simpa [evalW] using key _ _ h53

theorem relsHold_v6 (fA : Fin 6 → G) (fC : Fin 8 → G) (hA : RelsHold fA a2Words)
    (hC : RelsHold fC c2Words) (h45 : fA 4 = fC 5) (h56 : fA 5 = fC 6)
    (h42 : fA 0 * fC 2 = fC 2 * fA 0) (h43 : fA 0 * fC 3 = fC 3 * fA 0)
    (h52 : fA 1 * fC 2 = fC 2 * fA 1) (h53 : fA 1 * fC 3 = fC 3 * fA 1) :
    RelsHold (gOf fA fC) v6Words := by
  unfold v6Words
  rw [relsHold_append, relsHold_append]
  refine ⟨⟨relsHold_a2Part fA fC hA, ?_⟩, ?_⟩
  · exact relsHold_map_mapWord c2Idx _ _ (by rw [gOf_c2Idx fA fC h45 h56]; exact hC)
  · exact relsHold_commWords _ h42 h43 h52 h53

theorem relsHold_v6Glued (fA : Fin 6 → G) (fC : Fin 8 → G) (hA : RelsHold fA a2Words)
    (hC : RelsHold fC c2Words) (a b : List (Fin 12 × Bool))
    (ha : evalW (gOf fA fC) a = fC 5) (hb : evalW (gOf fA fC) b = fC 6)
    (h42 : fA 0 * fC 2 = fC 2 * fA 0) (h43 : fA 0 * fC 3 = fC 3 * fA 0)
    (h52 : fA 1 * fC 2 = fC 2 * fA 1) (h53 : fA 1 * fC 3 = fC 3 * fA 1) :
    RelsHold (gOf fA fC) (v6GluedWords a b) := by
  unfold v6GluedWords
  rw [relsHold_append, relsHold_append]
  refine ⟨⟨relsHold_a2Part fA fC hA, ?_⟩, relsHold_commWords _ h42 h43 h52 h53⟩
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  rw [evalW_flatMap_substLetter, evalW_mapWord]
  have hsub : substAssign (gOf fA fC) a b ∘ c2Idx = fC := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ha
    · exact hb
    · rfl
  rw [hsub]
  exact hC v hv

end Glue

end CFSG.ClassicalInvolution.Q3.Q3Z
