module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.ClassicalInvolution.Q3.Q3ZWords

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.CosetTable

section Eval

variable {m : ℕ} {G : Type*} [Group G]

@[expose] def evalW (g : Fin m → G) (w : List (Fin m × Bool)) : G :=
  (w.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod

@[expose] def RelsHold (g : Fin m → G) (ws : List (List (Fin m × Bool))) : Prop :=
  ∀ w ∈ ws, evalW g w = 1

@[simp] theorem evalW_nil (g : Fin m → G) : evalW g [] = 1 := rfl

theorem evalW_cons (g : Fin m → G) (p : Fin m × Bool) (w : List (Fin m × Bool)) :
    evalW g (p :: w) = (if p.2 then g p.1 else (g p.1)⁻¹) * evalW g w := by
  simp [evalW]

theorem evalW_append (g : Fin m → G) (u v : List (Fin m × Bool)) :
    evalW g (u ++ v) = evalW g u * evalW g v := by
  simp [evalW]

@[simp] theorem evalW_singleton_true (g : Fin m → G) (i : Fin m) :
    evalW g [(i, true)] = g i := by
  simp [evalW]

@[simp] theorem evalW_singleton_false (g : Fin m → G) (i : Fin m) :
    evalW g [(i, false)] = (g i)⁻¹ := by
  simp [evalW]

theorem evalW_invWord (g : Fin m → G) (w : List (Fin m × Bool)) :
    evalW g (invWord w) = (evalW g w)⁻¹ := by
  induction w with
  | nil => simp [invWord]
  | cons p w ih =>
    have h : invWord (p :: w) = invWord w ++ [(p.1, !p.2)] := by
      simp [invWord]
    rw [h, evalW_append, ih, evalW_cons]
    obtain ⟨i, b⟩ := p
    cases b <;> simp [evalW, mul_inv_rev]

theorem evalW_mapWord {a b : ℕ} (f : Fin a → Fin b) (g : Fin b → G) (w : List (Fin a × Bool)) :
    evalW g (mapWord f w) = evalW (g ∘ f) w := by
  induction w with
  | nil => simp [mapWord]
  | cons p w ih =>
    have h : mapWord f (p :: w) = (f p.1, p.2) :: mapWord f w := by simp [mapWord]
    rw [h, evalW_cons, evalW_cons, ih]
    rfl

theorem relsHold_map_mapWord {a b : ℕ} (f : Fin a → Fin b) (g : Fin b → G)
    (ws : List (List (Fin a × Bool))) (h : RelsHold (g ∘ f) ws) :
    RelsHold g (ws.map (mapWord f)) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  rw [evalW_mapWord]
  exact h v hv

theorem relsHold_append {g : Fin m → G} {ws vs : List (List (Fin m × Bool))} :
    RelsHold g (ws ++ vs) ↔ RelsHold g ws ∧ RelsHold g vs := by
  constructor
  · intro h
    exact ⟨fun w hw => h w (List.mem_append_left _ hw),
      fun w hw => h w (List.mem_append_right _ hw)⟩
  · rintro ⟨h1, h2⟩ w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact h1 w hw
    · exact h2 w hw

theorem exists_hom_of_relsHold (ws : List (List (Fin m × Bool))) (g : Fin m → G)
    (h : RelsHold g ws) : ∃ f : PG m ws →* G, ∀ i, f (PresentedGroup.of i) = g i := by
  have hlift : ∀ w : List (Fin m × Bool), FreeGroup.lift g (FreeGroup.mk w) = evalW g w := by
    intro w
    induction w with
    | nil => simp [evalW]
    | cons p w ih =>
      have hc : FreeGroup.mk (p :: w) = FreeGroup.mk [p] * FreeGroup.mk w := by
        rw [FreeGroup.mul_mk]
        rfl
      rw [hc, map_mul, ih, evalW_cons]
      obtain ⟨i, b⟩ := p
      cases b <;> simp
  refine ⟨PresentedGroup.toGroup (f := g) ?_, fun i => ?_⟩
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [hlift]
    exact h w hw
  · exact PresentedGroup.toGroup.of _

end Eval

section Subst

variable {G : Type*} [Group G]

@[expose] def substAssign (g : Fin 12 → G) (a b : List (Fin 12 × Bool)) : Fin 12 → G :=
  fun i => if i = xPlus then evalW g a else if i = xMinus then evalW g b else g i

theorem evalW_flatMap_substLetter (g : Fin 12 → G) (a b : List (Fin 12 × Bool))
    (w : List (Fin 12 × Bool)) :
    evalW g (w.flatMap (substLetter a b)) = evalW (substAssign g a b) w := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rw [List.flatMap_cons, evalW_append, ih, evalW_cons]
    congr 1
    obtain ⟨i, s⟩ := p
    by_cases h1 : i = xPlus
    · subst h1
      cases s <;> simp [substLetter, substAssign, evalW_invWord]
    · by_cases h2 : i = xMinus
      · subst h2
        have h12 : (xMinus : Fin 12) ≠ xPlus := by decide
        cases s <;> simp [substLetter, substAssign, evalW_invWord, h12]
      · cases s <;> simp [substLetter, substAssign, h1, h2]

end Subst

end CFSG.ClassicalInvolution.Q3.Q3Z
