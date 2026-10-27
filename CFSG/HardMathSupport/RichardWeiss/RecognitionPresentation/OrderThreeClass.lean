module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.WordTreeFact

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

structure OrderThreeClass {J : Type*} [Group J] (D : J → Prop) : Prop where
  cube : ∀ p, D p → p ^ 3 = 1
  ne_one : ∀ p, D p → p ≠ 1
  inv : ∀ p, D p → D p⁻¹
  conj : ∀ g p, D p → D (g⁻¹ * p * g)
  pair : ∀ p q, D p → D q → PairAlt p q

variable {J : Type*} [Group J] {D : J → Prop}

omit [Group J] in
theorem vec4_zero (a b c d : J) : (![a, b, c, d] : Fin 4 → J) 0 = a := rfl
omit [Group J] in
theorem vec4_one (a b c d : J) : (![a, b, c, d] : Fin 4 → J) 1 = b := rfl
omit [Group J] in
theorem vec4_two (a b c d : J) : (![a, b, c, d] : Fin 4 → J) 2 = c := rfl
omit [Group J] in
theorem vec4_three (a b c d : J) : (![a, b, c, d] : Fin 4 → J) 3 = d := rfl

theorem OrderThreeClass.evalW_cdesc (hD : OrderThreeClass D) {k : ℕ} (x : Fin k → J)
    (hx : ∀ i, D (x i)) (c : CDesc k) : D (evalW x c.elt) := by
  have hl : D (evalW x (FreeGroup.mk [c.letter])) := by
    rw [evalW_letter]
    split_ifs
    · exact hx _
    · exact hD.inv _ (hx _)
  have := hD.conj (evalW x c.conj) _ hl
  simpa [CDesc.elt, evalW_mul, evalW_inv] using this

theorem OrderThreeClass.pairAlt_evalW (hD : OrderThreeClass D) {k : ℕ} (x : Fin k → J)
    (hx : ∀ i, D (x i)) (c1 c2 : CDesc k) : PairAlt (evalW x c1.elt) (evalW x c2.elt) :=
  hD.pair _ _ (hD.evalW_cdesc x hx c1) (hD.evalW_cdesc x hx c2)

theorem OrderThreeClass.tree_sound (hD : OrderThreeClass D) {a b c d : J} (ha : D a) (hb : D b)
    (hc : D c) (hd : D d) (T : Tree 4) (rels : List (FreeGroup (Fin 4)))
    (hrels : ∀ r ∈ rels, evalW ![a, b, c, d] r = 1) (hok : T.okF [0, 1, 2] 3 rels) :
    d ∈ Subgroup.closure {a, b, c} ∨
      ∃ t ∈ T.succs, (evalW ![a, b, c, d] t.elt * d) ^ 2 = 1 := by
  have hx : ∀ i, D (![a, b, c, d] i) := by
    intro i; fin_cases i <;> assumption
  have := Tree.soundF (![a, b, c, d]) (hD.pairAlt_evalW _ hx) [0, 1, 2] 3 T rels hrels hok
  have himg : (![a, b, c, d] : Fin 4 → J) '' {s | s ∈ ([0, 1, 2] : List (Fin 4))} = {a, b, c} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases hi with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, Or.inl rfl, rfl⟩
      · exact ⟨1, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨2, Or.inr (Or.inr rfl), rfl⟩
  rw [himg] at this
  simpa using this

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
