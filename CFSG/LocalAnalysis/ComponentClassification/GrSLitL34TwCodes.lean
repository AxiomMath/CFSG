module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwIdxDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwFinDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

@[expose] def IsC4 (c : Fin 4 × Fin 4 × Bool) : Prop := c.2.2 = true ∧ cosXor c.1 c.2.1 = 3

@[expose] def UC : Set (Fin 4 × Fin 4 × Bool) :=
  {c | (c.2.2 = false ∧ c.1 = c.2.1) ∨ IsC4 c}

theorem qmulC_sw_base (a b x y : Fin 4) :
    qmulC (a, b, true) (x, y, false) = (cosXor a x, cosXor b y, true) := rfl

theorem qmulC_sw_sw (a b x y : Fin 4) :
    qmulC (a, b, true) (x, y, true) = (cosXor b x, cosXor a y, false) := rfl

theorem cosXor_comm : ∀ a b : Fin 4, cosXor a b = cosXor b a := by decide

private theorem diag_aux : ∀ a b x y : Fin 4, cosXor a b = 3 →
    cosXor (cosXor a x) (cosXor b y) = 3 → x = y := by decide

private theorem swap_aux : ∀ a b x y : Fin 4, cosXor a b = 3 → cosXor x y = 3 →
    cosXor a (cosXor a x) = x ∧ cosXor b (cosXor a x) = y := by decide

private theorem small_aux : ∀ a b x y : Fin 4, cosXor a b = 3 → cosXor x y = 3 →
    (cosXor y a = 0 ∨ cosXor y a = 3) → (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by decide

private theorem swap2_aux : ∀ a b : Fin 4, cosXor a b = 3 → cosXor a 3 = b ∧ cosXor b 3 = a := by
  decide

private theorem cases4_aux : ∀ a b : Fin 4, cosXor a b = 3 →
    (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by decide

theorem codes_classify (U : Set (Fin 4 × Fin 4 × Bool))
    (h0 : ((0 : Fin 4), (0 : Fin 4), false) ∈ U)
    (hmul : ∀ c ∈ U, ∀ d ∈ U, qmulC c d ∈ U) (hsw : ∃ c ∈ U, c.2.2 = true)
    (h4 : ∀ c ∈ U, c.2.2 = true → IsC4 c) : U = U1 ∨ U = U2 ∨ U = UC := by
  obtain ⟨⟨a, b, e⟩, hs, he⟩ := hsw
  have he' : e = true := he
  subst he'
  have hab : cosXor a b = 3 := (h4 _ hs rfl).2
  have hdiag : ∀ x y : Fin 4, (x, y, false) ∈ U → x = y := by
    intro x y hxy
    have h1 := hmul _ hs _ hxy
    rw [qmulC_sw_base] at h1
    exact diag_aux a b x y hab (h4 _ h1 rfl).2
  have hss : ((3 : Fin 4), (3 : Fin 4), false) ∈ U := by
    have h1 := hmul _ hs _ hs
    rw [qmulC_sw_sw, cosXor_comm b a, hab] at h1
    exact h1
  by_cases hbig : ((1 : Fin 4), (1 : Fin 4), false) ∈ U ∨ ((2 : Fin 4), (2 : Fin 4), false) ∈ U
  ·
    right; right
    have h12 : ((1 : Fin 4), (1 : Fin 4), false) ∈ U ∧ ((2 : Fin 4), (2 : Fin 4), false) ∈ U := by
      rcases hbig with h | h
      · exact ⟨h, hmul _ h _ hss⟩
      · exact ⟨hmul _ h _ hss, h⟩
    have hall : ∀ c : Fin 4, (c, c, false) ∈ U := by
      intro c
      fin_cases c
      · exact h0
      · exact h12.1
      · exact h12.2
      · exact hss
    ext ⟨x, y, e⟩
    constructor
    · intro hxy
      cases e
      · exact Or.inl ⟨rfl, hdiag x y hxy⟩
      · exact Or.inr (h4 _ hxy rfl)
    · rintro (⟨he, hxy⟩ | ⟨he, hxy⟩)
      · have he' : e = false := he
        subst he'
        have hxy' : x = y := hxy
        subst hxy'
        exact hall x
      · have he' : e = true := he
        subst he'
        obtain ⟨h1, h2⟩ := swap_aux a b x y hab hxy
        have h3 := hmul _ hs _ (hall (cosXor a x))
        rw [qmulC_sw_base, h1, h2] at h3
        exact h3
  · push_neg at hbig
    obtain ⟨hn1, hn2⟩ := hbig
    have hb03 : ∀ x y : Fin 4, (x, y, false) ∈ U → x = y ∧ (x = 0 ∨ x = 3) := by
      intro x y hxy
      have hxy' := hdiag x y hxy
      subst hxy'
      refine ⟨rfl, ?_⟩
      fin_cases x
      · exact Or.inl rfl
      · exact absurd hxy hn1
      · exact absurd hxy hn2
      · exact Or.inr rfl
    have hswap : ∀ x y : Fin 4, (x, y, true) ∈ U → (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
      intro x y hxy
      have h1 := hmul _ hxy _ hs
      rw [qmulC_sw_sw] at h1
      obtain ⟨-, h3⟩ := hb03 _ _ h1
      exact small_aux a b x y hab (h4 _ hxy rfl).2 h3
    have hba : (b, a, true) ∈ U := by
      have h1 := hmul _ hs _ hss
      rw [qmulC_sw_base] at h1
      obtain ⟨e1, e2⟩ := swap2_aux a b hab
      rwa [e1, e2] at h1
    have hU : ∀ c, c ∈ U ↔
        c = (0, 0, false) ∨ c = (3, 3, false) ∨ c = (a, b, true) ∨ c = (b, a, true) := by
      rintro ⟨x, y, e⟩
      constructor
      · intro hxy
        cases e
        · obtain ⟨h1, h2⟩ := hb03 x y hxy
          subst h1
          rcases h2 with rfl | rfl <;> simp
        · rcases hswap x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      · rintro (h | h | h | h)
        · rw [h]; exact h0
        · rw [h]; exact hss
        · rw [h]; exact hs
        · rw [h]; exact hba
    rcases cases4_aux a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; ext c; rw [hU]; simp [U1]
    · left; ext c; rw [hU]; simp only [U1, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    · right; left; ext c; rw [hU]; simp [U2]
    · right; left; ext c; rw [hU]; simp only [U2, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

end CFSG.ComponentClassification.GrSLit.L34Tw
