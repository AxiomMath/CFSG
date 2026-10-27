module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusCentEntries

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.LieType.Steinberg.SpinFrame

variable {n : ℕ} {K : Type} [Field K]

@[expose] def barS (n : ℕ) : SM n → SM n
  | .inl a => .inr (.inl a)
  | .inr (.inl a) => .inl a
  | .inr (.inr u) => .inr (.inr u)

theorem barS_barS (x : SM n) : barS n (barS n x) = x := by
  rcases x with a | a | u <;> rfl

theorem barS_inj {x y : SM n} (h : barS n x = barS n y) : x = y := by
  simpa only [barS_barS] using congrArg (barS n) h

theorem barS_minusPos (a : Fin (n - 1)) (r : Bool) : barS n (minusPos n a r) = minusPos n a (!r) := by
  cases r <;> rfl

theorem minusPos_ne_pl (a : Fin (n - 1)) (r : Bool) (u : Fin 2) : minusPos n a r ≠ pl n u := by
  cases r <;> simp [minusPos, pl]

theorem minusPos_inj {a a' : Fin (n - 1)} {r r' : Bool} (h : minusPos n a r = minusPos n a' r') :
    a = a' ∧ r = r' := by
  cases r <;> cases r' <;> simp_all [minusPos]

theorem minusPos_ne_not (a : Fin (n - 1)) (r : Bool) : minusPos n a r ≠ minusPos n a (!r) := by
  cases r <;> simp [minusPos]

@[expose] def HMS (G : Matrix (SM n) (SM n) K) (p r : SM n) : Prop :=
  ∀ x y, G x p * (if y = barS n r then 1 else 0) - G x r * (if y = barS n p then 1 else 0) =
    (if x = p then 1 else 0) * G (barS n r) y - (if x = r then 1 else 0) * G (barS n p) y

theorem hms_of_comm {a b' : Fin (n - 1)} (b c : K) (hab : a ≠ b') (t : Bool)
    (G : Matrix (SM n) (SM n) K)
    (hG : G * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) =
      mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) * G) :
    HMS G (minusPos n a true) (minusPos n b' t) := by
  intro x y
  have h := comm_entries_long_mat (b := b) (c := c) hab t G hG x y
  rw [barS_minusPos, barS_minusPos]
  simpa only [Bool.not_true] using h

section HMS

variable {G : Matrix (SM n) (SM n) K} {p r : SM n}

theorem HMS.col_p (h : HMS G p r) (hpr : p ≠ r) (x : SM n) :
    G x p = (if x = p then G (barS n r) (barS n r) else 0) -
      (if x = r then G (barS n p) (barS n r) else 0) := by
  have := h x (barS n r)
  have hne : barS n r ≠ barS n p := fun e => hpr (barS_inj e).symm
  simpa [hne] using this

theorem HMS.row_bar (h : HMS G p r) (hpr : p ≠ r) {y : SM n} (hy1 : y ≠ barS n r)
    (hy2 : y ≠ barS n p) : G (barS n r) y = 0 ∧ G (barS n p) y = 0 := by
  constructor
  · have := h p y
    simpa [hy1, hy2, hpr] using this.symm
  · have := h r y
    simpa [hy1, hy2, hpr.symm] using this

theorem col_row_of_two {r₁ r₂ : SM n} (h12 : r₁ ≠ r₂) (h1 : p ≠ r₁) (h2 : p ≠ r₂)
    (H1 : HMS G p r₁) (H2 : HMS G p r₂) :
    (∀ x, G x p = if x = p then G p p else 0) ∧
      (∀ y, G (barS n p) y = if y = barS n p then G (barS n p) (barS n p) else 0) := by
  constructor
  · intro x
    by_cases hx : x = p
    · subst hx; simp
    · rw [if_neg hx]
      by_cases hx1 : x = r₁
      · rw [H2.col_p h2 x]
        simp [hx1, h12, h1.symm]
      · rw [H1.col_p h1 x]
        simp [hx, hx1]
  · intro y
    by_cases hy : y = barS n p
    · subst hy; simp
    · rw [if_neg hy]
      by_cases hy1 : y = barS n r₁
      · exact (H2.row_bar h2 (fun e => h12 (barS_inj (hy1.symm.trans e)))  hy).2
      · exact (H1.row_bar h1 hy1 hy).2

end HMS

theorem one_sub_one_sub (u : Fin 2) : 1 - (1 - u) = u := by
  fin_cases u <;> rfl

section Plane

variable (b c : K) (G : Matrix (SM n) (SM n) K)

@[expose] def SId (a : Fin (n - 1)) (u : Fin 2) : Prop :=
  ∀ x y, G x (pl n u) * (if y = minusPos n a false then 1 else 0) -
        G x (minusPos n a true) * (b * (if y = pl n (1 - u) then 1 else 0) +
          planeN c u * (if y = minusPos n a false then 1 else 0)) =
      (if x = pl n u then 1 else 0) * G (minusPos n a false) y -
        (if x = minusPos n a true then 1 else 0) *
          (b * G (pl n (1 - u)) y + planeN c u * G (minusPos n a false) y)

structure PlaneData (a : Fin (n - 1)) : Prop where
  col : ∀ x, G x (minusPos n a true) =
    if x = minusPos n a true then G (minusPos n a true) (minusPos n a true) else 0
  row : ∀ y, G (minusPos n a false) y =
    if y = minusPos n a false then G (minusPos n a false) (minusPos n a false) else 0
  S : ∀ u, SId b c G a u

variable {b c G}

theorem PlaneData.plane_row (hb : b ≠ 0) {a : Fin (n - 1)} (D : PlaneData b c G a) (u' : Fin 2)
    {y : SM n} (hy : y ≠ minusPos n a false) :
    G (pl n u') y = if y = pl n u' then G (minusPos n a true) (minusPos n a true) else 0 := by
  have h := D.S (1 - u') (minusPos n a true) y
  rw [one_sub_one_sub] at h
  have hr := D.row y
  rw [if_neg hy] at hr
  have hne : minusPos n a true ≠ pl n (1 - u') := minusPos_ne_pl a true _
  rw [if_neg hy, if_neg hne, if_pos rfl, hr] at h
  apply mul_left_cancel₀ hb
  by_cases hy' : y = pl n u'
  · rw [if_pos hy'] at h ⊢
    linear_combination h
  · rw [if_neg hy'] at h ⊢
    linear_combination h

theorem PlaneData.plane_col {a : Fin (n - 1)} (D : PlaneData b c G a) (u : Fin 2) {x : SM n}
    (hx : x ≠ minusPos n a true) :
    G x (pl n u) = if x = pl n u then G (minusPos n a false) (minusPos n a false) else 0 := by
  have h := D.S u x (minusPos n a false)
  have hne : minusPos n a false ≠ pl n (1 - u) := minusPos_ne_pl a false _
  have hc := D.col x
  rw [if_neg hx] at hc
  rw [if_pos rfl, if_neg hne, if_neg hx, hc, D.row (minusPos n a false), if_pos rfl] at h
  by_cases hx' : x = pl n u
  · rw [if_pos hx'] at h ⊢
    linear_combination h
  · rw [if_neg hx'] at h ⊢
    linear_combination h

theorem block_of_two (hb : b ≠ 0) {a₁ a₂ : Fin (n - 1)} (h12 : a₁ ≠ a₂)
    (D₁ : PlaneData b c G a₁) (D₂ : PlaneData b c G a₂) :
    ∀ x y, (∃ u, x = pl n u) ∨ (∃ u, y = pl n u) →
      G x y = if x = y then G (minusPos n a₁ true) (minusPos n a₁ true) else 0 := by
  have hne : minusPos n a₁ false ≠ minusPos n a₂ false := fun e => h12 (minusPos_inj e).1
  have hne' : minusPos n a₁ true ≠ minusPos n a₂ true := fun e => h12 (minusPos_inj e).1
  have rows : ∀ u' y, G (pl n u') y =
      if y = pl n u' then G (minusPos n a₁ true) (minusPos n a₁ true) else 0 := by
    intro u' y
    by_cases hy : y = minusPos n a₁ false
    · subst hy
      rw [D₂.plane_row hb u' hne, if_neg (minusPos_ne_pl a₁ false u'), if_neg (minusPos_ne_pl a₁ false u')]
    · exact D₁.plane_row hb u' hy
  have cols : ∀ x u, G x (pl n u) =
      if x = pl n u then G (minusPos n a₁ true) (minusPos n a₁ true) else 0 := by
    intro x u
    have hlam : G (minusPos n a₁ false) (minusPos n a₁ false) =
        G (minusPos n a₁ true) (minusPos n a₁ true) := by
      have h1 := D₁.plane_col u (x := pl n u) (fun e => (minusPos_ne_pl a₁ true u) e.symm)
      rw [rows u (pl n u), if_pos rfl, if_pos rfl] at h1
      exact h1.symm
    have key : ∀ x, x ≠ minusPos n a₁ true → G x (pl n u) =
        if x = pl n u then G (minusPos n a₁ true) (minusPos n a₁ true) else 0 := by
      intro x hx
      rw [D₁.plane_col u hx, hlam]
    by_cases hx : x = minusPos n a₁ true
    · subst hx
      have := D₂.plane_col u (x := minusPos n a₁ true) hne'
      rw [this, if_neg (minusPos_ne_pl a₁ true u), if_neg (minusPos_ne_pl a₁ true u)]
    · exact key x hx
  rintro x y (⟨u, rfl⟩ | ⟨u, rfl⟩)
  · rw [rows u y]
    simp only [eq_comm]
  · exact cols x u

end Plane

end CFSG.HardMathSupport.Cooperstein.StructureLie
