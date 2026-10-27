module

public import CFSG.Sporadic.Co1Patterson.TitsMultiHomotopy
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open SimpleGraph CFSG.Monster.B.Recog CFSG.Sporadic.Co1Patterson

section Map

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {T' : Set V' → Prop}

theorem homotopicBy_map_of_homotopic (f : G →g G')
    (hT : ∀ (x y z : V) (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x),
      HomotopicBy T' (.cons (f.map_adj hxy) (.cons (f.map_adj hyz) (.cons (f.map_adj hzx) .nil))
        : G'.Walk (f x) (f x)) .nil)
    {u v : V} {p q : G.Walk u v} (h : Homotopic p q) :
    HomotopicBy T' (p.map f) (q.map f) := by
  induction h with
  | rel p q h =>
    cases h with
    | backtrack p q h =>
      simp only [Walk.map_append, Walk.map_cons]
      exact (ElemMoveBy.backtrack _ _ (f.map_adj h)).homotopicBy
    | @triangle x y z p q hxy hyz hzx =>
      have e := ((hT x y z hxy hyz hzx).append_right (q.map f)).append_left (p.map f)
      simp only [Walk.map_append, Walk.map_cons, Walk.cons_append, Walk.nil_append] at e ⊢
      exact e.symm
  | refl p => exact HomotopicBy.refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Map

section Edge

variable {V : Type*} {G : SimpleGraph V} {T : Set V → Prop}

theorem homotopicBy_edge_of_triangle {s t v : V}
    (hst : G.Adj s t) (hsv : G.Adj s v) (htv : G.Adj t v) (hT : T {s, t, v}) :
    HomotopicBy T (.cons hst .nil : G.Walk s t) (.cons hsv (.cons htv.symm .nil)) := by
  refine (homotopicBy_of_append_reverse ?_).symm
  have : T {s, v, t} := by rwa [Set.pair_comm v t]
  simpa using homotopicBy_triangle_nil hsv htv.symm hst.symm this

end Edge

section PointPlane

variable {P Q : Type*} {Δ : SimpleGraph P} {inc : P → Q → Prop} {Γ : SimpleGraph (P ⊕ Q)}
  {T : Set (P ⊕ Q) → Prop}

private def inlHom (hpp : ∀ x y, Γ.Adj (.inl x) (.inl y) ↔ Δ.Adj x y) : Δ →g Γ :=
  ⟨Sum.inl, fun h => (hpp _ _).2 h⟩

private theorem exists_homotopicBy_map_inl
    (hpp : ∀ x y, Γ.Adj (.inl x) (.inl y) ↔ Δ.Adj x y)
    (hpq : ∀ x π, Γ.Adj (.inl x) (.inr π) ↔ inc x π)
    (hqq : ∀ π ρ, ¬ Γ.Adj (.inr π) (.inr ρ))
    (hT : ∀ x y π, Δ.Adj x y → inc x π → inc y π → T {.inl x, .inl y, .inr π})
    (hclique : ∀ π x y, inc x π → inc y π → x ≠ y → Δ.Adj x y)
    {b : P} (n : ℕ) {a : P} (p : Γ.Walk (.inl a) (.inl b)) (hn : p.length ≤ n) :
    ∃ q : Δ.Walk a b, HomotopicBy T p (q.map (inlHom hpp)) := by
  induction n generalizing a with
  | zero =>
    cases p with
    | nil => exact ⟨.nil, HomotopicBy.refl _⟩
    | cons h p' => simp at hn
  | succ n ih =>
    cases p with
    | nil => exact ⟨.nil, HomotopicBy.refl _⟩
    | @cons _ w _ h p' =>
      rcases w with a' | π
      · obtain ⟨q', hq'⟩ := ih p' (by simpa using hn)
        have hΔ : Δ.Adj a a' := (hpp _ _).1 h
        exact ⟨.cons hΔ q', hq'.cons h⟩
      · cases p' with
        | @cons _ w' _ h' p'' =>
          rcases w' with a' | ρ
          · obtain ⟨q'', hq''⟩ := ih p'' (by simp at hn; omega)
            by_cases haa : a = a'
            · subst haa
              exact ⟨q'', (homotopicBy_cons_cons_symm h p'').trans hq''⟩
            · have hinc : inc a π := (hpq _ _).1 h
              have hinc' : inc a' π := (hpq _ _).1 h'.symm
              have hΔ : Δ.Adj a a' := hclique π a a' hinc hinc' haa
              have hst : Γ.Adj (.inl a) (.inl a') := (hpp _ _).2 hΔ
              have e := (homotopicBy_edge_of_triangle hst h h'.symm
                (hT a a' π hΔ hinc hinc')).append_right p''
              simp only [Walk.cons_append, Walk.nil_append] at e
              exact ⟨.cons hΔ q'', e.symm.trans (hq''.cons hst)⟩
          · exact absurd h' (hqq _ _)

private theorem homotopicBy_nil_of_closed_inl
    (hpp : ∀ x y, Γ.Adj (.inl x) (.inl y) ↔ Δ.Adj x y)
    (hpq : ∀ x π, Γ.Adj (.inl x) (.inr π) ↔ inc x π)
    (hqq : ∀ π ρ, ¬ Γ.Adj (.inr π) (.inr ρ))
    (hT : ∀ x y π, Δ.Adj x y → inc x π → inc y π → T {.inl x, .inl y, .inr π})
    (hclique : ∀ π x y, inc x π → inc y π → x ≠ y → Δ.Adj x y)
    (hplane : ∀ x y z, Δ.Adj x y → Δ.Adj y z → Δ.Adj x z → ∃ π, inc x π ∧ inc y π ∧ inc z π)
    (hΔ : Triangulable Δ) {a : P} (p : Γ.Walk (.inl a) (.inl a)) :
    HomotopicBy T p .nil := by
  obtain ⟨q, hq⟩ := exists_homotopicBy_map_inl hpp hpq hqq hT hclique p.length p le_rfl
  have hcone : ∀ (x y z : P) (hxy : Δ.Adj x y) (hyz : Δ.Adj y z) (hzx : Δ.Adj z x),
      HomotopicBy T (.cons ((inlHom hpp).map_adj hxy) (.cons ((inlHom hpp).map_adj hyz)
        (.cons ((inlHom hpp).map_adj hzx) .nil)) : Γ.Walk (.inl x) (.inl x)) .nil := by
    intro x y z hxy hyz hzx
    obtain ⟨π, hx, hy, hz⟩ := hplane x y z hxy hyz hzx.symm
    exact homotopicBy_triangle_of_cone ((hpp _ _).2 hxy) ((hpp _ _).2 hyz) ((hpp _ _).2 hzx)
      ((hpq _ _).2 hx) ((hpq _ _).2 hy) ((hpq _ _).2 hz)
      (hT x y π hxy hx hy) (hT y z π hyz hy hz) (hT z x π hzx hz hx)
  have h0 := homotopicBy_map_of_homotopic (inlHom hpp) hcone (hΔ a q)
  exact hq.trans h0

theorem triangulableBy_of_points
    (hpp : ∀ x y, Γ.Adj (.inl x) (.inl y) ↔ Δ.Adj x y)
    (hpq : ∀ x π, Γ.Adj (.inl x) (.inr π) ↔ inc x π)
    (hqq : ∀ π ρ, ¬ Γ.Adj (.inr π) (.inr ρ))
    (hT : ∀ x y π, Δ.Adj x y → inc x π → inc y π → T {.inl x, .inl y, .inr π})
    (hclique : ∀ π x y, inc x π → inc y π → x ≠ y → Δ.Adj x y)
    (hplane : ∀ x y z, Δ.Adj x y → Δ.Adj y z → Δ.Adj x z → ∃ π, inc x π ∧ inc y π ∧ inc z π)
    (hΔ : Triangulable Δ) : TriangulableBy Γ T := by
  rintro (a | π) p
  · exact homotopicBy_nil_of_closed_inl hpp hpq hqq hT hclique hplane hΔ p
  · cases p with
    | nil => exact HomotopicBy.refl _
    | @cons _ w _ h p' =>
      rcases w with a | ρ
      · have key : HomotopicBy T (p'.append (.cons h .nil)) .nil :=
          homotopicBy_nil_of_closed_inl hpp hpq hqq hT hclique hplane hΔ _
        have h₁ : HomotopicBy T p' (.cons h.symm .nil) :=
          homotopicBy_of_append_reverse (by simpa using key)
        exact (h₁.cons h).trans (homotopicBy_cons_cons_nil h)
      · exact absurd h (hqq _ _)

end PointPlane

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
