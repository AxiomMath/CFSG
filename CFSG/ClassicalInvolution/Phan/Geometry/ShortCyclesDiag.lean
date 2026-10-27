module

public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles

public section

namespace CFSG.ClassicalInvolution.Phan

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (E : ∀ x : V, Set (G.Walk x x))

@[expose] def ConeTrianglesD : Prop :=
  ∀ (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a),
    CycleHomotopic E (.cons hab (.cons hbc (.cons hca .nil)) : G.Walk a a) .nil ∨
    ∃ (e : V) (hae : G.Adj a e) (hbe : G.Adj b e) (hce : G.Adj c e),
      CycleHomotopic E (.cons hab (.cons hbe (.cons hae.symm .nil)) : G.Walk a a) .nil ∧
      CycleHomotopic E (.cons hbc (.cons hce (.cons hbe.symm .nil)) : G.Walk b b) .nil ∧
      CycleHomotopic E (.cons hca (.cons hae (.cons hce.symm .nil)) : G.Walk c c) .nil

theorem cycleHomotopic_triangle_nil_of_cone {a b c e : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (hae : G.Adj a e) (hbe : G.Adj b e) (hce : G.Adj c e)
    (T₁ : CycleHomotopic E (.cons hab (.cons hbe (.cons hae.symm .nil)) : G.Walk a a) .nil)
    (T₂ : CycleHomotopic E (.cons hbc (.cons hce (.cons hbe.symm .nil)) : G.Walk b b) .nil)
    (T₃ : CycleHomotopic E (.cons hca (.cons hae (.cons hce.symm .nil)) : G.Walk c c) .nil) :
    CycleHomotopic E (.cons hab (.cons hbc (.cons hca .nil)) : G.Walk a a) .nil := by
  refine cycleHomotopic_cone_nil E (e := e)
    (fun x y => (x = a ∧ y = b) ∨ (x = b ∧ y = c) ∨ (x = c ∧ y = a)) ?_ _ hae ?_
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hab, hae, hbe, T₁⟩
    · exact ⟨hbc, hbe, hce, T₂⟩
    · exact ⟨hca, hce, hae, T₃⟩
  · intro d hd
    simp only [Walk.darts_cons, Walk.darts_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem cycleHomotopic_length_three_D (hE : ConeTrianglesD E) {u : V} (p : G.Walk u u)
    (hp : p.length = 3) : CycleHomotopic E p .nil := by
  match u, p, hp with
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ =>
    rcases hE _ _ _ h₁ h₂ h₃ with h | ⟨e, hae, hbe, hce, T₁, T₂, T₃⟩
    · exact h
    · exact cycleHomotopic_triangle_nil_of_cone E h₁ h₂ h₃ hae hbe hce T₁ T₂ T₃

@[expose] def CommonNeighbour4D : Prop :=
  ∀ (a b c d : V), G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
    a ≠ c → ¬ G.Adj a c → b ≠ d → ¬ G.Adj b d →
    ∃ e : V, G.Adj a e ∧ G.Adj b e ∧ G.Adj c e ∧ G.Adj d e

theorem cycleHomotopic_quad_nil_of_diag
    (h3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil)
    {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (h : a = c ∨ G.Adj a c ∨ b = d ∨ G.Adj b d) :
    CycleHomotopic E (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil := by
  rcases h with hac | hac' | hbd | hbd'
  · subst hac
    have := (cycleHomotopic_cons_cons_nil E hab).append (cycleHomotopic_cons_cons_nil E hcd)
    simpa using this
  · have hca : G.Adj c a := hac'.symm
    have step := cycleHomotopic_backtrack E (.cons hab (.cons hbc .nil) : G.Walk a c)
      (.cons hcd (.cons hda .nil) : G.Walk c a) hca
    have t₁ := h3 (.cons hab (.cons hbc (.cons hca .nil)) : G.Walk a a) rfl
    have t₂ := h3 (.cons hac' (.cons hcd (.cons hda .nil)) : G.Walk a a) rfl
    have := t₁.append t₂
    refine step.trans ?_
    simpa using this
  · subst hbd
    have hc : CycleHomotopic E (.cons hbc (.cons hbc.symm .nil) : G.Walk b b) .nil :=
      cycleHomotopic_cons_cons_nil E hbc
    have h1 := cycleHomotopic_insert_null E (.cons hab .nil : G.Walk a b)
      (.cons hda .nil : G.Walk b a) hc
    have h2 := cycleHomotopic_cons_cons_nil E hab
    have h1' : CycleHomotopic E
        (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a)
        (.cons hab (.cons hda .nil) : G.Walk a a) := by
      simpa using h1.symm
    exact h1'.trans h2
  · have step := cycleHomotopic_backtrack E (.cons hab .nil : G.Walk a b)
      (.cons hbc (.cons hcd (.cons hda .nil)) : G.Walk b a) hbd'
    have tri : CycleHomotopic E
        (.cons hbd'.symm (.cons hbc (.cons hcd .nil)) : G.Walk d d) .nil := h3 _ rfl
    have h2 := cycleHomotopic_insert_null E (.cons hab (.cons hbd' .nil) : G.Walk a d)
      (.cons hda .nil : G.Walk d a) tri
    have t := h3 (.cons hab (.cons hbd' (.cons hda .nil)) : G.Walk a a) rfl
    refine step.trans ?_
    have e : (Walk.cons hab .nil : G.Walk a b).append
        (.cons hbd' (.cons hbd'.symm (.cons hbc (.cons hcd (.cons hda .nil))))) =
        (Walk.cons hab (.cons hbd' .nil) : G.Walk a d).append
          ((Walk.cons hbd'.symm (.cons hbc (.cons hcd .nil)) : G.Walk d d).append
            (.cons hda .nil)) := by simp
    rw [e]
    refine h2.symm.trans ?_
    simpa using t

theorem cycleHomotopic_quad_nil_D
    (h3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil)
    (h4 : CommonNeighbour4D (G := G)) {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) :
    CycleHomotopic E (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil := by
  by_cases h : a = c ∨ G.Adj a c ∨ b = d ∨ G.Adj b d
  · exact cycleHomotopic_quad_nil_of_diag E h3 hab hbc hcd hda h
  push Not at h
  obtain ⟨hac, hac', hbd, hbd'⟩ := h
  obtain ⟨e, hae, hbe, hce, hde⟩ := h4 a b c d hab hbc hcd hda hac hac' hbd hbd'
  refine cycleHomotopic_cone_nil E (e := e) (fun x y => G.Adj x y ∧ G.Adj x e ∧ G.Adj y e) ?_ _
    hae ?_
  · rintro x y ⟨hxy, hxe, hye⟩
    exact ⟨hxy, hxe, hye, h3 _ rfl⟩
  · intro d' hd'
    simp only [Walk.darts_cons, Walk.darts_nil, List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl
    · exact ⟨hab, hae, hbe⟩
    · exact ⟨hbc, hbe, hce⟩
    · exact ⟨hcd, hce, hde⟩
    · exact ⟨hda, hde, hae⟩

theorem cycleHomotopic_of_length_le_five_D (h3 : ConeTrianglesD E)
    (h4 : CommonNeighbour4D (G := G)) (h5 : ApexPentagon (G := G)) {u : V} (p : G.Walk u u)
    (hp : p.length ≤ 5) : CycleHomotopic E p .nil := by
  have e3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil :=
    fun p hp => cycleHomotopic_length_three_D E h3 p hp
  have e4 : ∀ {u : V} (p : G.Walk u u), p.length = 4 → CycleHomotopic E p .nil := by
    intro u p hp
    match u, p, hp with
    | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
      exact cycleHomotopic_quad_nil_D E e3 h4 h₁ h₂ h₃ h₄
  match u, p, hp with
  | _, .nil, _ => exact CycleHomotopic.refl _
  | _, .cons h₁ .nil, _ => exact absurd h₁ (G.loopless.irrefl _)
  | _, .cons h₁ (.cons h₂ .nil), _ =>
    exact cycleHomotopic_cons_cons_nil E h₁
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ => exact e3 _ rfl
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
    exact cycleHomotopic_quad_nil_D E e3 h4 h₁ h₂ h₃ h₄
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil)))), _ =>
    exact cycleHomotopic_pent_nil E e3 e4 h5 h₁ h₂ h₃ h₄ h₅
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem cycleTrivial_of_cycles_le_five_D (hconn : G.Connected) (hdiam : G.ediam ≤ 2)
    (h3 : ConeTrianglesD E) (h4 : CommonNeighbour4D (G := G)) (h5 : ApexPentagon (G := G)) :
    CycleTrivial E := by
  have hfin : G.ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hdiam
  have hd : G.diam ≤ 2 := ENat.toNat_le_of_le_natCast hdiam
  refine cycleTrivial_of_diam E hconn hfin fun u p hp => ?_
  exact cycleHomotopic_of_length_le_five_D E h3 h4 h5 p (by omega)

end CFSG.ClassicalInvolution.Phan

end
