module

public import CFSG.ClassicalInvolution.Phan.Geometry.WalkHomotopy
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ClassicalInvolution.Phan

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (E : ∀ x : V, Set (G.Walk x x))

@[expose] def ConeTriangles : Prop :=
  ∀ (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a),
    ∃ (e : V) (hae : G.Adj a e) (hbe : G.Adj b e) (hce : G.Adj c e),
      CycleHomotopic E (.cons hab (.cons hbe (.cons hae.symm .nil)) : G.Walk a a) .nil ∧
      CycleHomotopic E (.cons hbc (.cons hce (.cons hbe.symm .nil)) : G.Walk b b) .nil ∧
      CycleHomotopic E (.cons hca (.cons hae (.cons hce.symm .nil)) : G.Walk c c) .nil

theorem cycleHomotopic_triangle_nil (hE : ConeTriangles E) {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) :
    CycleHomotopic E (.cons hab (.cons hbc (.cons hca .nil)) : G.Walk a a) .nil := by
  obtain ⟨e, hae, hbe, hce, T₁, T₂, T₃⟩ := hE a b c hab hbc hca
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

theorem cycleHomotopic_length_three (hE : ConeTriangles E) {u : V} (p : G.Walk u u)
    (hp : p.length = 3) : CycleHomotopic E p .nil := by
  match u, p, hp with
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ => exact cycleHomotopic_triangle_nil E hE h₁ h₂ h₃

@[expose] def CommonNeighbour4 : Prop :=
  ∀ (a b c d : V), G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
    ∃ e : V, G.Adj a e ∧ G.Adj b e ∧ G.Adj c e ∧ G.Adj d e

theorem cycleHomotopic_quad_nil (h3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 →
      CycleHomotopic E p .nil) (h4 : CommonNeighbour4 (G := G)) {a b c d : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    CycleHomotopic E (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil := by
  obtain ⟨e, hae, hbe, hce, hde⟩ := h4 a b c d hab hbc hcd hda
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

@[expose] def ApexPentagon : Prop :=
  ∀ (a c d : V), G.Adj c d → ∃ f : V, G.Adj f c ∧ G.Adj f d ∧ G.Adj a f

theorem cycleHomotopic_pent_nil (h3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 →
      CycleHomotopic E p .nil)
    (h4 : ∀ {u : V} (p : G.Walk u u), p.length = 4 → CycleHomotopic E p .nil)
    (h5 : ApexPentagon (G := G)) {a b c d g : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hdg : G.Adj d g) (hga : G.Adj g a) :
    CycleHomotopic E (.cons hab (.cons hbc (.cons hcd (.cons hdg (.cons hga .nil)))) :
      G.Walk a a) .nil := by
  obtain ⟨f, hfc, hfd, haf⟩ := h5 a c d hcd
  have hT : CycleHomotopic E (.cons hcd (.cons hfd.symm (.cons hfc.symm.symm .nil)) :
      G.Walk c c) .nil := h3 _ rfl
  have hrep := cycleHomotopic_replace_edge E hcd hfc.symm hfd.symm hT
  have step₁ : CycleHomotopic E
      (.cons hab (.cons hbc (.cons hcd (.cons hdg (.cons hga .nil)))) : G.Walk a a)
      (.cons hab (.cons hbc (.cons hfc.symm (.cons hfd (.cons hdg (.cons hga .nil)))))) := by
    have := (hrep.append_right (.cons hdg (.cons hga .nil))).append_left
      (.cons hab (.cons hbc .nil))
    simpa using this
  have step₂ : CycleHomotopic E
      (.cons hab (.cons hbc (.cons hfc.symm (.cons hfd (.cons hdg (.cons hga .nil))))) :
        G.Walk a a)
      (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm (.cons haf
        (.cons hfd (.cons hdg (.cons hga .nil)))))))) := by
    have := cycleHomotopic_backtrack E (.cons hab (.cons hbc (.cons hfc.symm .nil)) : G.Walk a f)
      (.cons hfd (.cons hdg (.cons hga .nil))) haf.symm
    simpa using this
  have step₃ : CycleHomotopic E
      (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm (.cons haf
        (.cons hfd (.cons hdg (.cons hga .nil)))))))  : G.Walk a a) .nil := by
    have e₁ : (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm (.cons haf
        (.cons hfd (.cons hdg (.cons hga .nil))))))) : G.Walk a a) =
        (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm .nil))) : G.Walk a a).append
          (.cons haf (.cons hfd (.cons hdg (.cons hga .nil)))) := by simp
    rw [e₁]
    have q₁ := h4 (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm .nil))) : G.Walk a a)
      rfl
    have q₂ := h4 (.cons haf (.cons hfd (.cons hdg (.cons hga .nil))) : G.Walk a a) rfl
    simpa using q₁.append q₂
  exact step₁.trans (step₂.trans step₃)

theorem cycleHomotopic_of_length_le_five (h3 : ConeTriangles E) (h4 : CommonNeighbour4 (G := G))
    (h5 : ApexPentagon (G := G)) {u : V} (p : G.Walk u u) (hp : p.length ≤ 5) :
    CycleHomotopic E p .nil := by
  have e3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil :=
    fun p hp => cycleHomotopic_length_three E h3 p hp
  have e4 : ∀ {u : V} (p : G.Walk u u), p.length = 4 → CycleHomotopic E p .nil := by
    intro u p hp
    match u, p, hp with
    | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
      exact cycleHomotopic_quad_nil E e3 h4 h₁ h₂ h₃ h₄
  match u, p, hp with
  | _, .nil, _ => exact CycleHomotopic.refl _
  | _, .cons h₁ .nil, _ => exact absurd h₁ (G.loopless.irrefl _)
  | _, .cons h₁ (.cons h₂ .nil), _ =>
    exact cycleHomotopic_cons_cons_nil E h₁
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ => exact cycleHomotopic_triangle_nil E h3 h₁ h₂ h₃
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
    exact cycleHomotopic_quad_nil E e3 h4 h₁ h₂ h₃ h₄
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil)))), _ =>
    exact cycleHomotopic_pent_nil E e3 e4 h5 h₁ h₂ h₃ h₄ h₅
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem cycleTrivial_of_cycles_le_five (hconn : G.Connected) (hdiam : G.ediam ≤ 2)
    (h3 : ConeTriangles E) (h4 : CommonNeighbour4 (G := G)) (h5 : ApexPentagon (G := G)) :
    CycleTrivial E := by
  have hfin : G.ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hdiam
  have hd : G.diam ≤ 2 := ENat.toNat_le_of_le_natCast hdiam
  refine cycleTrivial_of_diam E hconn hfin fun u p hp => ?_
  exact cycleHomotopic_of_length_le_five E h3 h4 h5 p (by omega)

end CFSG.ClassicalInvolution.Phan
