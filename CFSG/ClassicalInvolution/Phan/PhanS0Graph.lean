module

public import CFSG.ClassicalInvolution.Phan.Geometry.WalkHomotopy
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open SimpleGraph CFSG.ClassicalInvolution.Phan

variable {V : Type*} {G : SimpleGraph V}

section Basic

variable (E : ∀ x : V, Set (G.Walk x x))

theorem cycleHomotopic_nil_of_conj {x y : V} (q : G.Walk x y) (c : G.Walk y y)
    (h : CycleHomotopic E (q.append (c.append q.reverse)) .nil) :
    CycleHomotopic E c .nil := by
  have h₁ : CycleHomotopic E c ((q.reverse.append q).append (c.append (q.reverse.append q))) := by
    have := (cycleHomotopic_reverse_append E q).symm.append
      ((cycleHomotopic_reverse_append E q).symm.append_left c)
    rwa [Walk.append_nil, Walk.nil_append] at this
  have h₂ : CycleHomotopic E ((q.reverse.append q).append (c.append (q.reverse.append q)))
      (q.reverse.append q) := by
    have := (h.append_right q).append_left q.reverse
    simpa [Walk.append_assoc] using this
  exact h₁.trans (h₂.trans (cycleHomotopic_reverse_append E q))

@[expose] def Tri (x y z : V) : Prop :=
  ∃ (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x),
    CycleHomotopic E (.cons hxy (.cons hyz (.cons hzx .nil)) : G.Walk x x) .nil

variable {E}

theorem Tri.adj_left {x y z : V} (h : Tri E x y z) : G.Adj x y := h.1

theorem Tri.adj_mid {x y z : V} (h : Tri E x y z) : G.Adj y z := h.2.1

theorem Tri.adj_right {x y z : V} (h : Tri E x y z) : G.Adj z x := h.2.2.1

theorem cycleHomotopic_cone_three {u v w z e : V} (huv : G.Adj u v) (hvw : G.Adj v w)
    (hwz : G.Adj w z) (hu : G.Adj u e) (hv : G.Adj v e) (hw : G.Adj w e) (hz : G.Adj z e)
    (T₁ : CycleHomotopic E (.cons huv (.cons hv (.cons hu.symm .nil)) : G.Walk u u) .nil)
    (T₂ : CycleHomotopic E (.cons hvw (.cons hw (.cons hv.symm .nil)) : G.Walk v v) .nil)
    (T₃ : CycleHomotopic E (.cons hwz (.cons hz (.cons hw.symm .nil)) : G.Walk w w) .nil) :
    CycleHomotopic E (.cons huv (.cons hvw (.cons hwz .nil)) : G.Walk u z)
      (.cons hu (.cons hz.symm .nil)) := by
  refine cycleHomotopic_cone E (e := e)
    (fun x y => (x = u ∧ y = v) ∨ (x = v ∧ y = w) ∨ (x = w ∧ y = z)) ?_ _ hu hz ?_
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨huv, hu, hv, T₁⟩
    · exact ⟨hvw, hv, hw, T₂⟩
    · exact ⟨hwz, hw, hz, T₃⟩
  · intro d hd
    simp only [Walk.darts_cons, Walk.darts_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem cycleHomotopic_triangle_of_octahedron {a b c p₁ p₂ p₃ : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (T₁ : Tri E b p₃ p₁) (T₂ : Tri E p₃ p₂ p₁) (T₃ : Tri E p₂ c p₁) (T₄ : Tri E b c p₁)
    (T₅ : Tri E b p₃ a) (T₆ : Tri E p₃ p₂ a) (T₇ : Tri E p₂ c a) :
    CycleHomotopic E (.cons hab (.cons hbc (.cons hca .nil)) : G.Walk a a) .nil := by
  obtain ⟨hbp₃, hp₃p₁, hp₁b, c₁⟩ := T₁
  obtain ⟨hp₃p₂, hp₂p₁, _, c₂⟩ := T₂
  obtain ⟨hp₂c, hcp₁, _, c₃⟩ := T₃
  obtain ⟨_, _, _, c₄⟩ := T₄
  obtain ⟨_, hp₃a, _, c₅⟩ := T₅
  obtain ⟨_, hp₂a, _, c₆⟩ := T₆
  obtain ⟨_, _, _, c₇⟩ := T₇
  have hA := cycleHomotopic_cone_three hbp₃ hp₃p₂ hp₂c hp₁b.symm hp₃p₁ hp₂p₁ hcp₁ c₁ c₂ c₃
  have hB : CycleHomotopic E (.cons hbc .nil : G.Walk b c)
      (.cons hp₁b.symm (.cons hcp₁.symm .nil)) :=
    cycleHomotopic_replace_edge E hbc hp₁b.symm hcp₁ c₄
  have hC := cycleHomotopic_cone_three hbp₃ hp₃p₂ hp₂c hab.symm hp₃a hp₂a hca c₅ c₆ c₇
  have hBC : CycleHomotopic E (.cons hbc .nil : G.Walk b c)
      (.cons hab.symm (.cons hca.symm .nil)) :=
    hB.trans (hA.symm.trans hC)
  have hW : CycleHomotopic E (.cons hab (.cons hbc (.cons hca .nil)) : G.Walk a a)
      (.cons hab (.cons hab.symm (.cons hca.symm (.cons hca .nil)))) := by
    have := (hBC.append_right (.cons hca .nil : G.Walk c a)).cons hab
    simpa using this
  refine hW.trans ?_
  have h1 : CycleHomotopic E (.cons hca.symm (.cons hca .nil) : G.Walk a a) .nil :=
    cycleHomotopic_cons_cons_nil E hca.symm
  have h2 := cycleHomotopic_backtrack E (.nil : G.Walk a a)
    (.cons hca.symm (.cons hca .nil) : G.Walk a a) hab
  simp only [Walk.nil_append] at h2
  exact h2.symm.trans h1

end Basic

section Short

@[expose] def triWalks (G : SimpleGraph V) : ∀ x : V, Set (G.Walk x x) :=
  fun _ => {w | w.length = 3}

@[expose] def QuadNull (G : SimpleGraph V) : Prop :=
  ∀ (a b c d : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a),
    CycleHomotopic (triWalks G)
      (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil

@[expose] def PentNull (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.length = 5 → CycleHomotopic (triWalks G) p .nil

theorem cycleHomotopic_mono {E₁ E₂ : ∀ x : V, Set (G.Walk x x)}
    (h : ∀ (x : V) (c : G.Walk x x), c ∈ E₁ x → CycleHomotopic E₂ c .nil) {u v : V}
    {p q : G.Walk u v} (hpq : CycleHomotopic E₁ p q) : CycleHomotopic E₂ p q := by
  refine CycleHomotopic.induction (R := fun a b => CycleHomotopic E₂ a b) hpq ?_ ?_ ?_ ?_
  · intro a b hab
    cases hab with
    | backtrack p q h' => exact cycleHomotopic_backtrack E₂ p q h'
    | elem p q c hc => exact cycleHomotopic_insert_null E₂ p q (h _ c hc)
  · intro a
    exact CycleHomotopic.refl a
  · intro a b hab
    exact hab.symm
  · intro a b c hab hbc
    exact hab.trans hbc

variable (E : ∀ x : V, Set (G.Walk x x))

theorem cycleHomotopic_quad_of_quadNull (hq : QuadNull G)
    (h3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil) {u : V}
    (p : G.Walk u u) (hp : p.length = 4) : CycleHomotopic E p .nil := by
  match u, p, hp with
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
    exact cycleHomotopic_mono (fun x c hc => h3 c hc) (hq _ _ _ _ h₁ h₂ h₃ h₄)

theorem cycleHomotopic_of_length_le_five_B3
    (h3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil)
    (hq : QuadNull G) (h5 : PentNull G) {u : V} (p : G.Walk u u)
    (hp : p.length ≤ 5) : CycleHomotopic E p .nil := by
  match u, p, hp with
  | _, .nil, _ => exact CycleHomotopic.refl _
  | _, .cons h₁ .nil, _ => exact absurd h₁ (G.loopless.irrefl _)
  | _, .cons h₁ (.cons h₂ .nil), _ =>
    exact cycleHomotopic_cons_cons_nil E h₁
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ => exact h3 _ rfl
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
    exact cycleHomotopic_quad_of_quadNull E hq h3 _ rfl
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil)))), _ =>
    exact cycleHomotopic_mono (fun x c hc => h3 c hc) (h5 _ _ rfl)
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem cycleTrivial_of_cycles_le_five_B3 (hconn : G.Connected) (hdiam : G.ediam ≤ 2)
    (h3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil)
    (hq : QuadNull G) (h5 : PentNull G) : CycleTrivial E := by
  have hfin : G.ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hdiam
  have hd : G.diam ≤ 2 := ENat.toNat_le_of_le_natCast hdiam
  refine cycleTrivial_of_diam E hconn hfin fun u p hp => ?_
  exact cycleHomotopic_of_length_le_five_B3 E h3 hq h5 p (by omega)

end Short

end CFSG.ClassicalInvolution.PhanB3.S
