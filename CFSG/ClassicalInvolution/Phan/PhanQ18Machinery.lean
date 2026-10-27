module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.PhanQ

open SimpleGraph CFSG.ClassicalInvolution.Phan

section Walks

variable {V : Type*} {G : SimpleGraph V}

@[expose] def triWalks (G : SimpleGraph V) : ∀ x : V, Set (G.Walk x x) :=
  fun _ => {w | w.length = 3}

@[expose] def QuadNull (G : SimpleGraph V) : Prop :=
  ∀ (a b c d : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a),
    CycleHomotopic (triWalks G)
      (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil

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

theorem cycleHomotopic_quad_of_quadNull (E : ∀ x : V, Set (G.Walk x x)) (hq : QuadNull G)
    (h3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil) {u : V}
    (p : G.Walk u u) (hp : p.length = 4) : CycleHomotopic E p .nil := by
  match u, p, hp with
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
    exact cycleHomotopic_mono (fun x c hc => h3 c hc) (hq _ _ _ _ h₁ h₂ h₃ h₄)

variable (E : ∀ x : V, Set (G.Walk x x))

theorem cycleHomotopic_of_length_le_five_true (h3 : ConeTriangles E) (hq : QuadNull G)
    (h5 : ApexPentagon (G := G)) {u : V} (p : G.Walk u u) (hp : p.length ≤ 5) :
    CycleHomotopic E p .nil := by
  have e3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil :=
    fun p hp => cycleHomotopic_length_three E h3 p hp
  have e4 : ∀ {u : V} (p : G.Walk u u), p.length = 4 → CycleHomotopic E p .nil :=
    fun p hp => cycleHomotopic_quad_of_quadNull E hq e3 p hp
  match u, p, hp with
  | _, .nil, _ => exact CycleHomotopic.refl _
  | _, .cons h₁ .nil, _ => exact absurd h₁ (G.loopless.irrefl _)
  | _, .cons h₁ (.cons h₂ .nil), _ =>
    exact cycleHomotopic_cons_cons_nil E h₁
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ => exact cycleHomotopic_triangle_nil E h3 h₁ h₂ h₃
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
    exact e4 (.cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil)))) rfl
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil)))), _ =>
    exact cycleHomotopic_pent_nil E e3 e4 h5 h₁ h₂ h₃ h₄ h₅
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem cycleTrivial_of_cycles_le_five_true (hconn : G.Connected) (hdiam : G.ediam ≤ 2)
    (h3 : ConeTriangles E) (hq : QuadNull G) (h5 : ApexPentagon (G := G)) : CycleTrivial E := by
  have hfin : G.ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hdiam
  have hd : G.diam ≤ 2 := ENat.toNat_le_of_le_natCast hdiam
  refine cycleTrivial_of_diam E hconn hfin fun u p hp => ?_
  exact cycleHomotopic_of_length_le_five_true E h3 hq h5 p (by omega)

end Walks

end CFSG.ClassicalInvolution.PhanQ
