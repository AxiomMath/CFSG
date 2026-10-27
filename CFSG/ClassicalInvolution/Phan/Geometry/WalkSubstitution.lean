module

public import CFSG.Monster.B.Recog.GenericWalkHomotopy
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace CFSG.ClassicalInvolution.Phan.Geometry

open SimpleGraph CFSG.Monster.B.Recog

variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {J : SimpleGraph X}

theorem homotopic_triangle_path {u v w : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) :
    Homotopic (Walk.cons huv (.cons hvw .nil)) (Walk.cons huw .nil) := by
  have ht := homotopic_triangle (.nil : G.Walk u u) (Walk.cons huw .nil)
    huv hvw huw.symm
  have hb := ((homotopic_cons_cons_nil huw.symm).cons hvw).cons huv
  exact (ht.trans hb).symm

theorem homotopic_cone_triangle {u v w s : V}
    (a : G.Walk u s) (b : G.Walk v s) (c : G.Walk w s) :
    Homotopic ((a.append b.reverse).append
      ((b.append c.reverse).append (c.append a.reverse))) .nil := by
  have hb := ((homotopic_reverse_append b).append_right
    (c.reverse.append (c.append a.reverse))).append_left a
  have hc := ((homotopic_reverse_append c).append_right a.reverse).append_left a
  have hbc : Homotopic ((a.append b.reverse).append
      ((b.append c.reverse).append (c.append a.reverse))) (a.append a.reverse) := by
    have hb' : Homotopic ((a.append b.reverse).append
        ((b.append c.reverse).append (c.append a.reverse)))
        (a.append (c.reverse.append (c.append a.reverse))) := by
      simpa only [Walk.append_assoc, Walk.nil_append] using hb
    have hc' : Homotopic (a.append (c.reverse.append (c.append a.reverse)))
        (a.append a.reverse) := by
      simpa only [Walk.append_assoc, Walk.nil_append] using hc
    exact hb'.trans hc'
  exact hbc.trans (homotopic_append_reverse a)

theorem homotopic_of_append_nil {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (h : Homotopic (p.append q) .nil) : Homotopic p q.reverse := by
  have h₁ : Homotopic (p.append (q.append q.reverse)) p := by
    simpa using (homotopic_append_reverse q).append_left p
  have h₂ : Homotopic (p.append (q.append q.reverse)) q.reverse := by
    simpa only [Walk.append_assoc, Walk.nil_append] using h.append_right q.reverse
  exact h₁.symm.trans h₂

theorem homotopic_reverse_connector {u v x y : V}
    {a : G.Walk u x} {b : G.Walk v y} {p : G.Walk x y} {q : G.Walk u v}
    (h : Homotopic (a.append p) (q.append b)) :
    Homotopic (b.append p.reverse) (q.reverse.append a) := by
  have hs := (h.reverse.append_left b).append_right a
  have hl : Homotopic ((b.append p.reverse).append (a.reverse.append a))
      (b.append p.reverse) := by
    simpa only [Walk.append_assoc, Walk.append_nil] using
      (homotopic_reverse_append a).append_left (b.append p.reverse)
  have hr : Homotopic ((b.append b.reverse).append (q.reverse.append a))
      (q.reverse.append a) := by
    simpa only [Walk.nil_append] using
      (homotopic_append_reverse b).append_right (q.reverse.append a)
  have hs' : Homotopic ((b.append p.reverse).append (a.reverse.append a))
      ((b.append b.reverse).append (q.reverse.append a)) := by
    simpa only [Walk.reverse_append, Walk.append_assoc] using hs
  exact hl.symm.trans (hs'.trans hr)

@[expose] def substituteWalk (f : V → W)
    (edge : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v)) :
    ∀ {u v}, G.Walk u v → H.Walk (f u) (f v)
  | _, _, .nil => .nil
  | _, _, .cons h p => (edge h).append (substituteWalk f edge p)

@[simp] theorem substituteWalk_nil (f : V → W)
    (edge : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v)) (u : V) :
    substituteWalk f edge (.nil : G.Walk u u) = .nil := rfl

@[simp] theorem substituteWalk_cons (f : V → W)
    (edge : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    {u v w} (h : G.Adj u v) (p : G.Walk v w) :
    substituteWalk f edge (.cons h p) = (edge h).append (substituteWalk f edge p) := rfl

@[simp] theorem substituteWalk_append (f : V → W)
    (edge : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    {u v w} (p : G.Walk u v) (q : G.Walk v w) :
    substituteWalk f edge (p.append q) =
      (substituteWalk f edge p).append (substituteWalk f edge q) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [Walk.cons_append, substituteWalk_cons, ih, Walk.append_assoc]

theorem substituteWalk_reverse_homotopic (f : V → W)
    (edge : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    (hback : ∀ {u v} (h : G.Adj u v), Homotopic ((edge h).append (edge h.symm)) .nil)
    {u v} (p : G.Walk u v) :
    Homotopic (substituteWalk f edge p.reverse) (substituteWalk f edge p).reverse := by
  induction p with
  | nil => exact Homotopic.refl _
  | cons h p ih =>
    simpa only [Walk.reverse_cons, substituteWalk_append, substituteWalk_cons,
      substituteWalk_nil, Walk.append_nil, Walk.reverse_append] using
      ih.append (homotopic_of_append_nil (hback h.symm))

theorem substituteWalk_homotopic (f : V → W)
    (edge : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    (hback : ∀ {u v} (h : G.Adj u v), Homotopic ((edge h).append (edge h.symm)) .nil)
    (htri : ∀ {u v w} (huv : G.Adj u v) (hvw : G.Adj v w) (hwu : G.Adj w u),
      Homotopic ((edge huv).append ((edge hvw).append (edge hwu))) .nil)
    {u v} {p q : G.Walk u v} (hpq : Homotopic p q) :
    Homotopic (substituteWalk f edge p) (substituteWalk f edge q) := by
  induction hpq with
  | rel p q h =>
    cases h with
    | backtrack p q h =>
      simpa only [substituteWalk_append, substituteWalk_cons, Walk.append_assoc,
        Walk.nil_append] using
        ((hback h).symm.append_right (substituteWalk f edge q)).append_left
          (substituteWalk f edge p)
    | triangle p q huv hvw hwu =>
      simpa only [substituteWalk_append, substituteWalk_cons, Walk.append_assoc,
        Walk.nil_append] using
        ((htri huv hvw hwu).symm.append_right (substituteWalk f edge q)).append_left
          (substituteWalk f edge p)
  | refl => exact Homotopic.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

@[simp] theorem substituteWalk_comp (f : V → W) (g : W → X)
    (edge : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    (edge' : ∀ {u v}, H.Adj u v → J.Walk (g u) (g v))
    {u v} (p : G.Walk u v) :
    substituteWalk g edge' (substituteWalk f edge p) =
      substituteWalk (g ∘ f) (fun h => substituteWalk g edge' (edge h)) p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [substituteWalk_cons, substituteWalk_append, ih]

theorem substituteWalk_naturality (f : V → V)
    (edge : ∀ {u v}, G.Adj u v → G.Walk (f u) (f v))
    (connector : ∀ u, G.Walk u (f u))
    (hedge : ∀ {u v} (h : G.Adj u v),
      Homotopic ((connector u).append (edge h))
        ((Walk.cons h .nil).append (connector v)))
    {u v} (p : G.Walk u v) :
    Homotopic ((connector u).append (substituteWalk f edge p))
      (p.append (connector v)) := by
  induction p with
  | nil => simpa using Homotopic.refl (connector _)
  | @cons u v w h p ih =>
    simp only [substituteWalk_cons, Walk.cons_append]
    have h₁ := (hedge h).append_right (substituteWalk f edge p)
    have h₂ := ih.cons h
    simpa only [Walk.append_assoc, Walk.cons_append, Walk.nil_append] using h₁.trans h₂

theorem triangulable_of_walk_retraction (i : W → V) (r : V → W)
    (expand : ∀ {u v}, H.Adj u v → G.Walk (i u) (i v))
    (reduce : ∀ {u v}, G.Adj u v → H.Walk (r u) (r v))
    (connector : ∀ u, G.Walk u (i (r u)))
    (hback : ∀ {u v} (h : H.Adj u v), Homotopic ((expand h).append (expand h.symm)) .nil)
    (htri : ∀ {u v w} (huv : H.Adj u v) (hvw : H.Adj v w) (hwu : H.Adj w u),
      Homotopic ((expand huv).append ((expand hvw).append (expand hwu))) .nil)
    (hedge : ∀ {u v} (h : G.Adj u v),
      Homotopic ((connector u).append (substituteWalk i expand (reduce h)))
        ((Walk.cons h .nil).append (connector v)))
    (hH : Triangulable H) : Triangulable G := by
  intro u p
  have hp := substituteWalk_homotopic i expand hback htri (hH (r u)
    (substituteWalk r reduce p))
  have hn := substituteWalk_naturality (i ∘ r)
    (fun h => substituteWalk i expand (reduce h)) connector hedge p
  rw [← substituteWalk_comp] at hn
  have hc : Homotopic (p.append (connector u)) (connector u) := by
    exact hn.symm.trans (by simpa using hp.append_left (connector u))
  have hc' := hc.append_right (connector u).reverse
  have hcancel := homotopic_append_reverse (connector u)
  have hp' : Homotopic (p.append ((connector u).append (connector u).reverse)) .nil := by
    simpa only [Walk.append_assoc] using hc'.trans hcancel
  have hstart : Homotopic (p.append ((connector u).append (connector u).reverse)) p := by
    simpa using hcancel.append_left p
  exact hstart.symm.trans hp'

theorem connected_of_walk_cover (i : W → V) (r : V → W)
    (expand : ∀ {u v}, H.Adj u v → G.Walk (i u) (i v))
    (connector : ∀ u, G.Walk u (i (r u))) (hH : H.Connected) : G.Connected := by
  rcases hH with ⟨hH⟩
  let : Nonempty V := Nonempty.map i inferInstance
  refine ⟨fun u v => ?_⟩
  obtain ⟨p⟩ := hH (r u) (r v)
  exact ⟨(connector u).append ((substituteWalk i expand p).append (connector v).reverse)⟩

theorem substituteWalk_copy (f : V → W)
    (edge : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    substituteWalk f edge (p.copy hu hv) =
      (substituteWalk f edge p).copy (congrArg f hu) (congrArg f hv) := by
  cases hu
  cases hv
  rfl

theorem homotopic_append_nil_copy {u x y : V} (p : G.Walk u x) (e : x = y) :
    Homotopic (p.append ((Walk.nil : G.Walk x x).copy rfl e)) (p.copy rfl e) := by
  subst y
  simp
  exact Homotopic.refl _

theorem homotopic_cons_copy_nil {u x y : V} (h : G.Adj u x) (h' : G.Adj u y)
    (e : x = y) :
    Homotopic (Walk.cons h ((Walk.nil : G.Walk x x).copy rfl e))
      (Walk.cons h' Walk.nil) := by
  subst y
  rw [show h' = h from Subsingleton.elim _ _]
  exact Homotopic.refl _

theorem homotopic_nil_copy_cons {x y z : V} (e : x = y) (h : G.Adj x z) (h' : G.Adj z y) :
    Homotopic ((Walk.nil : G.Walk x x).copy rfl e) (Walk.cons h (Walk.cons h' Walk.nil)) := by
  subst y
  rw [show h' = h.symm from Subsingleton.elim _ _]
  exact (homotopic_cons_cons_nil h).symm

theorem homotopic_two_edge_of_eq {V : Type} {G : SimpleGraph V} {W U L L' : V}
    (hL : L' = L) (a : G.Adj W L') (b : G.Adj L' U) (a' : G.Adj W L) (b' : G.Adj L U) :
    Homotopic (Walk.cons a (Walk.cons b Walk.nil)) (Walk.cons a' (Walk.cons b' Walk.nil)) := by
  cases hL
  rw [Subsingleton.elim a a', Subsingleton.elim b b']

theorem homotopic_four_cycle {V : Type} {G : SimpleGraph V} {u l w : V}
    (a : G.Walk u l) (q : G.Walk l w) (d : G.Adj w u) (f : G.Adj l w)
    (h1 : Homotopic q (Walk.cons f Walk.nil))
    (h2 : Homotopic (a.append (Walk.cons f Walk.nil)) (Walk.cons d.symm Walk.nil)) :
    Homotopic (a.append (q.append (Walk.cons d Walk.nil))) .nil := by
  have hq : Homotopic (a.append (q.append (Walk.cons d Walk.nil)))
      (a.append (Walk.cons f (Walk.cons d Walk.nil))) := by
    have := (h1.append_right (Walk.cons d Walk.nil)).append_left a
    simpa [← Walk.append_assoc] using this
  have hfd : Homotopic (a.append (Walk.cons f (Walk.cons d Walk.nil))) .nil := by
    have h2' := h2.append_right (Walk.cons d Walk.nil)
    have hb : Homotopic ((Walk.cons d.symm Walk.nil).append (Walk.cons d Walk.nil)) .nil := by
      simpa using homotopic_reverse_append (Walk.cons d Walk.nil)
    simpa [← Walk.append_assoc] using h2'.trans hb
  exact hq.trans hfd

end CFSG.ClassicalInvolution.Phan.Geometry

end
