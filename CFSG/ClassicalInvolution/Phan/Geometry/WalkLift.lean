module

public import CFSG.ClassicalInvolution.Phan.Geometry.WalkHomotopy
public import CFSG.ClassicalInvolution.Phan.Geometry.WalkSubstitution

public section

namespace CFSG.ClassicalInvolution.Phan.Geometry

open SimpleGraph CFSG.Monster.B.Recog

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

@[expose] def liftNull (i : W → V) (expand : ∀ {u v}, H.Adj u v → G.Walk (i u) (i v)) (x : W) :
    Set (H.Walk x x) :=
  {c | Homotopic (substituteWalk i expand c) .nil}

theorem homotopic_substituteWalk_of_cycleHomotopic (i : W → V)
    (expand : ∀ {u v}, H.Adj u v → G.Walk (i u) (i v))
    (hback : ∀ {u v} (h : H.Adj u v), Homotopic ((expand h).append (expand h.symm)) .nil)
    {u v : W} {p q : H.Walk u v} (h : CycleHomotopic (liftNull i expand) p q) :
    Homotopic (substituteWalk i expand p) (substituteWalk i expand q) := by
  induction h with
  | rel p q hmove =>
    cases hmove with
    | backtrack a b e =>
      simp only [substituteWalk_append, substituteWalk_cons]
      have hb := (hback e).symm.append_right (substituteWalk i expand b)
      simpa only [Walk.append_assoc, Walk.nil_append] using
        hb.append_left (substituteWalk i expand a)
    | elem a b c hc =>
      simp only [substituteWalk_append]
      have hc' := (hc.append_right (substituteWalk i expand b)).append_left
        (substituteWalk i expand a)
      simpa only [Walk.append_assoc, Walk.nil_append] using hc'.symm
  | refl p => exact Homotopic.refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem triangulable_of_cycleTrivial_liftNull (i : W → V) (r : V → W)
    (expand : ∀ {u v}, H.Adj u v → G.Walk (i u) (i v))
    (reduce : ∀ {u v}, G.Adj u v → H.Walk (r u) (r v))
    (connector : ∀ u, G.Walk u (i (r u)))
    (hback : ∀ {u v} (h : H.Adj u v), Homotopic ((expand h).append (expand h.symm)) .nil)
    (hedge : ∀ {u v} (h : G.Adj u v),
      Homotopic ((connector u).append (substituteWalk i expand (reduce h)))
        ((Walk.cons h .nil).append (connector v)))
    (hH : CycleTrivial (liftNull i expand)) : Triangulable G := by
  intro u p
  have hp : Homotopic (substituteWalk i expand (substituteWalk r reduce p)) .nil := by
    simpa only [substituteWalk_nil] using
      homotopic_substituteWalk_of_cycleHomotopic i expand hback
        (hH (r u) (substituteWalk r reduce p))
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

end CFSG.ClassicalInvolution.Phan.Geometry
