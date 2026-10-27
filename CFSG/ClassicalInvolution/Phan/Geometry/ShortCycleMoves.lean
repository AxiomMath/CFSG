module

public import CFSG.ClassicalInvolution.Phan.Geometry.WalkHomotopy
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ClassicalInvolution.Phan

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (E : ∀ x : V, Set (G.Walk x x))

abbrev triWalk {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    G.Walk a a :=
  .cons hab (.cons hbc (.cons hca .nil))

abbrev quadWalk {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hda : G.Adj d a) : G.Walk a a :=
  .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))

abbrev pentWalk {a b c d e : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) : G.Walk a a :=
  .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hea .nil))))

@[expose] def NullLen (k : ℕ) : Prop :=
  ∀ {u : V} (p : G.Walk u u), p.length = k → CycleHomotopic E p .nil

theorem cycleHomotopic_nil_of_nullLen (h3 : NullLen E 3) (h4 : NullLen E 4)
    (h5 : NullLen E 5) {u : V} (p : G.Walk u u) (hp : p.length ≤ 5) :
    CycleHomotopic E p .nil := by
  match u, p, hp with
  | _, .nil, _ => exact CycleHomotopic.refl _
  | _, .cons h₁ .nil, _ => exact absurd h₁ (G.loopless.irrefl _)
  | _, .cons h₁ (.cons _ .nil), _ => exact cycleHomotopic_cons_cons_nil E h₁
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ =>
    exact h3 (.cons h₁ (.cons h₂ (.cons h₃ .nil))) rfl
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
    exact h4 (.cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil)))) rfl
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil)))), _ =>
    exact h5 (.cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil))))) rfl
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem cycleTrivial_of_nullLen (hconn : G.Connected) (hdiam : G.ediam ≤ 2)
    (h3 : NullLen E 3) (h4 : NullLen E 4) (h5 : NullLen E 5) : CycleTrivial E := by
  have hfin : G.ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hdiam
  have hd : G.diam ≤ 2 := ENat.toNat_le_of_le_natCast hdiam
  refine cycleTrivial_of_diam E hconn hfin fun u p hp => ?_
  exact cycleHomotopic_nil_of_nullLen E h3 h4 h5 p (by omega)

theorem cycleHomotopic_of_append_nil {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (h : CycleHomotopic E (p.append q) .nil) : CycleHomotopic E p q.reverse := by
  refine cycleHomotopic_of_append_reverse E (p := p) (q := q.reverse) ?_
  simpa using h

theorem cycleHomotopic_rotate {a b : V} (hab : G.Adj a b) (t : G.Walk b a)
    (h : CycleHomotopic E (.cons hab t) .nil) :
    CycleHomotopic E (t.append (.cons hab .nil)) .nil := by
  have h₁ : CycleHomotopic E t (.cons hab.symm .nil) := by
    have hb : CycleHomotopic E
        ((.cons hab.symm (.cons hab .nil) : G.Walk b b).append t) t := by
      simpa using (cycleHomotopic_cons_cons_nil E hab.symm).append_right t
    refine hb.symm.trans ?_
    have h' := h.append_left (.cons hab.symm .nil : G.Walk b a)
    simpa using h'
  exact (h₁.append_right (.cons hab .nil)).trans
    (cycleHomotopic_cons_cons_nil E hab.symm)

theorem cycleHomotopic_quad_rotate {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a)
    (h : CycleHomotopic E (quadWalk hab hbc hcd hda) .nil) :
    CycleHomotopic E (quadWalk hbc hcd hda hab) .nil := by
  simpa [quadWalk] using
    cycleHomotopic_rotate E hab (.cons hbc (.cons hcd (.cons hda .nil)) : G.Walk b a) h

theorem cycleHomotopic_quad_rotate_rev {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a)
    (h : CycleHomotopic E (quadWalk hbc hcd hda hab) .nil) :
    CycleHomotopic E (quadWalk hab hbc hcd hda) .nil :=
  cycleHomotopic_quad_rotate E hda hab hbc hcd
    (cycleHomotopic_quad_rotate E hcd hda hab hbc
      (cycleHomotopic_quad_rotate E hbc hcd hda hab h))

theorem cycleHomotopic_pent_rotate {a b c d e : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hde : G.Adj d e) (hea : G.Adj e a)
    (h : CycleHomotopic E (pentWalk hab hbc hcd hde hea) .nil) :
    CycleHomotopic E (pentWalk hbc hcd hde hea hab) .nil := by
  simpa [pentWalk] using
    cycleHomotopic_rotate E hab
      (.cons hbc (.cons hcd (.cons hde (.cons hea .nil))) : G.Walk b a) h

theorem cycleHomotopic_pent_reverse (hE : ∀ x (c : G.Walk x x), c ∈ E x → c.reverse ∈ E x)
    {a b c d e : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a)
    (h : CycleHomotopic E (pentWalk hab hbc hcd hde hea) .nil) :
    CycleHomotopic E (pentWalk hea.symm hde.symm hcd.symm hbc.symm hab.symm) .nil := by
  simpa [pentWalk, Walk.reverse_cons] using CycleHomotopic.reverse (E := E) hE h

theorem cycleHomotopic_quad_trans {a b c d p : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcp : G.Adj c p) (hpa : G.Adj p a) (hcd : G.Adj c d) (hda : G.Adj d a)
    (h₁ : CycleHomotopic E (quadWalk hab hbc hcp hpa) .nil)
    (h₂ : CycleHomotopic E (quadWalk hpa.symm hcp.symm hcd hda) .nil) :
    CycleHomotopic E (quadWalk hab hbc hcd hda) .nil := by
  let u : G.Walk a p := .cons hab (.cons hbc (.cons hcp .nil))
  let v : G.Walk p a := .cons hcp.symm (.cons hcd (.cons hda .nil))
  have h₁' : CycleHomotopic E u (.cons hpa.symm .nil) := by
    have h := cycleHomotopic_of_append_nil E (p := u) (q := (.cons hpa .nil : G.Walk p a))
      (by simpa [u, quadWalk] using h₁)
    simpa [u, Walk.reverse_cons] using h
  have h₂' : CycleHomotopic E v (.cons hpa .nil) := by
    have hrot : CycleHomotopic E (v.append (.cons hpa.symm .nil)) .nil := by
      have h := cycleHomotopic_rotate E hpa.symm
        (.cons hcp.symm (.cons hcd (.cons hda .nil)) : G.Walk p a) h₂
      simpa [v] using h
    have h := cycleHomotopic_of_append_nil E (p := v)
      (q := (.cons hpa.symm .nil : G.Walk a p)) hrot
    simpa [Walk.reverse_cons] using h
  have hq : CycleHomotopic E (quadWalk hab hbc hcd hda) (u.append v) := by
    have h := cycleHomotopic_backtrack E (.cons hab (.cons hbc .nil) : G.Walk a c)
      (.cons hcd (.cons hda .nil) : G.Walk c a) hcp
    simpa [u, v, quadWalk, Walk.append_assoc] using h
  refine hq.trans ?_
  refine ((h₁'.append h₂').trans ?_)
  simpa using cycleHomotopic_cons_cons_nil E hpa.symm

theorem cycleHomotopic_of_quad_nil_through {x y z w : V} (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hzw : G.Adj z w) (hwx : G.Adj w x)
    (h : CycleHomotopic E (quadWalk hxy hyz hzw hwx) .nil) :
    CycleHomotopic E (.cons hxy (.cons hyz .nil) : G.Walk x z)
      (.cons hwx.symm (.cons hzw.symm .nil) : G.Walk x z) := by
  have h' : CycleHomotopic E
      ((.cons hxy (.cons hyz .nil) : G.Walk x z).append
        (.cons hzw (.cons hwx .nil))) .nil := by
    simpa [quadWalk] using h
  have h'' := cycleHomotopic_of_append_nil E
    (p := (.cons hxy (.cons hyz .nil) : G.Walk x z))
    (q := (.cons hzw (.cons hwx .nil) : G.Walk z x)) h'
  simpa [Walk.reverse_cons] using h''

theorem cycleHomotopic_quad_wheel (h3 : NullLen E 3) {a b c d m₁ m₂ m₃ m₄ e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hm₁a : G.Adj m₁ a) (hm₁b : G.Adj m₁ b) (hm₁e : G.Adj m₁ e)
    (hm₂b : G.Adj m₂ b) (hm₂c : G.Adj m₂ c) (hm₂e : G.Adj m₂ e)
    (hm₃c : G.Adj m₃ c) (hm₃d : G.Adj m₃ d) (hm₃e : G.Adj m₃ e)
    (hm₄d : G.Adj m₄ d) (hm₄a : G.Adj m₄ a) (hm₄e : G.Adj m₄ e)
    (hSa : CycleHomotopic E (quadWalk hm₁a.symm hm₁e hm₄e.symm hm₄a) .nil)
    (hSb : CycleHomotopic E (quadWalk hm₁b hm₂b.symm hm₂e hm₁e.symm) .nil)
    (hSc : CycleHomotopic E (quadWalk hm₂c hm₃c.symm hm₃e hm₂e.symm) .nil)
    (hSd : CycleHomotopic E (quadWalk hm₃d hm₄d.symm hm₄e hm₃e.symm) .nil) :
    CycleHomotopic E (quadWalk hab hbc hcd hda) .nil := by
  let P₁ : G.Walk a m₁ := .cons hm₁a.symm .nil
  let E₁ : G.Walk m₁ e := .cons hm₁e .nil
  let G₂ : G.Walk e m₂ := .cons hm₂e.symm .nil
  let E₂ : G.Walk m₂ e := .cons hm₂e .nil
  let G₃ : G.Walk e m₃ := .cons hm₃e.symm .nil
  let E₃ : G.Walk m₃ e := .cons hm₃e .nil
  let G₄ : G.Walk e m₄ := .cons hm₄e.symm .nil
  let F₄ : G.Walk m₄ e := .cons hm₄e .nil
  let A : G.Walk a m₄ := .cons hm₄a.symm .nil
  let P₂ : G.Walk m₄ a := .cons hm₄a .nil
  let U₂ : G.Walk m₁ m₂ := .cons hm₁b (.cons hm₂b.symm .nil)
  let W₂ : G.Walk m₁ m₂ := E₁.append G₂
  let U₃ : G.Walk m₂ m₃ := .cons hm₂c (.cons hm₃c.symm .nil)
  let W₃ : G.Walk m₂ m₃ := E₂.append G₃
  let U₄ : G.Walk m₃ m₄ := .cons hm₃d (.cons hm₄d.symm .nil)
  let W₄ : G.Walk m₃ m₄ := E₃.append G₄
  have hb : CycleHomotopic E U₂ W₂ := by
    have h := cycleHomotopic_of_quad_nil_through E hm₁b hm₂b.symm hm₂e hm₁e.symm hSb
    simpa [U₂, W₂, E₁, G₂] using h
  have hc : CycleHomotopic E U₃ W₃ := by
    have h := cycleHomotopic_of_quad_nil_through E hm₂c hm₃c.symm hm₃e hm₂e.symm hSc
    simpa [U₃, W₃, E₂, G₃] using h
  have hd : CycleHomotopic E U₄ W₄ := by
    have h := cycleHomotopic_of_quad_nil_through E hm₃d hm₄d.symm hm₄e hm₃e.symm hSd
    simpa [U₄, W₄, E₃, G₄] using h
  have ha : CycleHomotopic E (P₁.append E₁) (A.append F₄) := by
    have h := cycleHomotopic_of_quad_nil_through E hm₁a.symm hm₁e hm₄e.symm hm₄a hSa
    simpa [P₁, E₁, A, F₄] using h
  have t_ab : CycleHomotopic E (.cons hab .nil : G.Walk a b)
      (.cons hm₁a.symm (.cons hm₁b .nil)) :=
    cycleHomotopic_replace_edge E hab hm₁a.symm hm₁b.symm
      (h3 (triWalk hab hm₁b.symm hm₁a) rfl)
  have t_bc : CycleHomotopic E (.cons hbc .nil : G.Walk b c)
      (.cons hm₂b.symm (.cons hm₂c .nil)) :=
    cycleHomotopic_replace_edge E hbc hm₂b.symm hm₂c.symm
      (h3 (triWalk hbc hm₂c.symm hm₂b) rfl)
  have t_cd : CycleHomotopic E (.cons hcd .nil : G.Walk c d)
      (.cons hm₃c.symm (.cons hm₃d .nil)) :=
    cycleHomotopic_replace_edge E hcd hm₃c.symm hm₃d.symm
      (h3 (triWalk hcd hm₃d.symm hm₃c) rfl)
  have t_da : CycleHomotopic E (.cons hda .nil : G.Walk d a)
      (.cons hm₄d.symm (.cons hm₄a .nil)) :=
    cycleHomotopic_replace_edge E hda hm₄d.symm hm₄a.symm
      (h3 (triWalk hda hm₄a.symm hm₄d) rfl)
  have hqq' : CycleHomotopic E (quadWalk hab hbc hcd hda)
      (P₁.append (U₂.append (U₃.append (U₄.append P₂)))) := by
    have h := (t_ab.append t_bc).append (t_cd.append t_da)
    simpa [quadWalk, P₁, U₂, U₃, U₄, P₂, Walk.append_assoc] using h
  let R : G.Walk a a := P₁.append (W₂.append (W₃.append (W₄.append P₂)))
  have hq'R : CycleHomotopic E (P₁.append (U₂.append (U₃.append (U₄.append P₂)))) R := by
    have h := ((hb.append hc).append hd).append_left P₁ |>.append_right P₂
    simpa [R, Walk.append_assoc] using h
  let T : G.Walk a a := (P₁.append E₁).append (G₄.append P₂)
  have hTS : CycleHomotopic E T R := by
    have h₃ : CycleHomotopic E T ((P₁.append E₁).append
        ((G₃.append E₃).append (G₄.append P₂))) := by
      have h := cycleHomotopic_backtrack E (P₁.append E₁) (G₄.append P₂) hm₃e.symm
      simpa [T, G₃, E₃, Walk.append_assoc] using h
    have h₂ : CycleHomotopic E ((P₁.append E₁).append
        ((G₃.append E₃).append (G₄.append P₂))) R := by
      have h := cycleHomotopic_backtrack E (P₁.append E₁)
        ((G₃.append E₃).append (G₄.append P₂)) hm₂e.symm
      simpa [R, W₂, W₃, W₄, E₁, G₂, E₂, G₃, E₃, G₄, P₁, P₂,
        Walk.append_assoc, Walk.cons_append, Walk.nil_append, Walk.append_nil] using h
    exact h₃.trans h₂
  have hTn : CycleHomotopic E T .nil := by
    have hmid : CycleHomotopic E T ((A.append F₄).append (G₄.append P₂)) := by
      have h := ha.append (CycleHomotopic.refl (G₄.append P₂))
      simpa [T] using h
    have hback : CycleHomotopic E (A.append (.cons hm₄e (.cons hm₄e.symm P₂)))
        (A.append P₂) :=
      (cycleHomotopic_insert_null E A P₂
        (cycleHomotopic_cons_cons_nil E hm₄e)).symm
    exact hmid.trans (hback.trans (cycleHomotopic_cons_cons_nil E hm₄a.symm))
  exact hqq'.trans (hq'R.trans (hTS.symm.trans hTn))

theorem cycleHomotopic_pent_nil_of_apex (h3 : NullLen E 3) (h4 : NullLen E 4)
    {a b c d e f : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) (hfc : G.Adj f c) (hfd : G.Adj f d)
    (haf : G.Adj a f) :
    CycleHomotopic E (pentWalk hab hbc hcd hde hea) .nil := by
  have hT : CycleHomotopic E (.cons hcd (.cons hfd.symm (.cons hfc.symm.symm .nil)) :
      G.Walk c c) .nil := h3 _ rfl
  have hrep := cycleHomotopic_replace_edge E hcd hfc.symm hfd.symm hT
  have hreplace : CycleHomotopic E
      (.cons hab (.cons hbc (.cons hcd (.cons hde (.cons hea .nil)))) : G.Walk a a)
      (.cons hab (.cons hbc (.cons hfc.symm (.cons hfd (.cons hde (.cons hea .nil)))))) := by
    have := (hrep.append_right (.cons hde (.cons hea .nil))).append_left
      (.cons hab (.cons hbc .nil))
    simpa using this
  have hinsert : CycleHomotopic E
      (.cons hab (.cons hbc (.cons hfc.symm (.cons hfd (.cons hde (.cons hea .nil))))) :
        G.Walk a a)
      (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm (.cons haf
        (.cons hfd (.cons hde (.cons hea .nil)))))))) := by
    have := cycleHomotopic_backtrack E (.cons hab (.cons hbc (.cons hfc.symm .nil)) : G.Walk a f)
      (.cons hfd (.cons hde (.cons hea .nil))) haf.symm
    simpa using this
  have hsplit : CycleHomotopic E
      (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm (.cons haf
        (.cons hfd (.cons hde (.cons hea .nil))))))) : G.Walk a a) .nil := by
    have e₁ : (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm (.cons haf
        (.cons hfd (.cons hde (.cons hea .nil))))))) : G.Walk a a) =
        (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm .nil))) : G.Walk a a).append
          (.cons haf (.cons hfd (.cons hde (.cons hea .nil)))) := by simp
    rw [e₁]
    have q₁ := h4 (.cons hab (.cons hbc (.cons hfc.symm (.cons haf.symm .nil))) : G.Walk a a)
      rfl
    have q₂ := h4 (.cons haf (.cons hfd (.cons hde (.cons hea .nil))) : G.Walk a a) rfl
    simpa using q₁.append q₂
  exact hreplace.trans (hinsert.trans hsplit)

theorem cycleHomotopic_pent_of_split {a b c d e f : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hde : G.Adj d e) (hea : G.Adj e a) (hdf : G.Adj d f)
    (hfa : G.Adj f a)
    (h₁ : CycleHomotopic E (pentWalk hab hbc hcd hdf hfa) .nil)
    (h₂ : CycleHomotopic E (quadWalk hfa.symm hdf.symm hde hea) .nil) :
    CycleHomotopic E (pentWalk hab hbc hcd hde hea) .nil := by
  let u : G.Walk a d := .cons hab (.cons hbc (.cons hcd .nil))
  let w : G.Walk d a := .cons hde (.cons hea .nil)
  let v : G.Walk a d := .cons hfa.symm (.cons hdf.symm .nil)
  have h₁' : CycleHomotopic E u v := by
    have h := cycleHomotopic_of_append_nil E (p := u)
      (q := (.cons hdf (.cons hfa .nil) : G.Walk d a))
      (by simpa [u, pentWalk] using h₁)
    simpa [u, v, Walk.reverse_cons] using h
  have h₂' : CycleHomotopic E v w.reverse := by
    have h := cycleHomotopic_of_append_nil E (p := v) (q := w)
      (by simpa [v, w, quadWalk] using h₂)
    simpa [v, w] using h
  have hstart : CycleHomotopic E (pentWalk hab hbc hcd hde hea) (u.append w) := by
    simpa [pentWalk, u, w] using CycleHomotopic.refl (u.append w)
  refine hstart.trans ?_
  refine ((h₁'.append (CycleHomotopic.refl w)).trans (h₂'.append_right w)).trans ?_
  exact cycleHomotopic_reverse_append E w

end CFSG.ClassicalInvolution.Phan
