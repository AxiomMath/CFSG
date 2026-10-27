module

public import CFSG.Combinatorics.AperiodicSixteenGraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Combinatorics.AperiodicSixteenGraph

variable {Ω : Type*}

@[expose] def colourGraph (r : Fin 3 → Ω → Ω) : SimpleGraph Ω :=
  SimpleGraph.fromRel fun x y => ∃ i, y = r i x

theorem colourGraph_adj {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x) {x y : Ω} :
    (colourGraph r).Adj x y ↔ x ≠ y ∧ ∃ i, y = r i x := by
  rw [colourGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, ⟨i, h⟩ | ⟨i, h⟩⟩
    · exact ⟨hxy, i, h⟩
    · exact ⟨hxy, i, by rw [h, hinv]⟩
  · rintro ⟨hxy, i, h⟩
    exact ⟨hxy, Or.inl ⟨i, h⟩⟩

theorem colourGraph_adj_r {r : Fin 3 → Ω → Ω} (hfix : ∀ i x, r i x ≠ x) (i : Fin 3) (x : Ω) :
    (colourGraph r).Adj x (r i x) := by
  rw [colourGraph, SimpleGraph.fromRel_adj]
  exact ⟨(hfix i x).symm, Or.inl ⟨i, rfl⟩⟩

private theorem exists_isCycle_three {V : Type*} {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 3 := by
  refine ⟨.cons hab (.cons hbc (.cons hca .nil)), ?_, rfl⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  simp [hab.ne, hab.ne.symm, hbc.ne, hca.ne, hca.ne.symm]

private theorem exists_isCycle_four {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c)
    (hbd : b ≠ d) : ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 4 := by
  refine ⟨.cons hab (.cons hbc (.cons hcd (.cons hda .nil))), ?_, rfl⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  simp [hab.ne, hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hda.ne.symm, hac, hac.symm, hbd]

private def sq (r : Fin 3 → Ω → Ω) (a b : Fin 3) (x : Ω) : Ω :=
  r b (r a (r b (r a x)))

private def zmap (r : Fin 3 → Ω → Ω) (x : Ω) : Ω :=
  sq r 0 1 x

private theorem sq_sq {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x) (a b : Fin 3) (x : Ω) :
    sq r a b (sq r b a x) = x := by
  simp only [sq, hinv]

private theorem sq_eq {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (x : Ω) :
    sq r a b x = sq r a c x := by
  have h := congrArg (r c) (hrel a b c hab hbc hac (r b (r a x)))
  simp only [hinv] at h
  exact h

private theorem sq_one_two {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (x : Ω) : sq r 1 2 x = zmap r x := by
  have e : sq r 2 1 (sq r 0 2 x) = x := by
    rw [← sq_eq hinv hrel (by decide : (2 : Fin 3) ≠ 0) (by decide) (by decide)]
    exact sq_sq hinv 2 0 x
  calc sq r 1 2 x = sq r 1 2 (sq r 2 1 (sq r 0 2 x)) := by rw [e]
    _ = sq r 0 2 x := sq_sq hinv 1 2 _
    _ = zmap r x := sq_eq hinv hrel (by decide) (by decide) (by decide) x

private theorem zmap_zmap {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (x : Ω) : zmap r (zmap r x) = x := by
  have h : sq r 1 0 x = zmap r x :=
    (sq_eq hinv hrel (by decide : (1 : Fin 3) ≠ 0) (by decide) (by decide) x).trans
      (sq_one_two hinv hrel x)
  conv_lhs => rw [← h]
  exact sq_sq hinv 0 1 x

private theorem sq_eq_zmap {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    {a b : Fin 3} (hab : a ≠ b) (x : Ω) : sq r a b x = zmap r x := by
  have h12 := sq_one_two hinv hrel
  have h21 : ∀ x, sq r 2 1 x = zmap r x := fun x => by
    conv_lhs => rw [← zmap_zmap hinv hrel x, ← h12 (zmap r x)]
    exact sq_sq hinv 2 1 _
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · rfl
  · exact sq_eq hinv hrel (by decide) (by decide) (by decide) x
  · exact (sq_eq hinv hrel (by decide) (by decide) (by decide) x).trans (h12 x)
  · exact absurd rfl hab
  · exact h12 x
  · exact (sq_eq hinv hrel (by decide) (by decide) (by decide) x).trans (h21 x)
  · exact h21 x
  · exact absurd rfl hab

private theorem comm {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    {a b : Fin 3} (hab : a ≠ b) (y : Ω) : r b (r a y) = zmap r (r a (r b y)) := by
  have h := sq_eq_zmap hinv hrel hab (r a (r b y))
  simp only [sq, hinv] at h
  exact h

private theorem r_zmap {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (i : Fin 3) (x : Ω) : r i (zmap r x) = zmap r (r i x) := by
  obtain ⟨b, hib⟩ : ∃ b : Fin 3, i ≠ b := ⟨i + 1, by fin_cases i <;> decide⟩
  rw [← sq_eq_zmap hinv hrel hib x, ← sq_eq_zmap hinv hrel hib.symm (r i x)]
  rfl

private def rIter (r : Fin 3 → Ω → Ω) (i : Fin 3) (e : ZMod 2) (x : Ω) : Ω :=
  if e = 1 then r i x else x

private def zIter (r : Fin 3 → Ω → Ω) (e : ZMod 2) (x : Ω) : Ω :=
  if e = 1 then zmap r x else x

private def act (r : Fin 3 → Ω → Ω) (g : K) (x : Ω) : Ω :=
  zIter r g.cen (rIter r 2 (g.vec 2) (rIter r 1 (g.vec 1) (rIter r 0 (g.vec 0) x)))

private theorem zmod_two (e : ZMod 2) : e = 0 ∨ e = 1 := by
  revert e
  decide

private theorem rIter_zero (r : Fin 3 → Ω → Ω) (i : Fin 3) (x : Ω) : rIter r i 0 x = x :=
  ite_eq_right (by decide)

private theorem rIter_one (r : Fin 3 → Ω → Ω) (i : Fin 3) (x : Ω) : rIter r i 1 x = r i x :=
  ite_eq_left rfl

private theorem zIter_zero (r : Fin 3 → Ω → Ω) (x : Ω) : zIter r 0 x = x :=
  ite_eq_right (by decide)

private theorem zIter_one (r : Fin 3 → Ω → Ω) (x : Ω) : zIter r 1 x = zmap r x :=
  ite_eq_left rfl

private theorem r_rIter_self {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x) (i : Fin 3)
    (e : ZMod 2) (y : Ω) : r i (rIter r i e y) = rIter r i (e + 1) y := by
  rcases zmod_two e with rfl | rfl
  · rw [rIter_zero, zero_add, rIter_one]
  · rw [rIter_one, hinv, show (1 : ZMod 2) + 1 = 0 by decide, rIter_zero]

private theorem r_zIter {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (i : Fin 3) (e : ZMod 2) (y : Ω) : r i (zIter r e y) = zIter r e (r i y) := by
  rcases zmod_two e with rfl | rfl
  · rw [zIter_zero, zIter_zero]
  · rw [zIter_one, zIter_one, r_zmap hinv hrel]

private theorem r_rIter_ne {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    {a b : Fin 3} (hab : a ≠ b) (e : ZMod 2) (y : Ω) :
    r a (rIter r b e y) = zIter r e (rIter r b e (r a y)) := by
  rcases zmod_two e with rfl | rfl
  · rw [rIter_zero, rIter_zero, zIter_zero]
  · rw [rIter_one, rIter_one, zIter_one, comm hinv hrel hab.symm]

private theorem rIter_zIter {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (i : Fin 3) (e e' : ZMod 2) (y : Ω) :
    rIter r i e (zIter r e' y) = zIter r e' (rIter r i e y) := by
  rcases zmod_two e with rfl | rfl
  · rw [rIter_zero, rIter_zero]
  · rw [rIter_one, rIter_one, r_zIter hinv hrel]

private theorem zIter_zIter {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (e e' : ZMod 2) (y : Ω) : zIter r e (zIter r e' y) = zIter r (e + e') y := by
  rcases zmod_two e with rfl | rfl <;> rcases zmod_two e' with rfl | rfl
  · rw [zIter_zero, zIter_zero, add_zero, zIter_zero]
  · rw [zIter_zero, zero_add]
  · rw [zIter_zero, add_zero]
  · rw [zIter_one, zIter_one, zmap_zmap hinv hrel, show (1 : ZMod 2) + 1 = 0 by decide,
      zIter_zero]

private theorem act_mul_s {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (g : K) (i : Fin 3) (x : Ω) : act r (g * s i) x = r i (act r g x) := by
  rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
  · have h0 : (g * s 0).vec 0 = g.vec 0 + 1 := by simp [s]
    have h1 : (g * s 0).vec 1 = g.vec 1 := by simp [s]
    have h2 : (g * s 0).vec 2 = g.vec 2 := by simp [s]
    have hc : (g * s 0).cen = g.cen + g.vec 2 + g.vec 1 := by
      simp [s, form_eq]
      ring
    simp only [act, h0, h1, h2, hc]
    rw [r_zIter hinv hrel, r_rIter_ne hinv hrel (by decide : (0 : Fin 3) ≠ 2),
      r_rIter_ne hinv hrel (by decide : (0 : Fin 3) ≠ 1), r_rIter_self hinv,
      rIter_zIter hinv hrel, zIter_zIter hinv hrel, zIter_zIter hinv hrel]
  · have h0 : (g * s 1).vec 0 = g.vec 0 := by simp [s]
    have h1 : (g * s 1).vec 1 = g.vec 1 + 1 := by simp [s]
    have h2 : (g * s 1).vec 2 = g.vec 2 := by simp [s]
    have hc : (g * s 1).cen = g.cen + g.vec 2 := by simp [s, form_eq]
    simp only [act, h0, h1, h2, hc]
    rw [r_zIter hinv hrel, r_rIter_ne hinv hrel (by decide : (1 : Fin 3) ≠ 2),
      r_rIter_self hinv, zIter_zIter hinv hrel]
  · have h0 : (g * s 2).vec 0 = g.vec 0 := by simp [s]
    have h1 : (g * s 2).vec 1 = g.vec 1 := by simp [s]
    have h2 : (g * s 2).vec 2 = g.vec 2 + 1 := by simp [s]
    have hc : (g * s 2).cen = g.cen := by simp [s, form_eq]
    simp only [act, h0, h1, h2, hc]
    rw [r_zIter hinv hrel, r_rIter_self hinv]

private theorem act_one (r : Fin 3 → Ω → Ω) (x : Ω) : act r 1 x = x := by
  simp only [act, K.one_vec, K.one_cen, Pi.zero_apply, rIter_zero, zIter_zero]

private def sIter (i : Fin 3) (e : ZMod 2) : K :=
  if e = 1 then s i else 1

private def zElt (e : ZMod 2) : K :=
  if e = 1 then z else 1

private theorem normal_form :
    ∀ g : K, g = sIter 0 (g.vec 0) * sIter 1 (g.vec 1) * sIter 2 (g.vec 2) * zElt g.cen := by
  decide

private theorem z_eq : z = s 0 * s 1 * s 0 * s 1 := by
  decide

private theorem eq_act {r : Fin 3 → Ω → Ω} {ψ : K → Ω} {y : Ω} (h1 : ψ 1 = y)
    (hψ : ∀ g i, ψ (g * s i) = r i (ψ g)) (g : K) : ψ g = act r g y := by
  have hs : ∀ g i e, ψ (g * sIter i e) = rIter r i e (ψ g) := by
    intro g i e
    rcases zmod_two e with rfl | rfl
    · rw [sIter, ite_eq_right (by decide), mul_one, rIter_zero]
    · rw [sIter, ite_eq_left rfl, hψ, rIter_one]
  have hz : ∀ g e, ψ (g * zElt e) = zIter r e (ψ g) := by
    intro g e
    rcases zmod_two e with rfl | rfl
    · rw [zElt, ite_eq_right (by decide), mul_one, zIter_zero]
    · rw [zElt, ite_eq_left rfl, zIter_one, z_eq, ← mul_assoc, ← mul_assoc, ← mul_assoc, hψ, hψ,
        hψ, hψ]
      rfl
  conv_lhs => rw [normal_form g, ← one_mul (sIter 0 (g.vec 0))]
  rw [hz, hs, hs, hs, h1]
  rfl

private theorem act_mul {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (g h : K) (x : Ω) : act r (g * h) x = act r h (act r g x) :=
  eq_act (ψ := fun h => act r (g * h) x) (by rw [mul_one])
    (fun h i => by rw [← mul_assoc, act_mul_s hinv hrel]) h

private theorem short_words : ∀ k : K, k = 1 ∨ (∃ a, k = s a) ∨
    (∃ a b, a ≠ b ∧ k = s a * s b) ∨ (∃ a b c, k = s a * s b * s c) ∨
    ∃ a b, a ≠ b ∧ k = s a * s b * s a * s b := by
  decide

private theorem rr_ne {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hdist : ∀ x, Function.Injective fun i => r i x) {a b : Fin 3} (hab : a ≠ b) (x : Ω) :
    r b (r a x) ≠ x := by
  intro h
  apply hab
  apply hdist x
  show r a x = r b x
  rw [← hinv b (r a x), h]

private theorem act_ne {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hfix : ∀ i x, r i x ≠ x) (hdist : ∀ x, Function.Injective fun i => r i x)
    (hcyc : ∀ x (p : (colourGraph r).Walk x x), p.IsCycle → p.length ≠ 3 ∧ p.length ≠ 4)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    {k : K} (hk : k ≠ 1) (x : Ω) : act r k x ≠ x := by
  have hs : ∀ a y, act r (s a) y = r a y := fun a y => by
    rw [← one_mul (s a), act_mul_s hinv hrel, act_one]
  have hadj := colourGraph_adj_r hfix
  rcases short_words k with rfl | ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩ | ⟨a, b, c, rfl⟩ |
    ⟨a, b, hab, rfl⟩
  · exact absurd rfl hk
  · rw [hs]
    exact hfix a x
  · rw [act_mul_s hinv hrel, hs]
    exact rr_ne hinv hdist hab x
  ·
    rw [act_mul_s hinv hrel, act_mul_s hinv hrel, hs]
    intro h
    have h3 := hadj c (r b (r a x))
    rw [h] at h3
    obtain ⟨p, hp, hl⟩ := exists_isCycle_three (hadj a x) (hadj b (r a x)) h3
    exact (hcyc x p hp).1 hl
  ·
    rw [act_mul_s hinv hrel, act_mul_s hinv hrel, act_mul_s hinv hrel, hs]
    intro h
    have h4 := hadj b (r a (r b (r a x)))
    rw [h] at h4
    obtain ⟨p, hp, hl⟩ := exists_isCycle_four (hadj a x) (hadj b (r a x))
      (hadj a (r b (r a x))) h4 (rr_ne hinv hdist hab x).symm
      (rr_ne hinv hdist hab.symm (r a x)).symm
    exact (hcyc x p hp).2 hl

theorem existsUnique_colour_equiv {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hfix : ∀ i x, r i x ≠ x) (hdist : ∀ x, Function.Injective fun i => r i x)
    (hconn : (colourGraph r).Connected)
    (hcyc : ∀ x (p : (colourGraph r).Walk x x), p.IsCycle → p.length ≠ 3 ∧ p.length ≠ 4)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x)))
    (ω₀ : Ω) : ∃! φ : K ≃ Ω, φ o = ω₀ ∧ ∀ g i, φ (g * s i) = r i (φ g) := by
  have hinj : Function.Injective fun g => act r g ω₀ := by
    intro g h hgh
    have hfix' : act r (g * h⁻¹) ω₀ = ω₀ := by
      rw [act_mul hinv hrel, show act r g ω₀ = act r h ω₀ from hgh, ← act_mul hinv hrel,
        mul_inv_cancel, act_one]
    by_contra hne
    exact act_ne hinv hfix hdist hcyc hrel (fun h1 => hne (mul_inv_eq_one.mp h1)) ω₀ hfix'
  have hsurj : Function.Surjective fun g => act r g ω₀ := by
    intro x
    obtain ⟨p⟩ := hconn.preconnected ω₀ x
    suffices ∀ y (q : (colourGraph r).Walk y x), (∃ g, act r g ω₀ = y) → ∃ g, act r g ω₀ = x
      from this ω₀ p ⟨1, act_one r ω₀⟩
    intro y q
    clear p
    induction q with
    | nil => exact id
    | cons h q ih =>
      rintro ⟨g, hg⟩
      obtain ⟨-, i, hi⟩ := (colourGraph_adj hinv).mp h
      exact ih ⟨g * s i, by rw [act_mul_s hinv hrel, hg, hi]⟩
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, ⟨act_one r ω₀, fun g i => act_mul_s hinv hrel g i ω₀⟩,
    ?_⟩
  rintro ψ ⟨hψo, hψ⟩
  ext g
  exact eq_act hψo hψ g

theorem adj_iff_of_colour {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
    (hfix : ∀ i x, r i x ≠ x) (φ : K ≃ Ω) (hφ : ∀ g i, φ (g * s i) = r i (φ g)) (g h : K) :
    T.Adj g h ↔ (colourGraph r).Adj (φ g) (φ h) := by
  rw [colourGraph_adj hinv, adj_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨fun e => hfix i (φ g) ((hφ g i).symm.trans e.symm), i, hφ g i⟩
  · rintro ⟨-, i, hi⟩
    exact ⟨i, φ.injective (hi.trans (hφ g i).symm)⟩

end CFSG.Combinatorics.AperiodicSixteenGraph
