module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Aff
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfClosure

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def eqP (x y : Wr 8) : Prop := x = y ∨ x = y * allOnes 8

instance (x y : Wr 8) : Decidable (eqP x y) := by unfold eqP; infer_instance

@[expose] def supp8 (v : Fin 8 → ZMod 2) : List (Fin 8) := (List.finRange 8).filter fun i => v i = 1

@[expose] def pairUp8 : List (Fin 8) → List (Fin 8 × Fin 8)
  | x :: y :: t => (x, y) :: pairUp8 t
  | _ => []

theorem decomp8_ok : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 →
    ((pairUp8 (supp8 v)).map fun q => ofVec (vecOf [q.1, q.2])).prod = ofVec v := by
  decide +kernel

theorem mem_aeSubOver_of (w : Wr 8) (h : wsum w = 0 ∧ Equiv.Perm.sign w.perm = 1 ∧
    ∀ s ∈ affinePlanes, s.map w.perm.toEmbedding ∈ affinePlanes ∧
      s.map w.perm⁻¹.toEmbedding ∈ affinePlanes) : w ∈ aeSubOver agl32 :=
  ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[expose] def tp (t u : List (Fin 8))
    (h : ∀ i : Fin 8, u.getD (t.getD i.1 0).1 0 = i ∧ t.getD (u.getD i.1 0).1 0 = i) :
    Equiv.Perm (Fin 8) :=
  ⟨fun i => t.getD i.1 0, fun i => u.getD i.1 0, fun i => (h i).1, fun i => (h i).2⟩

@[expose] def gp (tu : List (Fin 8) × List (Fin 8)) : Equiv.Perm (Fin 8) :=
  if h : ∀ i : Fin 8, tu.2.getD (tu.1.getD i.1 0).1 0 = i ∧ tu.1.getD (tu.2.getD i.1 0).1 0 = i then
    tp tu.1 tu.2 h else 1

@[expose] def masksN : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 1, 0],
  [0, 0, 0, 0, 1, 0, 1, 0],
  [0, 0, 0, 0, 1, 1, 0, 0],
  [0, 0, 0, 1, 0, 0, 1, 0],
  [0, 0, 0, 1, 0, 1, 0, 0],
  [0, 0, 0, 1, 1, 0, 0, 0],
  [0, 0, 0, 1, 1, 1, 1, 0],
  [0, 0, 1, 0, 0, 0, 1, 0],
  [0, 0, 1, 0, 0, 1, 0, 0],
  [0, 0, 1, 0, 1, 0, 0, 0],
  [0, 0, 1, 0, 1, 1, 1, 0],
  [0, 0, 1, 1, 0, 0, 0, 0],
  [0, 0, 1, 1, 0, 1, 1, 0],
  [0, 0, 1, 1, 1, 0, 1, 0],
  [0, 0, 1, 1, 1, 1, 0, 0],
  [0, 1, 0, 0, 0, 0, 1, 0],
  [0, 1, 0, 0, 0, 1, 0, 0],
  [0, 1, 0, 0, 1, 0, 0, 0],
  [0, 1, 0, 0, 1, 1, 1, 0],
  [0, 1, 0, 1, 0, 0, 0, 0],
  [0, 1, 0, 1, 0, 1, 1, 0],
  [0, 1, 0, 1, 1, 0, 1, 0],
  [0, 1, 0, 1, 1, 1, 0, 0],
  [0, 1, 1, 0, 0, 0, 0, 0],
  [0, 1, 1, 0, 0, 1, 1, 0],
  [0, 1, 1, 0, 1, 0, 1, 0],
  [0, 1, 1, 0, 1, 1, 0, 0],
  [0, 1, 1, 1, 0, 0, 1, 0],
  [0, 1, 1, 1, 0, 1, 0, 0],
  [0, 1, 1, 1, 1, 0, 0, 0],
  [0, 1, 1, 1, 1, 1, 1, 0],
  [1, 0, 0, 0, 0, 0, 1, 0],
  [1, 0, 0, 0, 0, 1, 0, 0],
  [1, 0, 0, 0, 1, 0, 0, 0],
  [1, 0, 0, 0, 1, 1, 1, 0],
  [1, 0, 0, 1, 0, 0, 0, 0],
  [1, 0, 0, 1, 0, 1, 1, 0],
  [1, 0, 0, 1, 1, 0, 1, 0],
  [1, 0, 0, 1, 1, 1, 0, 0],
  [1, 0, 1, 0, 0, 0, 0, 0],
  [1, 0, 1, 0, 0, 1, 1, 0],
  [1, 0, 1, 0, 1, 0, 1, 0],
  [1, 0, 1, 0, 1, 1, 0, 0],
  [1, 0, 1, 1, 0, 0, 1, 0],
  [1, 0, 1, 1, 0, 1, 0, 0],
  [1, 0, 1, 1, 1, 0, 0, 0],
  [1, 0, 1, 1, 1, 1, 1, 0],
  [1, 1, 0, 0, 0, 0, 0, 0],
  [1, 1, 0, 0, 0, 1, 1, 0],
  [1, 1, 0, 0, 1, 0, 1, 0],
  [1, 1, 0, 0, 1, 1, 0, 0],
  [1, 1, 0, 1, 0, 0, 1, 0],
  [1, 1, 0, 1, 0, 1, 0, 0],
  [1, 1, 0, 1, 1, 0, 0, 0],
  [1, 1, 0, 1, 1, 1, 1, 0],
  [1, 1, 1, 0, 0, 0, 1, 0],
  [1, 1, 1, 0, 0, 1, 0, 0],
  [1, 1, 1, 0, 1, 0, 0, 0],
  [1, 1, 1, 0, 1, 1, 1, 0],
  [1, 1, 1, 1, 0, 0, 0, 0],
  [1, 1, 1, 1, 0, 1, 1, 0],
  [1, 1, 1, 1, 1, 0, 1, 0],
  [1, 1, 1, 1, 1, 1, 0, 0]]

@[expose] def vecOfN (l : List ℕ) : Fin 8 → ZMod 2 := fun i => (l.getD i.1 0 : ℕ)

theorem masks_cover : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → v 7 = 0 →
    ∃ l ∈ masksN, vecOfN l = v := by decide +kernel

structure PairData where
  a : Wr 8
  b : Wr 8
  c : Wr 8
  d : Wr 8
  h : Wr 8
  rels : List (List ℕ)
  cands : List (Wr 8 × List ℕ)
  pairWords : List (Fin 8 × Fin 8 × List ℕ)
  permWords : List (List (List (Fin 8)) × List ℕ)
  goodPerms : List (List (Fin 8) × List (Fin 8))

namespace PairData

variable (D : PairData)

@[expose] def gens (x : Wr 8) : List (Wr 8) := [D.a, D.b, D.c, D.d, x]

@[expose] def pgens (q : Equiv.Perm (Fin 8)) : List (Equiv.Perm (Fin 8)) :=
  [D.a.perm, D.b.perm, D.c.perm, D.d.perm, q]

@[expose] def look (t : Wr 8) : List ℕ :=
  match D.cands.find? (fun e => decide (eqP e.1 t)) with
  | some e => e.2
  | none => []

@[expose] def step (c1 t : Wr 8) : Wr 8 := evalW (D.gens c1) (D.look t)

@[expose] def inS (t : Wr 8) : Prop := ∃ e ∈ D.cands, eqP e.1 t

instance (t : Wr 8) : Decidable (D.inS t) := by unfold PairData.inS; infer_instance

end PairData

structure PairData.Ok (D : PairData) : Prop where
  ha : D.a ∈ aeSubOver agl32
  hb : D.b ∈ aeSubOver agl32
  hc : D.c ∈ aeSubOver agl32
  hd : D.d ∈ aeSubOver agl32
  hh : D.h ∈ aeSubOver agl32
  rels_h : ∀ r ∈ D.rels, eqP (evalW (D.gens D.h) r) 1
  rels_cands : ∀ e ∈ D.cands, ∀ r ∈ D.rels, eqP (evalW (D.gens e.1) r) 1
  cand_words : ∀ e ∈ D.cands, eqP (evalW (D.gens D.h) e.2) e.1
  dyn : ∀ e ∈ D.cands, D.inS e.1 ∧ D.inS (D.step e.1 e.1) ∧ D.inS (D.step e.1 (D.step e.1 e.1)) ∧
    eqP (D.step e.1 (D.step e.1 (D.step e.1 e.1))) D.h
  perm_filter : ∀ t ∈ D.permWords, (∀ r ∈ D.rels, evalW (D.pgens (pc t.1)) r = 1) →
    ∃ g ∈ D.goodPerms, gp g = pc t.1
  filter_ok : ∀ g ∈ D.goodPerms, ∀ l ∈ masksN,
    (∀ r ∈ D.rels, eqP (evalW (D.gens (⟨vecOfN l, gp g⟩ : Wr 8)) r) 1) →
      ∃ e ∈ D.cands, eqP e.1 (⟨vecOfN l, gp g⟩ : Wr 8)
  perm_chk : chk (fun q t => decide (∀ x, pc t.1 x = qf q x)) quadsList D.permWords = true
  permWords_ok : ∀ t ∈ D.permWords, eqP (evalW (D.gens D.h) t.2) ⟨0, pc t.1⟩
  pairWords_ok : ∀ t ∈ D.pairWords, eqP (evalW (D.gens D.h) t.2.2) (ofVec (vecOf [t.1, t.2.1]))
  pairs_cov : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ∀ q ∈ pairUp8 (supp8 v),
    ∃ t ∈ D.pairWords, t.1 = q.1 ∧ t.2.1 = q.2

@[expose] def eH (w : Wr 8) (hw : w ∈ aeSubOver agl32) : ↥e29Sub := ⟨mkQ 8 w, ⟨w, hw, rfl⟩⟩

@[expose] def Rep (x : ↥e29Sub) (t : Wr 8) : Prop := (x : AEQ 8) = mkQ 8 t

theorem rep_eq {x y : ↥e29Sub} {t : Wr 8} (hx : Rep x t) (hy : Rep y t) : x = y :=
  Subtype.ext (hx.trans hy.symm)

theorem rep_of_eqP {x : ↥e29Sub} {t t' : Wr 8} (hx : Rep x t) (h : eqP t t') : Rep x t' := by
  unfold Rep at *
  rw [hx]
  rcases h with h | h
  · rw [h]
  · rw [h]
    have : mkQ 8 (allOnes 8) = 1 := (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)
    rw [map_mul, this, mul_one]

theorem rep_mul {x y : ↥e29Sub} {s t : Wr 8} (hx : Rep x s) (hy : Rep y t) :
    Rep (x * y) (s * t) := by
  unfold Rep at *
  show (x : AEQ 8) * (y : AEQ 8) = mkQ 8 (s * t)
  rw [hx, hy, map_mul]

theorem rep_one : Rep (1 : ↥e29Sub) 1 := by
  unfold Rep
  show (1 : AEQ 8) = mkQ 8 1
  rw [map_one]

theorem eqP_of_mkQ_eq {a b : Wr 8} (h : mkQ 8 a = mkQ 8 b) : eqP a b := by
  rcases mkQ_eq_iff.mp h with h | h
  · left; exact (inv_mul_eq_one.mp h)
  · right
    have h1 : b = a * allOnes 8 := by
      calc b = a * (a⁻¹ * b) := by group
        _ = a * allOnes 8 := by rw [h]
    have h2 : a = b * allOnes 8 := by
      rw [h1, mul_assoc, allOnes_mul_self, mul_one]
    exact h2

theorem eqP_symm {x y : Wr 8} (h : eqP x y) : eqP y x := by
  rcases h with h | h
  · left; exact h.symm
  · right; rw [h, mul_assoc, allOnes_mul_self, mul_one]

theorem eqP_trans {x y z : Wr 8} (h1 : eqP x y) (h2 : eqP y z) : eqP x z := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; rw [h1, h2]
  · right; rw [h1, h2]
  · right; rw [h1, h2]
  · left; rw [h1, h2, mul_assoc, allOnes_mul_self, mul_one]

section Core

variable {D : PairData} (hD : D.Ok)
include hD

theorem val_evalW (x : ↥e29Sub) (xw : Wr 8) (hx : Rep x xw) (w : List ℕ) :
    ((evalW [eH D.a hD.ha, eH D.b hD.hb, eH D.c hD.hc, eH D.d hD.hd, x] w : ↥e29Sub) : AEQ 8) =
      mkQ 8 (evalW (D.gens xw) w) := by
  have h1 : ((evalW [eH D.a hD.ha, eH D.b hD.hb, eH D.c hD.hc, eH D.d hD.hd, x] w : ↥e29Sub) :
      AEQ 8) = evalW [mkQ 8 D.a, mkQ 8 D.b, mkQ 8 D.c, mkQ 8 D.d, (x : AEQ 8)] w := by
    have := map_evalW e29Sub.subtype
      [eH D.a hD.ha, eH D.b hD.hb, eH D.c hD.hc, eH D.d hD.hd, x] w
    simpa [eH] using this
  have h2 : mkQ 8 (evalW (D.gens xw) w) =
      evalW [mkQ 8 D.a, mkQ 8 D.b, mkQ 8 D.c, mkQ 8 D.d, mkQ 8 xw] w := by
    have := map_evalW (mkQ 8) (D.gens xw) w
    simpa [PairData.gens] using this
  rw [h1, h2, hx]



omit hD in
theorem exists_rep (x : ↥e29Sub) : ∃ (v : Fin 8 → ZMod 2) (p : Equiv.Perm (Fin 8)), ∑ i, v i = 0 ∧
    v 7 = 0 ∧ p ∈ agl32 ∧ Rep x ⟨v, p⟩ := by
  obtain ⟨w, hw, hwx⟩ := x.2
  have hrep : Rep x w := by unfold Rep; rw [← hwx]
  have hs : ∑ i, w.vec i = 0 := hw.1.1
  by_cases h7 : w.vec 7 = 0
  · exact ⟨w.vec, w.perm, hs, h7, hw.2, hrep⟩
  · have h1 : w.vec 7 = 1 := by
      have := zmod_two_cases (w.vec 7)
      tauto
    refine ⟨fun i => w.vec i + 1, w.perm, ?_, ?_, hw.2, ?_⟩
    · rw [Finset.sum_add_distrib, hs]; simp
      decide
    · show w.vec 7 + 1 = 0
      rw [h1]; decide
    · have : (⟨fun i => w.vec i + 1, w.perm⟩ : Wr 8) = w * allOnes 8 := by
        refine Wr.ext (funext fun i => ?_) (by simp [mul_perm, allOnes])
        rfl
      rw [this]
      exact rep_of_eqP hrep (Or.inr (by rw [mul_assoc, allOnes_mul_self, mul_one]))

theorem relOK_h : ∀ r ∈ D.rels, evalW [eH D.a hD.ha, eH D.b hD.hb, eH D.c hD.hc, eH D.d hD.hd,
    eH D.h hD.hh] r = 1 := by
  intro r hr
  have h1 := val_evalW hD (eH D.h hD.hh) D.h rfl r
  apply Subtype.ext
  rw [h1]
  rcases hD.rels_h r hr with h | h
  · rw [h]; rfl
  · rw [h, map_mul]
    have : mkQ 8 (allOnes 8) = 1 := (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)
    rw [this, mul_one]; rfl

@[expose] def gH (x : ↥e29Sub) : List ↥e29Sub :=
  [eH D.a hD.ha, eH D.b hD.hb, eH D.c hD.hc, eH D.d hD.hd, x]

theorem look_spec {t : Wr 8} (ht : D.inS t) : eqP (evalW (D.gens D.h) (D.look t)) t := by
  unfold PairData.look
  obtain ⟨c, hc, hct⟩ := ht
  have hsome : (D.cands.find? (fun c => decide (eqP c.1 t))).isSome :=
    List.find?_isSome.mpr ⟨c, hc, by simpa using hct⟩
  cases hf : D.cands.find? (fun c => decide (eqP c.1 t)) with
  | none => rw [hf] at hsome; simp at hsome
  | some c' =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only
    exact eqP_trans (hD.cand_words c' h2) (of_decide_eq_true h1)

theorem step_rep (σ : ↥e29Sub →* ↥e29Sub) (ha : σ (eH D.a hD.ha) = eH D.a hD.ha)
    (hb : σ (eH D.b hD.hb) = eH D.b hD.hb) (hc : σ (eH D.c hD.hc) = eH D.c hD.hc)
    (hd : σ (eH D.d hD.hd) = eH D.d hD.hd) {x : ↥e29Sub} {t c1w : Wr 8} (hx : Rep x t)
    (ht : D.inS t) (hc1 : Rep (σ (eH D.h hD.hh)) c1w) : Rep (σ x) (D.step c1w t) := by
  have hw := look_spec hD ht
  have hxe : x = evalW (gH hD (eH D.h hD.hh)) (D.look t) :=
    rep_eq hx (rep_of_eqP (val_evalW hD (eH D.h hD.hh) D.h rfl (D.look t)) hw)
  have h1 : σ x = evalW (gH hD (σ (eH D.h hD.hh))) (D.look t) := by
    rw [hxe]
    have := map_evalW σ (gH hD (eH D.h hD.hh)) (D.look t)
    simpa [gH, ha, hb, hc, hd] using this
  rw [h1]
  exact val_evalW hD (σ (eH D.h hD.hh)) c1w hc1 (D.look t)

theorem relOK_map (σ : ↥e29Sub →* ↥e29Sub) (ha : σ (eH D.a hD.ha) = eH D.a hD.ha)
    (hb : σ (eH D.b hD.hb) = eH D.b hD.hb) (hc : σ (eH D.c hD.hc) = eH D.c hD.hc)
    (hd : σ (eH D.d hD.hd) = eH D.d hD.hd) {x : ↥e29Sub}
    (hx : ∀ r ∈ D.rels, evalW (gH hD x) r = 1) : ∀ r ∈ D.rels, evalW (gH hD (σ x)) r = 1 := by
  intro r hr
  have := map_evalW σ (gH hD x) r
  simp only [gH, List.map_cons, List.map_nil, ha, hb, hc, hd] at this
  have h2 : evalW (gH hD (σ x)) r = σ (evalW (gH hD x) r) := this.symm
  rw [h2, hx r hr, map_one]

omit hD in
theorem eqP_perm {x : Wr 8} (h : eqP x 1) : x.perm = 1 := by
  rcases h with h | h
  · rw [h]; rfl
  · rw [h]; rfl

theorem lemmaS (x : ↥e29Sub) (hx : ∀ r ∈ D.rels, evalW (gH hD x) r = 1) :
    ∃ e ∈ D.cands, Rep x e.1 := by
  obtain ⟨v, p, hv, hv7, hp, hrep⟩ := exists_rep x
  obtain ⟨t, ht, htp⟩ := perm_cover_of_chk hD.perm_chk p hp
  have hrels : ∀ r ∈ D.rels, eqP (evalW (D.gens (⟨v, pc t.1⟩ : Wr 8)) r) 1 := by
    intro r hr
    have h1 := val_evalW hD x ⟨v, p⟩ hrep r
    have h2 : evalW (gH hD x) r = 1 := hx r hr
    rw [show evalW [eH D.a hD.ha, eH D.b hD.hb, eH D.c hD.hc, eH D.d hD.hd, x] r = 1 from h2] at h1
    rw [htp]
    apply eqP_of_mkQ_eq
    rw [map_one, ← h1]
    rfl
  have hperm : ∀ r ∈ D.rels, evalW (D.pgens (pc t.1)) r = 1 := by
    intro r hr
    have hmap := map_evalW (permHom 8) (D.gens (⟨v, pc t.1⟩ : Wr 8)) r
    have h1 := eqP_perm (hrels r hr)
    exact (by simpa [PairData.gens, PairData.pgens, permHom] using hmap.symm.trans h1)
  obtain ⟨g, hg, hgt⟩ := hD.perm_filter t ht hperm
  obtain ⟨l, hl, hlv⟩ := masks_cover v hv hv7
  subst hlv
  rw [← hgt] at hrels
  obtain ⟨e, he, hee⟩ := hD.filter_ok g hg l hl hrels
  rw [hgt] at hee
  refine ⟨e, he, ?_⟩
  rw [htp] at hee
  exact rep_of_eqP hrep (eqP_symm hee)

theorem gen_e29 (x : ↥e29Sub) :
    x ∈ Subgroup.closure {y | y ∈ gH hD (eH D.h hD.hh)} := by
  obtain ⟨v, p, hv, hv7, hp, hrep⟩ := exists_rep x
  obtain ⟨t, ht, htp⟩ := perm_cover_of_chk hD.perm_chk p hp
  have hperm : ∃ y ∈ Subgroup.closure {y | y ∈ gH hD (eH D.h hD.hh)}, Rep y ⟨0, p⟩ := by
    refine ⟨evalW (gH hD (eH D.h hD.hh)) t.2, evalW_mem_closure _ _, ?_⟩
    have := val_evalW hD (eH D.h hD.hh) D.h rfl t.2
    refine rep_of_eqP this ?_
    rw [← htp]
    exact hD.permWords_ok t ht
  have hvec : ∀ l : List (Fin 8 × Fin 8), (∀ q ∈ l, ∃ t ∈ D.pairWords, t.1 = q.1 ∧ t.2.1 = q.2) →
      ∃ y ∈ Subgroup.closure {y | y ∈ gH hD (eH D.h hD.hh)},
        Rep y ((l.map fun q => ofVec (vecOf [q.1, q.2])).prod) := by
    intro l
    induction l with
    | nil => intro _; exact ⟨1, Subgroup.one_mem _, rep_one⟩
    | cons q l ih =>
      intro hl
      obtain ⟨y, hy, hyr⟩ := ih fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')
      obtain ⟨t, ht, h1, h2⟩ := hl q List.mem_cons_self
      have hq : Rep (evalW (gH hD (eH D.h hD.hh)) t.2.2) (ofVec (vecOf [q.1, q.2])) := by
        have := val_evalW hD (eH D.h hD.hh) D.h rfl t.2.2
        refine rep_of_eqP this ?_
        have := hD.pairWords_ok t ht
        rw [h1, h2] at this
        exact this
      refine ⟨evalW (gH hD (eH D.h hD.hh)) t.2.2 * y,
        (Subgroup.closure _).mul_mem (evalW_mem_closure _ _) hy, ?_⟩
      simpa using rep_mul hq hyr
  obtain ⟨y1, hy1, hr1⟩ := hvec _ (hD.pairs_cov v hv)
  rw [decomp8_ok v hv] at hr1
  obtain ⟨y2, hy2, hr2⟩ := hperm
  have hxy : x = y1 * y2 := by
    refine rep_eq hrep ?_
    have := rep_mul hr1 hr2
    have e : (ofVec v * (⟨0, p⟩ : Wr 8)) = ⟨v, p⟩ := by
      refine Wr.ext (funext fun i => ?_) (by simp [mul_perm, ofVec])
      show v i + 0 = v i
      simp
    rw [e] at this
    exact this
  rw [hxy]
  exact (Subgroup.closure _).mul_mem hy1 hy2

theorem fix_core (σ : ↥e29Sub →* ↥e29Sub) (hσ : ∃ a : ℕ, ∀ r, σ^[3 ^ a] r = r)
    (ha : σ (eH D.a hD.ha) = eH D.a hD.ha) (hb : σ (eH D.b hD.hb) = eH D.b hD.hb)
    (hc : σ (eH D.c hD.hc) = eH D.c hD.hc) (hd : σ (eH D.d hD.hd) = eH D.d hD.hd) :
    ∀ r, σ r = r := by
  obtain ⟨N0, hN⟩ := hσ
  obtain ⟨e, he, hc1⟩ := lemmaS hD (σ (eH D.h hD.hh)) (relOK_map hD σ ha hb hc hd (relOK_h hD))
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hD.dyn e he
  have rep_h : Rep (eH D.h hD.hh) D.h := rfl
  have x2 := step_rep hD σ ha hb hc hd hc1 hs1 hc1
  have x3 := step_rep hD σ ha hb hc hd x2 hs2 hc1
  have x4 := step_rep hD σ ha hb hc hd x3 hs3 hc1
  have h4 : σ (σ (σ (σ (eH D.h hD.hh)))) = eH D.h hD.hh := rep_eq (rep_of_eqP x4 hs4) rep_h
  have h4' : (⇑σ)^[4] (eH D.h hD.hh) = eH D.h hD.hh := by simpa using h4
  have hσh : σ (eH D.h hD.hh) = eH D.h hD.hh := by
    have hmod : 3 ^ N0 % 4 = 1 ∨ 3 ^ N0 % 4 = 3 := by
      clear hN
      induction N0 with
      | zero => left; rfl
      | succ k ih => rw [pow_succ]; omega
    have hN' : (⇑σ)^[3 ^ N0] (eH D.h hD.hh) = eH D.h hD.hh := hN _
    have hfix : ∀ m : ℕ, (⇑σ)^[4 * m] (eH D.h hD.hh) = eH D.h hD.hh := fun m => by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed h4' m
    have hdecomp : 3 ^ N0 = (3 ^ N0 % 4) + 4 * (3 ^ N0 / 4) := (Nat.mod_add_div _ _).symm
    rw [hdecomp, Function.iterate_add_apply, hfix] at hN'
    rcases hmod with h1 | h3
    · rw [h1] at hN'; simpa using hN'
    · rw [h3] at hN'
      have : (⇑σ)^[4] (eH D.h hD.hh) = σ (eH D.h hD.hh) := by
        have e : (⇑σ)^[4] (eH D.h hD.hh) = σ ((⇑σ)^[3] (eH D.h hD.hh)) :=
          Function.iterate_succ_apply' σ 3 _
        rw [e, hN']
      rw [← this]; exact h4'
  intro r
  have hgen := gen_e29 hD r
  have hle : Subgroup.closure {y | y ∈ gH hD (eH D.h hD.hh)} ≤
      MonoidHom.eqLocus σ (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [gH, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact hσh
  exact hle hgen

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
