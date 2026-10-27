module

public import Certificates.Data.Kernel.F4T7B
public import CFSG.Certificates.Kernel.F4M3BSound

public section

namespace CFSG.KC.F4T7B

open CFSG.KC.F4M3B

variable {α β : Type}

@[expose] def VT.map (f : α → β) (w : VT α) : VT β :=
  ⟨f w.l0, f w.h0, f w.l1, f w.h1, f w.l2, f w.h2⟩

section map

variable (o : Ops α) (o' : Ops β) (f : α → β) (ha : ∀ p q, f (o.a p q) = o'.a (f p) (f q))
  (hx : ∀ p q, f (o.x p q) = o'.x (f p) (f q)) (ht : f o.t = o'.t)

include hx ht in
theorem zr_map : f (zr o) = zr o' := by
  simp only [zr, hx, ht]

include hx ht in
theorem sel_map (b : Bool) (p : α) : f (sel o b p) = sel o' b (f p) := by
  cases b <;> simp only [sel, cond, zr_map o o' f hx ht]

include ha hx ht in
theorem lit_map (b : Bool) (p : α) : f (lit o b p) = lit o' b (f p) := by
  cases b <;> simp only [lit, cond, bnot_map o o' f ha hx ht]

include hx ht in
theorem kl_map (c : Nat) (l h : α) : f (kl o c l h) = kl o' c (f l) (f h) := by
  simp only [kl, hx, sel_map o o' f hx ht]

include hx ht in
theorem kh_map (c : Nat) (l h : α) : f (kh o c l h) = kh o' c (f l) (f h) := by
  simp only [kh, hx, sel_map o o' f hx ht]

include hx ht in
theorem img_map (A : MatT α) (u : Pt) : (img o A u).map f = img o' (A.map f) u := by
  simp only [img, VT.map, MatT.map, hx, kl_map o o' f hx ht, kh_map o o' f hx ht]

include ha hx ht in
theorem eqV_map (w : VT α) (e : Pt) : f (eqV o w e) = eqV o' (w.map f) e := by
  simp only [eqV, VT.map, ha, lit_map o o' f ha hx ht]

include ha hx ht in
theorem mulOf_map (w : VT α) (u : Pt) : f (mulOf o w u) = mulOf o' (w.map f) u := by
  simp only [mulOf, bor_map o o' f ha hx ht, eqV_map o o' f ha hx ht]

include ha hx ht in
theorem mtab_map (A : MatT α) (om : List Pt) :
    (mtab o A om).map (List.map f) = mtab o' (A.map f) om := by
  simp only [mtab, List.map_map]
  congr 1
  funext u
  simp only [Function.comp, List.map_map]
  congr 1
  funext v
  simp only [Function.comp, mulOf_map o o' f ha hx ht, img_map o o' f hx ht]

include ha hx ht in
theorem orL_map (l : List α) : f (orL o l) = orL o' (l.map f) := by
  induction l with
  | nil => exact zr_map o o' f hx ht
  | cons a l ih =>
    simp only [orL, List.foldr_cons, List.map_cons] at ih ⊢
    rw [bor_map o o' f ha hx ht, ih]

include ha ht in
theorem andL_map (l : List α) : f (andL o l) = andL o' (l.map f) := by
  induction l with
  | nil => exact ht
  | cons a l ih =>
    simp only [andL, List.foldr_cons, List.map_cons] at ih ⊢
    rw [ha, ih]

include ha hx ht in
theorem stabT_map (T : List (List α)) : f (stabT o T) = stabT o' (T.map (List.map f)) := by
  simp only [stabT, andL_map o o' f ha ht, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp, orL_map o o' f ha hx ht]

omit ha hx ht in
theorem getD_map' {γ δ : Type} (g : γ → δ) (l : List γ) (n : Nat) (d : γ) :
    (l.map g).getD n (g d) = g (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

omit ha hx ht in
theorem getD_nil_map (T : List (List α)) (k : Nat) :
    (T.map (List.map f)).getD k [] = (T.getD k []).map f :=
  getD_map' (List.map f) T k []

include hx ht in
theorem getD2_map (T : List (List α)) (k j : Nat) :
    f ((T.getD k []).getD j (zr o)) = ((T.map (List.map f)).getD k []).getD j (zr o') := by
  rw [← zr_map o o' f hx ht, getD_nil_map, getD_map']

include ha hx ht in
theorem kerT_map (T : List (List α)) : f (kerT o T) = kerT o' (T.map (List.map f)) := by
  simp only [kerT, andL_map o o' f ha ht, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp, getD2_map o o' f hx ht]

include ha hx ht in
theorem before_map (r : List α) (j : Nat) : f (before o r j) = before o' (r.map f) j := by
  simp only [before, orL_map o o' f ha hx ht, List.map_take]

include ha hx ht in
theorem invP_map (rk rl : List α) : f (invP o rk rl) = invP o' (rk.map f) (rl.map f) := by
  simp only [invP, orL_map o o' f ha hx ht, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  rw [Function.comp, ha, before_map o o' f ha hx ht, ← zr_map o o' f hx ht, getD_map']

include hx ht in
theorem xorL_map (l : List α) : f (l.foldr o.x (zr o)) = (l.map f).foldr o'.x (zr o') := by
  induction l with
  | nil => exact zr_map o o' f hx ht
  | cons a l ih => simp only [List.foldr_cons, List.map_cons, hx, ih]

include ha hx ht in
theorem parT_map (T : List (List α)) : f (parT o T) = parT o' (T.map (List.map f)) := by
  simp only [parT, xorL_map o o' f hx ht, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro k _
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro l _
  by_cases h : k < l
  · simp only [h, if_true, Option.map_some, invP_map o o' f ha hx ht]
    rw [getD_nil_map, getD_nil_map]
  · simp only [h, if_false, Option.map_none]

include ha hx ht in
theorem invT_map (T U : List (List α)) :
    f (invT o T U) = invT o' (T.map (List.map f)) (U.map (List.map f)) := by
  simp only [invT, andL_map o o' f ha ht, List.map_flatMap, List.map_map]
  congr 1
  apply List.flatMap_congr
  intro k _
  apply List.map_congr_left
  intro j _
  simp only [Function.comp, ha, bor_map o o' f ha hx ht, bnot_map o o' f ha hx ht,
    getD2_map o o' f hx ht]

include hx in
theorem ml_map (a0 a1 b0 b1 c0 c1 d0 d1 : α) (ha : ∀ p q, f (o.a p q) = o'.a (f p) (f q)) :
    f (ml o a0 a1 b0 b1 c0 c1 d0 d1) =
      ml o' (f a0) (f a1) (f b0) (f b1) (f c0) (f c1) (f d0) (f d1) := by
  simp only [ml, pl, hx, ha]

include hx in
theorem mh_map (a0 a1 b0 b1 c0 c1 d0 d1 : α) (ha : ∀ p q, f (o.a p q) = o'.a (f p) (f q)) :
    f (mh o a0 a1 b0 b1 c0 c1 d0 d1) =
      mh o' (f a0) (f a1) (f b0) (f b1) (f c0) (f c1) (f d0) (f d1) := by
  simp only [mh, ph, hx, ha]

include ha hx in
theorem adjT_map (A : MatT α) : (adjT o A).map f = adjT o' (A.map f) := by
  simp only [adjT, MatT.map, ml_map o o' f hx _ _ _ _ _ _ _ _ ha, mh_map o o' f hx _ _ _ _ _ _ _ _ ha]

include ha hx ht in
theorem stabX_map (A : MatT α) (om : List Pt) : f (stabX o A om) = stabX o' (A.map f) om := by
  simp only [stabX, ha, isOne_map o o' f ha hx ht, detL_map o o' f ha hx, detH_map o o' f ha hx,
    stabT_map o o' f ha hx ht, mtab_map o o' f ha hx ht]

include ha hx ht in
theorem badX_map (A : MatT α) (om : List Pt) : f (badX o A om) = badX o' (A.map f) om := by
  simp only [badX, bor_map o o' f ha hx ht, bnot_map o o' f ha hx ht, stabT_map o o' f ha hx ht,
    invT_map o o' f ha hx ht, parT_map o o' f ha hx ht, mtab_map o o' f ha hx ht,
    adjT_map o o' f ha hx]

end map

end CFSG.KC.F4T7B

end
