module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

structure FW where
  v : List ℕ
  p : List ℕ
  q : List ℕ

@[expose] instance : DecidableEq FW := fun a b =>
  decidable_of_iff (a.v = b.v ∧ a.p = b.p ∧ a.q = b.q) (by
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    simp)

@[expose] def tab (f : Fin 8 → ℕ) : List ℕ := (List.range 8).map fun k => f (Fin.ofNat 8 k)

theorem ofNat_val (k : Fin 8) : Fin.ofNat 8 k.1 = k := by
  apply Fin.ext
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt k.2]

theorem tab_getD (f : Fin 8 → ℕ) (k : Fin 8) : (tab f).getD k.1 0 = f k := by
  unfold tab
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range k.2]
  simp [ofNat_val]

theorem tab_inj {f g : Fin 8 → ℕ} (h : tab f = tab g) : f = g := by
  funext k
  have := congrArg (fun l => l.getD k.1 0) h
  simp only [tab_getD] at this
  exact this

@[expose] def ofWr (x : Wr 8) : FW :=
  ⟨tab fun i => (x.vec i).val, tab fun i => (x.perm i).val, tab fun i => (x.perm.symm i).val⟩

@[expose] def mulF (x y : FW) : FW :=
  ⟨(List.range 8).map fun i => (x.v.getD i 0 + y.v.getD (x.q.getD i 0) 0) % 2,
    (List.range 8).map fun i => x.p.getD (y.p.getD i 0) 0,
    (List.range 8).map fun i => y.q.getD (x.q.getD i 0) 0⟩

@[expose] def invF (x : FW) : FW :=
  ⟨(List.range 8).map fun i => x.v.getD (x.p.getD i 0) 0, x.q, x.p⟩

@[expose] def oneF : FW := ⟨(List.range 8).map fun _ => 0, List.range 8, List.range 8⟩

@[expose] def piF : FW := ⟨(List.range 8).map fun _ => 1, List.range 8, List.range 8⟩

theorem ofWr_inj {x y : Wr 8} (h : ofWr x = ofWr y) : x = y := by
  have hv := tab_inj (FW.mk.inj h).1
  have hp := tab_inj (FW.mk.inj h).2.1
  refine Wr.ext (funext fun i => ?_) (Equiv.ext fun i => ?_)
  · exact ZMod.val_injective 2 (congrFun hv i)
  · exact Fin.ext (congrFun hp i)

theorem map_range_eq_tab (G : ℕ → ℕ) (f : Fin 8 → ℕ) (h : ∀ k : Fin 8, G k.1 = f k) :
    (List.range 8).map G = tab f := by
  unfold tab
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < 8 := List.mem_range.mp hk
  have := h ⟨k, hk'⟩
  simp only [] at this
  rw [this]
  exact congrArg f (Fin.ext (by simp [Fin.val_ofNat, Nat.mod_eq_of_lt hk']))

theorem ofWr_mul (x y : Wr 8) : ofWr (x * y) = mulF (ofWr x) (ofWr y) := by
  unfold ofWr mulF
  simp only []
  congr 1
  · symm
    refine map_range_eq_tab _ _ fun k => ?_
    simp only [tab_getD]
    rw [mul_vec, ZMod.val_add]
  · symm
    refine map_range_eq_tab _ _ fun k => ?_
    simp only [tab_getD]
    rfl
  · symm
    refine map_range_eq_tab _ _ fun k => ?_
    simp only [tab_getD]
    rfl

theorem ofWr_inv (x : Wr 8) : ofWr x⁻¹ = invF (ofWr x) := by
  unfold ofWr invF
  simp only []
  congr 1
  · symm
    refine map_range_eq_tab _ _ fun k => ?_
    simp only [tab_getD]
    rfl

theorem ofWr_one : ofWr (1 : Wr 8) = oneF := by decide +kernel

theorem ofWr_allOnes : ofWr (allOnes 8) = piF := by decide +kernel

@[expose] def letterF (gs : List FW) (l : ℕ) : FW :=
  if l < gs.length then gs.getD l oneF else invF (gs.getD (l - gs.length) oneF)

@[expose] def evalF (gs : List FW) (w : List ℕ) : FW := (w.map (letterF gs)).foldr mulF oneF

theorem ofWr_letter (gs : List (Wr 8)) (l : ℕ) :
    ofWr (letter gs l) = letterF (gs.map ofWr) l := by
  unfold letter letterF
  simp only [List.length_map]
  have h1 : ∀ m : ℕ, (gs.map ofWr).getD m oneF = ofWr (gs.getD m 1) := by
    intro m
    rw [← ofWr_one, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases gs[m]? <;> simp
  split_ifs
  · rw [h1]
  · rw [ofWr_inv, h1]

theorem ofWr_evalW (gs : List (Wr 8)) (w : List ℕ) :
    ofWr (evalW gs w) = evalF (gs.map ofWr) w := by
  induction w with
  | nil => simp only [evalW, List.map_nil, List.prod_nil, evalF, List.foldr_nil]; exact ofWr_one
  | cons l w ih =>
    have : evalW gs (l :: w) = letter gs l * evalW gs w := by
      simp [evalW, List.prod_cons]
    rw [this, ofWr_mul, ofWr_letter, ih]
    simp [evalF, List.foldr_cons]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
