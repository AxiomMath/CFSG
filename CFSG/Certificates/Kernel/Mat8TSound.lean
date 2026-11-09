module

public import Certificates.Data.Kernel.Mat8T
public import CFSG.Certificates.Kernel.Mat8CSound

public section

namespace CFSG.KC.Mat8T

open CFSG.KC.Mat8P CFSG.KC.Mat8R CFSG.KC.Mat8S CFSG.KC.Mat8C

theorem elemN_eq (y : ℕ) (xs : List ℕ) : elemN y xs = xs.contains y := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (motive := fun _ => Bool) (elemN y xs) true (Nat.beq x y) = _
    rw [List.contains_cons, ih]
    by_cases e : x = y
    · subst e
      rw [Nat.beq_refl, beq_self_eq_true, Bool.true_or]
    · have h : Nat.beq x y = false := by
        cases h' : Nat.beq x y
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') e
      rw [h, beq_eq_false_iff_ne.mpr (Ne.symm e), Bool.false_or]

theorem memT_insT (x y : ℕ) : ∀ (t : NT ℕ) (kx ky : ℕ), (x = y → kx = ky) →
    memT y (insT x t kx) ky = (x == y || memT y t ky) := by
  intro t
  induction t with
  | tip xs =>
    intro kx ky _
    change elemN y (x :: xs) = (x == y || elemN y xs)
    rw [elemN_eq, elemN_eq, List.contains_cons, beq_symm]
  | node l r ihl ihr =>
    intro kx ky hk
    change memT y (Bool.rec (motive := fun _ => NT ℕ) (.node l (insT x r (Nat.shiftRight kx 1)))
        (.node (insT x l (Nat.shiftRight kx 1)) r) (Nat.beq (Nat.land kx 1) 0)) ky =
      (x == y || Bool.rec (motive := fun _ => Bool) (memT y r (Nat.shiftRight ky 1))
        (memT y l (Nat.shiftRight ky 1)) (Nat.beq (Nat.land ky 1) 0))
    have hk' : x = y → Nat.shiftRight kx 1 = Nat.shiftRight ky 1 := fun e => by rw [hk e]
    cases bx : Nat.beq (Nat.land kx 1) 0 <;> cases bY : Nat.beq (Nat.land ky 1) 0
    · change Bool.rec (motive := fun _ => Bool) (memT y (insT x r (Nat.shiftRight kx 1)) _)
        (memT y l _) (Nat.beq (Nat.land ky 1) 0) = _
      rw [bY]
      exact ihr _ _ hk'
    · have hxy : (x == y) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        rw [hk e, bY] at bx
        exact Bool.false_ne_true bx.symm
      change Bool.rec (motive := fun _ => Bool) (memT y (insT x r (Nat.shiftRight kx 1)) _)
        (memT y l _) (Nat.beq (Nat.land ky 1) 0) = _
      rw [bY, hxy, Bool.false_or]
    · have hxy : (x == y) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        rw [hk e, bY] at bx
        exact Bool.false_ne_true bx
      change Bool.rec (motive := fun _ => Bool) (memT y r _)
        (memT y (insT x l (Nat.shiftRight kx 1)) _) (Nat.beq (Nat.land ky 1) 0) = _
      rw [bY, hxy, Bool.false_or]
    · change Bool.rec (motive := fun _ => Bool) (memT y r _)
        (memT y (insT x l (Nat.shiftRight kx 1)) _) (Nat.beq (Nat.land ky 1) 0) = _
      rw [bY]
      exact ihl _ _ hk'

theorem memK_insK (k : ℕ) (t : NT ℕ) (x y : ℕ) : memK k (insK k t x) y = (x == y || memK k t y) :=
  memT_insT x y t _ _ (fun e => by rw [e])

theorem memT_fullT (y : ℕ) : ∀ (d k : ℕ), memT y (fullT d) k = false := by
  intro d
  induction d with
  | zero => intro k; rfl
  | succ d ih =>
    intro k
    change Bool.rec (motive := fun _ => Bool) (memT y (fullT d) _) (memT y (fullT d) _)
      (Nat.beq (Nat.land k 1) 0) = false
    rw [ih]
    cases Nat.beq (Nat.land k 1) 0 <;> rfl

theorem memK_fullT (d k y : ℕ) : memK k (fullT d) y = false := memT_fullT y d _

theorem memK_foldR (k : ℕ) (L : List ℕ) :
    ∀ (t : NT ℕ) (y : ℕ), memK k (foldR (insK k) t L) y = (L.contains y || memK k t y) := by
  induction L with
  | nil => intro t y; rfl
  | cons x L ih =>
    intro t y
    change memK k (foldR (insK k) (insK k t x) L) y = _
    rw [ih, memK_insK, List.contains_cons, beq_symm x y]
    cases L.contains y <;> cases (y == x) <;> rfl

theorem memK_ofListT (d k : ℕ) (L : List ℕ) (y : ℕ) : memK k (ofListT d k L) y = L.contains y := by
  rw [ofListT, memK_foldR, memK_fullT, Bool.or_false]

theorem memP_ofListP_T (d k : ℕ) (L : List ℕ) : memP (ofListP L) = memK k (ofListT d k L) := by
  funext y
  rw [memP_ofListP, memK_ofListT]

theorem allR_eq {α : Type} (p : α → Bool) (l : List α) : allR p l = l.all p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) false (allR p l) (p x) = _
    rw [List.all_cons, ih]
    cases p x <;> rfl

theorem closedP_T (d k : ℕ) (gp L : List ℕ) : closedP gp L = closedPT d k gp L := by
  rw [closedP, closedPT, allR_eq]
  congr 1
  funext x
  rw [allR_eq, memP_ofListP_T d k]

theorem nodupTA_eq (k : ℕ) : ∀ (L : List ℕ) (t : NT ℕ) (s : NT ℕ),
    (∀ z, memP s z = memK k t z) → nodupTA k L t = nodupPAux s L := by
  intro L
  induction L with
  | nil => intro t s _; rfl
  | cons x L ih =>
    intro t s h
    change Bool.rec (motive := fun _ => Bool) (nodupTA k L (insK k t x)) false (memK k t x) =
      (!(memP s x) && nodupPAux (insP s x) L)
    rw [← h x]
    cases memP s x
    · rw [ih (insK k t x) (insP s x) (fun z => by rw [memP_insP, memK_insK, h])]
      rfl
    · rfl

theorem nodupP_T (d k : ℕ) (L : List ℕ) : nodupP L = nodupT d k L := by
  rw [nodupP, nodupT, nodupTA_eq k L (fullT d) (.tip []) (fun z => by rw [memP_empty, memK_fullT])]

def TR (d m k : ℕ) (p q : NT ℕ × List ℕ × List ℕ) : Prop :=
  (∀ z, memS d m p.1 z = memK k q.1 z) ∧ p.2 = q.2

theorem stepT_rel (d m k : ℕ) (p q : NT ℕ × List ℕ × List ℕ) (y : ℕ) (h : TR d m k p q) :
    TR d m k (stepS d m p y) (stepT k q y) := by
  rcases p with ⟨s, a, f⟩
  rcases q with ⟨t, a', f'⟩
  obtain ⟨h1, h2⟩ := h
  have h1' : ∀ z, memS d m s z = memK k t z := h1
  have h2' : (a, f) = (a', f') := h2
  rw [Prod.mk.injEq] at h2'
  obtain ⟨rfl, rfl⟩ := h2'
  change TR d m k (Bool.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (insS d m s y, y :: a, y :: f) (s, a, f) (memS d m s y))
    (Bool.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (insK k t y, y :: a, y :: f) (t, a, f) (memK k t y))
  rw [h1' y]
  cases memK k t y
  · refine ⟨fun z => ?_, rfl⟩
    change memS d m (insS d m s y) z = memK k (insK k t y) z
    rw [memS_insS, memK_insK, h1' z]
  · exact ⟨h1', rfl⟩

theorem foldR_rel' {α β γ : Type} (F : β → α → β) (G : γ → α → γ) (R : β → γ → Prop)
    (h : ∀ p q x, R p q → R (F p x) (G q x)) :
    ∀ (l : List α) (p : β) (q : γ), R p q → R (foldR F p l) (foldR G q l) := by
  intro l
  induction l with
  | nil => intro p q hpq; exact hpq
  | cons x l ih => intro p q hpq; exact ih _ _ (h p q x hpq)

theorem layerT_rel (d m k : ℕ) (gens : List ℕ) (s t : NT ℕ) (acc fr : List ℕ)
    (h : ∀ z, memS d m s z = memK k t z) :
    TR d m k (layerS d m gens s acc fr) (layerT k gens t acc fr) :=
  foldR_rel' _ _ (TR d m k) (fun p q x hpq => foldR_rel' _ _ (TR d m k)
    (fun p q g hpq => stepT_rel d m k p q (mulP g x) hpq) gens p q hpq) fr _ _ ⟨h, rfl⟩

theorem prodRec3B (g : NT ℕ → List ℕ → List ℕ → List ℕ × Bool) (p : NT ℕ × List ℕ × List ℕ) :
    Prod.rec (motive := fun _ => List ℕ × Bool)
      (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool) (fun a f => g s a f) r) p =
      g p.1 p.2.1 p.2.2 := by
  rcases p with ⟨s, a, f⟩
  rfl

theorem bfsTC_eq (d m k : ℕ) (gens : List ℕ) (cap : ℕ) :
    ∀ fuel (s t : NT ℕ) acc fr, (∀ z, memS d m s z = memK k t z) →
      bfsTC k gens cap fuel t acc fr = bfsC d m gens cap fuel s acc fr := by
  intro fuel
  induction fuel with
  | zero => intro s t acc fr _; rfl
  | succ n ih =>
    intro s t acc fr h
    cases fr with
    | nil => rfl
    | cons x l =>
      change Bool.rec (motive := fun _ => List ℕ × Bool) (Prod.rec (motive := fun _ => List ℕ × Bool)
            (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool)
              (fun a f => bfsTC k gens cap n s a f) r)
            (layerT k gens t acc (x :: l)))
          (acc, false) (Nat.ble cap (lenR acc)) =
        Bool.rec (motive := fun _ => List ℕ × Bool) (Prod.rec (motive := fun _ => List ℕ × Bool)
            (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool)
              (fun a f => bfsC d m gens cap n s a f) r)
            (layerS d m gens s acc (x :: l)))
          (acc, false) (Nat.ble cap (lenR acc))
      rw [prodRec3B, prodRec3B]
      obtain ⟨h1, h2⟩ := layerT_rel d m k gens s t acc (x :: l) h
      rw [← h2, ih _ _ _ _ h1]

theorem elemsC_T (d m : ℕ) (D k : ℕ) (gens : List ℕ) (cap : ℕ) :
    elemsC d m gens cap = elemsTC D k gens cap := by
  rw [elemsC, elemsTC]
  refine (bfsTC_eq d m k gens cap 200 _ _ _ _ (fun z => ?_)).symm
  rw [memS_insS, memK_insK, memS_empty, memK_fullT]

theorem runT_append (k : ℕ) (gens : List ℕ) (st : NT ℕ × List ℕ × List ℕ) (C D : List ℕ) :
    runT k gens st (C ++ D) = runT k gens (runT k gens st C) D := by
  simp only [runT, foldR_eq, List.foldl_append]

theorem layerT_eq (k : ℕ) (gens : List ℕ) (t : NT ℕ) (acc fr : List ℕ) :
    layerT k gens t acc fr = runT k gens (t, acc, []) fr := rfl

def SameT (k : ℕ) (p q : NT ℕ × List ℕ × List ℕ) : Prop :=
  (∀ z, memK k p.1 z = memK k q.1 z) ∧ p.2 = q.2

theorem stepT_same (k : ℕ) (p q : NT ℕ × List ℕ × List ℕ) (y : ℕ) (h : SameT k p q) :
    SameT k (stepT k p y) (stepT k q y) := by
  rcases p with ⟨s, a, f⟩
  rcases q with ⟨t, a', f'⟩
  obtain ⟨h1, h2⟩ := h
  have h1' : ∀ z, memK k s z = memK k t z := h1
  have h2' : (a, f) = (a', f') := h2
  rw [Prod.mk.injEq] at h2'
  obtain ⟨rfl, rfl⟩ := h2'
  change SameT k (Bool.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (insK k s y, y :: a, y :: f) (s, a, f) (memK k s y))
    (Bool.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (insK k t y, y :: a, y :: f) (t, a, f) (memK k t y))
  rw [h1' y]
  cases memK k t y
  · refine ⟨fun z => ?_, rfl⟩
    change memK k (insK k s y) z = memK k (insK k t y) z
    rw [memK_insK, memK_insK, h1' z]
  · exact ⟨h1', rfl⟩

theorem runT_same (k : ℕ) (gens C : List ℕ) (p q : NT ℕ × List ℕ × List ℕ) (h : SameT k p q) :
    SameT k (runT k gens p C) (runT k gens q C) :=
  foldR_rel' _ _ (SameT k) (fun p q x hpq => foldR_rel' _ _ (SameT k)
    (fun p q g hpq => stepT_same k p q (mulP g x) hpq) gens p q hpq) C p q h

def InvT (k : ℕ) (p : NT ℕ × List ℕ × List ℕ) : Prop := ∀ z, memK k p.1 z = p.2.1.contains z

theorem stepT_inv (k : ℕ) (p : NT ℕ × List ℕ × List ℕ) (y : ℕ) (h : InvT k p) :
    InvT k (stepT k p y) := by
  rcases p with ⟨s, a, f⟩
  have h' : ∀ z, memK k s z = a.contains z := h
  change InvT k (Bool.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (insK k s y, y :: a, y :: f) (s, a, f) (memK k s y))
  cases memK k s y
  · intro z
    change memK k (insK k s y) z = (y :: a).contains z
    rw [memK_insK, h' z, List.contains_cons, beq_symm]
  · exact h'

theorem innerT_inv (k x : ℕ) : ∀ (gens : List ℕ) (p : NT ℕ × List ℕ × List ℕ), InvT k p →
    InvT k (foldR (fun st g => stepT k st (mulP g x)) p gens) := by
  intro gens
  induction gens with
  | nil => intro p h; exact h
  | cons g gens ih => intro p h; exact ih _ (stepT_inv k p (mulP g x) h)

theorem runT_inv (k : ℕ) (gens : List ℕ) : ∀ (C : List ℕ) (p : NT ℕ × List ℕ × List ℕ), InvT k p →
    InvT k (runT k gens p C) := by
  intro C
  induction C with
  | nil => intro p h; exact h
  | cons x C ih => intro p h; exact ih _ (innerT_inv k x gens p h)

theorem bfsTC_same (k : ℕ) (gens : List ℕ) (cap : ℕ) :
    ∀ fuel (s t : NT ℕ) acc fr, (∀ z, memK k s z = memK k t z) →
      bfsTC k gens cap fuel s acc fr = bfsTC k gens cap fuel t acc fr := by
  intro fuel
  induction fuel with
  | zero => intro s t acc fr _; rfl
  | succ n ih =>
    intro s t acc fr h
    cases fr with
    | nil => rfl
    | cons x l =>
      change Bool.rec (motive := fun _ => List ℕ × Bool) (Prod.rec (motive := fun _ => List ℕ × Bool)
            (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool)
              (fun a f => bfsTC k gens cap n s a f) r)
            (layerT k gens s acc (x :: l)))
          (acc, false) (Nat.ble cap (lenR acc)) =
        Bool.rec (motive := fun _ => List ℕ × Bool) (Prod.rec (motive := fun _ => List ℕ × Bool)
            (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool)
              (fun a f => bfsTC k gens cap n s a f) r)
            (layerT k gens t acc (x :: l)))
          (acc, false) (Nat.ble cap (lenR acc))
      rw [prodRec3B, prodRec3B]
      obtain ⟨h1, h2⟩ := runT_same k gens (x :: l) (s, acc, []) (t, acc, []) ⟨h, rfl⟩
      rw [layerT_eq, layerT_eq, ← h2, ih _ _ _ _ h1]

def Reach (k : ℕ) (gens : List ℕ) (cap n : ℕ) (A F : List ℕ) (R : List ℕ × Bool) : Prop :=
  ∀ t, (∀ z, memK k t z = A.contains z) → bfsTC k gens cap n t A F = R

def ReachMid (k : ℕ) (gens : List ℕ) (cap n : ℕ) (A F C : List ℕ) (R : List ℕ × Bool) : Prop :=
  ∀ t, (∀ z, memK k t z = A.contains z) →
    bfsTC k gens cap n (runT k gens (t, A, F) C).1 (runT k gens (t, A, F) C).2.1
      (runT k gens (t, A, F) C).2.2 = R

theorem reach_done (k : ℕ) (gens : List ℕ) (cap n : ℕ) (A : List ℕ) :
    Reach k gens cap (n + 1) A [] (A, true) := fun _ _ => rfl

theorem reach_layer (k : ℕ) (gens : List ℕ) (cap n : ℕ) (A : List ℕ) (x : ℕ) (l : List ℕ)
    (R : List ℕ × Bool) (hc : Nat.ble cap (lenR A) = false)
    (h : ReachMid k gens cap n A [] (x :: l) R) : Reach k gens cap (n + 1) A (x :: l) R := by
  intro t ht
  change Bool.rec (motive := fun _ => List ℕ × Bool) (Prod.rec (motive := fun _ => List ℕ × Bool)
        (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool)
          (fun a f => bfsTC k gens cap n s a f) r)
        (layerT k gens t A (x :: l)))
      (A, false) (Nat.ble cap (lenR A)) = R
  rw [hc, prodRec3B]
  exact h t ht

theorem mid_end (k : ℕ) (gens : List ℕ) (cap n : ℕ) (A F : List ℕ) (R : List ℕ × Bool)
    (h : Reach k gens cap n A F R) : ReachMid k gens cap n A F [] R := fun t ht => h t ht

theorem mid_chunk (d k : ℕ) (gens : List ℕ) (cap n : ℕ) (A F C A' F' rest : List ℕ)
    (R : List ℕ × Bool) (hp : pieceT d k gens A F C A' F' = true)
    (h : ReachMid k gens cap n A' F' rest R) : ReachMid k gens cap n A F (C ++ rest) R := by
  intro t ht
  have hp' : (runT k gens (ofListT d k A, A, F) C).2 = (A', F') := by
    simpa [pieceT] using hp
  have hs := runT_same k gens C (t, A, F) (ofListT d k A, A, F)
    ⟨fun z => by rw [ht, memK_ofListT], rfl⟩
  have hi := runT_inv k gens C (t, A, F) ht
  rw [runT_append]
  obtain ⟨hs1, hs2⟩ := hs
  rw [hp'] at hs2
  have e : runT k gens (t, A, F) C = ((runT k gens (t, A, F) C).1, A', F') := by
    rw [← hs2]
  rw [e] at hi ⊢
  exact h _ hi

theorem elemsTC_of_reach (d k : ℕ) (gens : List ℕ) (cap : ℕ) (R : List ℕ × Bool)
    (h : Reach k gens cap 200 [oneP] [oneP] R) : elemsTC d k gens cap = R := by
  apply h
  intro z
  rw [memK_insK, memK_fullT, Bool.or_false, List.contains_cons, List.contains_nil, Bool.or_false,
    beq_symm]



theorem runLayersT_spec (k : ℕ) (gens : List ℕ) (cap : ℕ) : ∀ (j : ℕ) (t : NT ℕ) (A F : List ℕ)
    (s : NT ℕ × List ℕ × List ℕ), InvT k (t, A, F) → runLayersT k gens cap j t A F = some s →
      InvT k s ∧ ∀ n, bfsTC k gens cap (n + j) t A F = bfsTC k gens cap n s.1 s.2.1 s.2.2 := by
  intro j
  induction j with
  | zero =>
    intro t A F s hi hs
    have hs' : some (t, A, F) = some s := hs
    cases Option.some.inj hs'
    exact ⟨hi, fun n => rfl⟩
  | succ j ih =>
    intro t A F s hi hs
    cases F with
    | nil => exact absurd hs (by intro h; cases h)
    | cons x l =>
      have hs' : Bool.rec (motive := fun _ => Option (NT ℕ × List ℕ × List ℕ))
          (Prod.rec (motive := fun _ => Option (NT ℕ × List ℕ × List ℕ))
            (fun s r => Prod.rec (motive := fun _ => Option (NT ℕ × List ℕ × List ℕ))
              (fun a f => runLayersT k gens cap j s a f) r)
            (layerT k gens t A (x :: l)))
          none (Nat.ble cap (lenR A)) = some s := hs
      cases hc : Nat.ble cap (lenR A)
      · rw [hc] at hs'
        have e : ∀ (g : NT ℕ → List ℕ → List ℕ → Option (NT ℕ × List ℕ × List ℕ))
            (p : NT ℕ × List ℕ × List ℕ),
            Prod.rec (motive := fun _ => Option (NT ℕ × List ℕ × List ℕ))
              (fun s r => Prod.rec (motive := fun _ => Option (NT ℕ × List ℕ × List ℕ))
                (fun a f => g s a f) r) p = g p.1 p.2.1 p.2.2 := by
          intro g p; rcases p with ⟨_, _, _⟩; rfl
        rw [e] at hs'
        have hi' := runT_inv k gens (x :: l) (t, A, []) hi
        obtain ⟨h1, h2⟩ := ih _ _ _ s hi' hs'
        refine ⟨h1, fun n => ?_⟩
        rw [← h2 n]
        change Bool.rec (motive := fun _ => List ℕ × Bool)
            (Prod.rec (motive := fun _ => List ℕ × Bool)
              (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool)
                (fun a f => bfsTC k gens cap (n + j) s a f) r)
              (layerT k gens t A (x :: l)))
            (A, false) (Nat.ble cap (lenR A)) = _
        rw [hc, prodRec3B]
        rfl
      · rw [hc] at hs'
        exact absurd hs' (by intro h; cases h)

theorem reach_layers (d k : ℕ) (gens : List ℕ) (cap n j : ℕ) (A F A' F' : List ℕ)
    (R : List ℕ × Bool) (hp : layersT d k gens cap j A F A' F' = true)
    (h : Reach k gens cap n A' F' R) : Reach k gens cap (n + j) A F R := by
  intro t ht
  have hi : InvT k (ofListT d k A, A, F) := fun z => memK_ofListT d k A z
  rw [bfsTC_same k gens cap (n + j) t (ofListT d k A) A F (fun z => by rw [ht, memK_ofListT])]
  unfold layersT at hp
  revert hp
  cases hr : runLayersT k gens cap j (ofListT d k A) A F with
  | none => intro hp; exact absurd hp (by intro e; cases e)
  | some s =>
    intro hp
    have hs : s.2 = (A', F') := by simpa using hp
    obtain ⟨h1, h2⟩ := runLayersT_spec k gens cap j _ A F s hi hr
    rw [h2 n]
    have e : s = (s.1, A', F') := by rw [← hs]
    rw [e] at h1 ⊢
    exact h _ h1

theorem take_drop_split (L : List ℕ) (p q1 q2 : ℕ) :
    (L.drop p).take (q1 + q2) = (L.drop p).take q1 ++ (L.drop (p + q1)).take q2 := by
  rw [List.take_add, List.drop_drop]

theorem reach_layer' (k : ℕ) (gens : List ℕ) (cap n : ℕ) (A fr : List ℕ) (R : List ℕ × Bool)
    (hc : Nat.ble cap (lenR A) = false) (hne : fr ≠ [])
    (h : ReachMid k gens cap n A [] fr R) : Reach k gens cap (n + 1) A fr R := by
  cases fr with
  | nil => exact absurd rfl hne
  | cons x l => exact reach_layer k gens cap n A x l R hc h

theorem mid_chunk' (d k : ℕ) (gens : List ℕ) (cap n : ℕ) (A F A' F' L : List ℕ) (p q1 q2 : ℕ)
    (R : List ℕ × Bool) (hp : pieceT d k gens A F ((L.drop p).take q1) A' F' = true)
    (h : ReachMid k gens cap n A' F' ((L.drop (p + q1)).take q2) R) :
    ReachMid k gens cap n A F ((L.drop p).take (q1 + q2)) R := by
  rw [take_drop_split]
  exact mid_chunk d k gens cap n A F _ A' F' _ R hp h

theorem mid_last (d k : ℕ) (gens : List ℕ) (cap n : ℕ) (A F C A' F' : List ℕ)
    (R : List ℕ × Bool) (hp : pieceT d k gens A F C A' F' = true)
    (h : Reach k gens cap n A' F' R) : ReachMid k gens cap n A F C R := by
  rw [← List.append_nil C]
  exact mid_chunk d k gens cap n A F C A' F' [] R hp (mid_end k gens cap n A' F' R h)

theorem ble_lenR (cap : ℕ) (L : List ℕ) (h : L.length < cap) (a : ℕ) :
    Nat.ble cap (lenR (L.drop a)) = false := by
  have h' : ¬ cap ≤ lenR (L.drop a) := by
    rw [lenR_eq, List.length_drop]
    omega
  cases hb : Nat.ble cap (lenR (L.drop a))
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) h'

theorem reach_done' (k : ℕ) (gens : List ℕ) (cap n : ℕ) (A L : List ℕ) (h : A = L) :
    Reach k gens cap (n + 1) A [] (L, true) := by
  subst h
  exact reach_done k gens cap n A

theorem elemsP_eq_T (D k : ℕ) (gp : List ℕ) (cap : ℕ) :
    elemsP gp cap = (elemsTC D k gp cap).1 := by
  rw [elemsP_eq_C 16 65521, elemsC_T 16 65521 D k]

theorem closedP_elemsP_T (D k : ℕ) (gp : List ℕ) (cap : ℕ) :
    closedP gp (elemsP gp cap) = closedTC D k gp cap := by
  rw [closedP_elemsP 16 65521, closedC, elemsC_T 16 65521 D k, closedP_T D k]
  rfl

open CFSG.Quasithin.H13.Mat8Cert in
theorem subB_of_bfs (gens : List (List ℕ)) (hg : gens.all validB = true) (L : List ℕ)
    (h : elemsTC 16 65521 (gens.map code64R) 100000 = (L, true)) (h1 : L.contains oneP = true) :
    subB gens (elemsOf gens) = true := by
  have hE : elemsP (gens.map code64R) 100000 = L := by rw [elemsP_eq_T 16 65521, h]
  have hlt := (CFSG.KC.Mat8S.nInv_elemsP (gens.map code64R) 100000).2
  have c2 : closedB gens (elemsF gens 100000) = true := by
    rw [CFSG.KC.Mat8S.closedB_elemsF, if_pos hg, closedP_elemsP_T 16 65521, closedTC, h]
    rfl
  have c3 : nodupB (elemsF gens 100000) = true := by
    rw [nodupB_toP, CFSG.KC.Mat8S.nodupP_elemsF_if, if_pos hg]
  have c4 : (elemsF gens 100000).contains one8 = true := by
    rw [elemsF, if_pos hg, ← oneP_eq, CFSG.KC.Mat8S.contains_map_unpackM _ hlt _ oneP_lt, hE, h1]
  rw [elemsOf_toF, subB, CFSG.KC.Mat8S.all_validB_elemsF, if_pos hg, c2, c3, c4, hg]
  rfl

open CFSG.Quasithin.H13.Mat8Cert in
theorem elemsF_T (gens : List (List ℕ)) (cap : ℕ) :
    elemsF gens cap = if gens.all validB then
      ((elemsTC 16 65521 (gens.map code64R) cap).1).map unpackM
    else elemsOf gens cap := by
  rw [elemsF, elemsP_eq_T 16 65521]

@[expose] def elemsOfZ (gens : List (List ℕ)) (cap : ℕ) : List (List ℕ) :=
  CFSG.Quasithin.H13.Mat8Cert.elemsOf gens cap

open CFSG.Quasithin.H13.Mat8Cert in
theorem elemsOf_T (gens : List (List ℕ)) (cap : ℕ) :
    elemsOf gens cap = if gens.all validB then
      ((elemsTC 16 65521 (gens.map code64R) cap).1).map unpackM
    else elemsOfZ gens cap := by
  rw [elemsOfZ, ← elemsF_T, elemsOf_toF]

end CFSG.KC.Mat8T

end
