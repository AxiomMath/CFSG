module

public import Certificates.Data.Kernel.Mat8C
public import CFSG.Certificates.Kernel.Mat8SSound

public section

namespace CFSG.KC.Mat8C

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P CFSG.KC.Mat8R CFSG.KC.Mat8S

variable (d m : ℕ) (gens : List ℕ) (cap : ℕ)

theorem bfsS_cons (n : ℕ) (s : NT ℕ) (acc : List ℕ) (x : ℕ) (l : List ℕ) :
    bfsS d m gens cap (n + 1) s acc (x :: l) =
      Bool.rec (motive := fun _ => List ℕ) (bfsS d m gens cap n (layerS d m gens s acc (x :: l)).1
        (layerS d m gens s acc (x :: l)).2.1 (layerS d m gens s acc (x :: l)).2.2)
        acc (Nat.ble cap (lenR acc)) := by
  change Bool.rec (motive := fun _ => List ℕ) (Prod.rec (motive := fun _ => List ℕ)
      (fun s r => Prod.rec (motive := fun _ => List ℕ) (fun a f => bfsS d m gens cap n s a f) r)
      (layerS d m gens s acc (x :: l))) acc (Nat.ble cap (lenR acc)) = _
  generalize layerS d m gens s acc (x :: l) = p
  rcases p with ⟨s', a', f'⟩
  rfl

theorem bfsC_cons (n : ℕ) (s : NT ℕ) (acc : List ℕ) (x : ℕ) (l : List ℕ) :
    bfsC d m gens cap (n + 1) s acc (x :: l) =
      Bool.rec (motive := fun _ => List ℕ × Bool) (bfsC d m gens cap n (layerS d m gens s acc (x :: l)).1
        (layerS d m gens s acc (x :: l)).2.1 (layerS d m gens s acc (x :: l)).2.2)
        (acc, false) (Nat.ble cap (lenR acc)) := by
  change Bool.rec (motive := fun _ => List ℕ × Bool) (Prod.rec (motive := fun _ => List ℕ × Bool)
      (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool)
        (fun a f => bfsC d m gens cap n s a f) r)
      (layerS d m gens s acc (x :: l))) (acc, false) (Nat.ble cap (lenR acc)) = _
  generalize layerS d m gens s acc (x :: l) = p
  rcases p with ⟨s', a', f'⟩
  rfl

theorem bfsE_cons (n : ℕ) (s : NT ℕ) (acc : List ℕ) (x : ℕ) (l : List ℕ) (c : ℕ) :
    bfsE d m gens cap (n + 1) s acc (x :: l) c =
      Bool.rec (motive := fun _ => ℕ) (bfsE d m gens cap n (layerE d m cap gens s acc (x :: l) c).1
        (layerE d m cap gens s acc (x :: l) c).2.1 (layerE d m cap gens s acc (x :: l) c).2.2.1
        (layerE d m cap gens s acc (x :: l) c).2.2.2)
        c (Nat.ble cap c) := by
  change Bool.rec (motive := fun _ => ℕ) (Prod.rec (motive := fun _ => ℕ)
      (fun s r => Prod.rec (motive := fun _ => ℕ)
        (fun a r => Prod.rec (motive := fun _ => ℕ) (fun f c' => bfsE d m gens cap n s a f c') r) r)
      (layerE d m cap gens s acc (x :: l) c)) c (Nat.ble cap c) = _
  generalize layerE d m cap gens s acc (x :: l) c = p
  rcases p with ⟨s', a', f', c'⟩
  rfl

theorem stepS_eq (t : NT ℕ) (a f : List ℕ) (y : ℕ) :
    stepS d m (t, a, f) y = Bool.rec (insS d m t y, y :: a, y :: f) (t, a, f) (memS d m t y) :=
  rfl

theorem bfsC_fst : ∀ fuel s acc fr,
    (bfsC d m gens cap fuel s acc fr).1 = bfsS d m gens cap fuel s acc fr := by
  intro fuel
  induction fuel with
  | zero => intro s acc fr; rfl
  | succ n ih =>
    intro s acc fr
    cases fr with
    | nil => rfl
    | cons x l =>
      rw [bfsC_cons, bfsS_cons]
      generalize Nat.ble cap (lenR acc) = b
      cases b
      · exact ih _ _ _
      · rfl

def CI (s : NT ℕ) (acc fr : List ℕ) : Prop :=
  (∀ z, memS d m s z = acc.contains z) ∧ ∀ x ∈ acc, x ∈ fr ∨ ∀ g ∈ gens, mulP g x ∈ acc

def SI (acc0 : List ℕ) (st : NT ℕ × List ℕ × List ℕ) : Prop :=
  (∀ z, memS d m st.1 z = st.2.1.contains z) ∧ (∀ z ∈ acc0, z ∈ st.2.1) ∧
    ∀ z ∈ st.2.1, z ∈ st.2.2 ∨ z ∈ acc0

theorem stepS_SI (acc0 : List ℕ) (st : NT ℕ × List ℕ × List ℕ) (y : ℕ) (h : SI d m acc0 st) :
    SI d m acc0 (stepS d m st y) ∧ y ∈ (stepS d m st y).2.1 ∧
      ∀ z ∈ st.2.1, z ∈ (stepS d m st y).2.1 := by
  obtain ⟨t, a, f⟩ := st
  obtain ⟨h1, h2, h3⟩ := h
  have h1' : ∀ z, memS d m t z = a.contains z := h1
  have h2' : ∀ z ∈ acc0, z ∈ a := h2
  have h3' : ∀ z ∈ a, z ∈ f ∨ z ∈ acc0 := h3
  rw [stepS_eq]
  cases hc : memS d m t y
  · refine ⟨⟨fun z => ?_, fun z hz => List.mem_cons_of_mem _ (h2' z hz), fun z hz => ?_⟩,
      List.mem_cons.mpr (Or.inl rfl), fun z hz => List.mem_cons_of_mem _ hz⟩
    · change memS d m (insS d m t y) z = (y :: a).contains z
      rw [memS_insS, h1' z, List.contains_cons, beq_symm y z]
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
      · rcases h3' z hz with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
  · refine ⟨⟨h1, h2, h3⟩, ?_, fun z hz => hz⟩
    have e := h1' y
    rw [hc] at e
    exact List.contains_iff_mem.mp e.symm

theorem inner_SI (acc0 : List ℕ) (x : ℕ) : ∀ (gs : List ℕ) (st : NT ℕ × List ℕ × List ℕ),
    SI d m acc0 st →
      SI d m acc0 (foldR (fun st g => stepS d m st (mulP g x)) st gs) ∧
      (∀ g ∈ gs, mulP g x ∈ (foldR (fun st g => stepS d m st (mulP g x)) st gs).2.1) ∧
      ∀ z ∈ st.2.1, z ∈ (foldR (fun st g => stepS d m st (mulP g x)) st gs).2.1
  | [], st, h => ⟨h, fun g hg => absurd hg List.not_mem_nil, fun z hz => hz⟩
  | g :: gs, st, h => by
    obtain ⟨hs, hy, hm⟩ := stepS_SI d m acc0 st (mulP g x) h
    obtain ⟨r1, r2, r3⟩ := inner_SI acc0 x gs _ hs
    refine ⟨r1, fun g' hg' => ?_, fun z hz => r3 z (hm z hz)⟩
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact r3 _ hy
    · exact r2 g' hg'

theorem outer_SI (acc0 : List ℕ) : ∀ (fr : List ℕ) (st : NT ℕ × List ℕ × List ℕ),
    SI d m acc0 st →
      SI d m acc0 (foldR (fun st x => foldR (fun st g => stepS d m st (mulP g x)) st gens) st fr) ∧
      (∀ x ∈ fr, ∀ g ∈ gens, mulP g x ∈
        (foldR (fun st x => foldR (fun st g => stepS d m st (mulP g x)) st gens) st fr).2.1) ∧
      ∀ z ∈ st.2.1, z ∈
        (foldR (fun st x => foldR (fun st g => stepS d m st (mulP g x)) st gens) st fr).2.1
  | [], st, h => ⟨h, fun x hx => absurd hx List.not_mem_nil, fun z hz => hz⟩
  | x :: fr, st, h => by
    obtain ⟨hs, hy, hm⟩ := inner_SI d m acc0 x gens st h
    obtain ⟨r1, r2, r3⟩ := outer_SI acc0 fr _ hs
    refine ⟨r1, fun x' hx' g hg => ?_, fun z hz => r3 z (hm z hz)⟩
    rcases List.mem_cons.mp hx' with rfl | hx'
    · exact r3 _ (hy g hg)
    · exact r2 x' hx' g hg

theorem layerS_CI (s : NT ℕ) (acc fr : List ℕ) (h : CI d m gens s acc fr) :
    CI d m gens (layerS d m gens s acc fr).1 (layerS d m gens s acc fr).2.1
      (layerS d m gens s acc fr).2.2 := by
  have h0 : SI d m acc (s, acc, []) := ⟨h.1, fun z hz => hz, fun z hz => Or.inr hz⟩
  obtain ⟨⟨r1, r2, r3⟩, r4, -⟩ := outer_SI d m gens acc fr _ h0
  refine ⟨r1, fun x hx => ?_⟩
  rcases r3 x hx with h' | h'
  · exact Or.inl h'
  · rcases h.2 x h' with hf | hc
    · exact Or.inr (r4 x hf)
    · exact Or.inr fun g hg => r2 _ (hc g hg)

theorem bfsC_closed : ∀ fuel s acc fr, CI d m gens s acc fr →
    (bfsC d m gens cap fuel s acc fr).2 = true →
      ∀ x ∈ (bfsC d m gens cap fuel s acc fr).1, ∀ g ∈ gens,
        mulP g x ∈ (bfsC d m gens cap fuel s acc fr).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro s acc fr _ hf
    exact absurd hf Bool.false_ne_true
  | succ n ih =>
    intro s acc fr h hf
    cases fr with
    | nil =>
      intro x hx g hg
      rcases h.2 x hx with h' | h'
      · exact absurd h' List.not_mem_nil
      · exact h' g hg
    | cons x l =>
      rw [bfsC_cons] at hf ⊢
      cases hb : Nat.ble cap (lenR acc)
      · rw [hb] at hf
        exact ih _ _ _ (layerS_CI d m gens s acc (x :: l) h) hf
      · rw [hb] at hf
        exact absurd hf Bool.false_ne_true

theorem elemsP_eq_C (gp : List ℕ) (cap : ℕ) : elemsP gp cap = (elemsC d m gp cap).1 := by
  rw [← elemsS_eq d m, elemsC, bfsC_fst]
  rfl

@[expose] def closedC (d m : ℕ) (gp : List ℕ) (cap : ℕ) : Bool :=
  (elemsC d m gp cap).2 || closedP gp (elemsC d m gp cap).1

theorem closedP_elemsP (gp : List ℕ) (cap : ℕ) : closedP gp (elemsP gp cap) = closedC d m gp cap := by
  rw [closedC, elemsP_eq_C d m]
  cases hf : (elemsC d m gp cap).2
  · rw [Bool.false_or]
  · rw [Bool.true_or, closedP, List.all_eq_true]
    intro x hx
    rw [List.all_eq_true]
    intro g hg
    rw [memP_ofListP, List.contains_iff_mem]
    refine bfsC_closed d m gp cap 200 _ _ _ ⟨fun z => ?_, fun z hz => Or.inl hz⟩ hf x hx g hg
    rw [memS_insS, memS_empty, List.contains_cons, List.contains_nil, beq_symm]

def ER (p : NT ℕ × List ℕ × List ℕ) (q : NT ℕ × List ℕ × List ℕ × ℕ) : Prop :=
  q = (p.1, p.2.1, p.2.2, lenR p.2.1) ∨ cap ≤ lenR p.2.1

theorem stepS_len (st : NT ℕ × List ℕ × List ℕ) (y : ℕ) :
    lenR st.2.1 ≤ lenR (stepS d m st y).2.1 := by
  obtain ⟨t, a, f⟩ := st
  rw [stepS_eq]
  cases memS d m t y
  · exact Nat.le_succ _
  · exact Nat.le_refl _

theorem stepE_ER (p : NT ℕ × List ℕ × List ℕ) (q : NT ℕ × List ℕ × List ℕ × ℕ) (y : ℕ)
    (h : ER cap p q) : ER cap (stepS d m p y) (stepE d m cap q y) := by
  rcases h with rfl | h
  · obtain ⟨t, a, f⟩ := p
    change ER cap (stepS d m (t, a, f) y) (Bool.rec
      (Bool.rec (insS d m t y, y :: a, y :: f, Nat.succ (lenR a)) (t, a, f, lenR a) (memS d m t y))
      (t, a, f, lenR a) (Nat.ble cap (lenR a)))
    cases hb : Nat.ble cap (lenR a)
    · rw [stepS_eq]
      cases memS d m t y
      · exact Or.inl rfl
      · exact Or.inl rfl
    · exact Or.inr (Nat.le_trans (Nat.le_of_ble_eq_true hb) (stepS_len d m (t, a, f) y))
  · exact Or.inr (Nat.le_trans h (stepS_len d m p y))

theorem foldR_rel2 {α β γ : Type} (F : β → α → β) (G : γ → α → γ) (R : β → γ → Prop)
    (h : ∀ p q x, R p q → R (F p x) (G q x)) :
    ∀ (l : List α) (p : β) (q : γ), R p q → R (foldR F p l) (foldR G q l) := by
  intro l
  induction l with
  | nil => intro p q hpq; exact hpq
  | cons x l ih => intro p q hpq; exact ih _ _ (h p q x hpq)

theorem layerE_ER (s : NT ℕ) (acc fr : List ℕ) :
    ER cap (layerS d m gens s acc fr) (layerE d m cap gens s acc fr (lenR acc)) :=
  foldR_rel2 (fun st x => foldR (fun st g => stepS d m st (mulP g x)) st gens)
    (fun st x => foldR (fun st g => stepE d m cap st (mulP g x)) st gens) (ER cap)
    (fun p q x hpq => foldR_rel2 (fun st g => stepS d m st (mulP g x))
      (fun st g => stepE d m cap st (mulP g x)) (ER cap)
      (fun p q g hpq => stepE_ER d m cap p q (mulP g x) hpq) gens p q hpq)
    fr (s, acc, []) (s, acc, [], lenR acc) (Or.inl rfl)

theorem layerS_len (s : NT ℕ) (acc fr : List ℕ) : lenR acc ≤ lenR (layerS d m gens s acc fr).2.1 :=
  foldR_rel2 (fun st x => foldR (fun st g => stepS d m st (mulP g x)) st gens)
    (fun st x => foldR (fun st g => stepS d m st (mulP g x)) st gens)
    (fun _ q => lenR acc ≤ lenR q.2.1)
    (fun _ q x hq => foldR_rel2 (fun st g => stepS d m st (mulP g x))
      (fun st g => stepS d m st (mulP g x)) (fun _ q => lenR acc ≤ lenR q.2.1)
      (fun _ q g hq => Nat.le_trans hq (stepS_len d m q (mulP g x))) gens q q hq)
    fr (s, acc, []) (s, acc, []) (Nat.le_refl _)

theorem bfsS_len : ∀ fuel s acc fr, lenR acc ≤ lenR (bfsS d m gens cap fuel s acc fr) := by
  intro fuel
  induction fuel with
  | zero => intro s acc fr; exact Nat.le_refl _
  | succ n ih =>
    intro s acc fr
    cases fr with
    | nil => exact Nat.le_refl _
    | cons x l =>
      rw [bfsS_cons]
      generalize Nat.ble cap (lenR acc) = b
      cases b
      · exact Nat.le_trans (layerS_len d m gens s acc (x :: l)) (ih _ _ _)
      · exact Nat.le_refl _

theorem bfsE_le : ∀ fuel (p : NT ℕ × List ℕ × List ℕ) (q : NT ℕ × List ℕ × List ℕ × ℕ),
    ER cap p q → cap ≤ bfsE d m gens cap fuel q.1 q.2.1 q.2.2.1 q.2.2.2 →
      cap ≤ lenR (bfsS d m gens cap fuel p.1 p.2.1 p.2.2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p q h he
    rcases h with rfl | h
    · exact he
    · exact h
  | succ n ih =>
    intro p q h he
    rcases h with rfl | h
    · obtain ⟨s, a, f⟩ := p
      dsimp only at he ⊢
      cases f with
      | nil => exact he
      | cons x l =>
        rw [bfsE_cons] at he
        rw [bfsS_cons]
        cases hb : Nat.ble cap (lenR a)
        · rw [hb] at he
          exact ih _ _ (layerE_ER d m gens cap s a (x :: l)) he
        · exact Nat.le_of_ble_eq_true hb
    · exact Nat.le_trans h (bfsS_len d m gens cap _ _ _ _)

theorem reachE_le (gp : List ℕ) (cap : ℕ) (h : reachE d m gp cap = true) :
    cap ≤ (elemsP gp cap).length := by
  rw [← elemsS_eq d m, ← lenR_eq]
  exact bfsE_le d m gp cap 200 (insS d m (.tip []) oneP, [oneP], [oneP])
    (insS d m (.tip []) oneP, [oneP], [oneP], nat_lit 1) (Or.inl rfl) (Nat.le_of_ble_eq_true h)

theorem lt_length_elemsF (gens : List (List ℕ)) (k : ℕ) :
    decide (k < (elemsF gens (k + 1)).length) =
      (gens.all validB && reachE d m (gens.map code64R) (k + 1) || ltLenF gens k) := by
  cases h : (gens.all validB && reachE d m (gens.map code64R) (k + 1))
  · rw [Bool.false_or]
    rfl
  · rw [Bool.true_or, decide_eq_true_iff]
    rw [Bool.and_eq_true] at h
    rw [elemsF, if_pos h.1, List.length_map]
    exact reachE_le d m _ _ h.2

end CFSG.KC.Mat8C

end
