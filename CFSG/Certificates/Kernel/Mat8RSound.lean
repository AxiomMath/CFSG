module

public import Certificates.Data.Kernel.Mat8R
public import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CFSG.KC.Mat8R

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P

theorem foldR_eq {α β : Type} (f : β → α → β) (l : List α) :
    ∀ init, foldR f init l = l.foldl f init := by
  induction l with
  | nil => intro init; rfl
  | cons x l ih => intro init; exact ih (f init x)

theorem lenR_eq {α : Type} (l : List α) : lenR l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg Nat.succ ih

theorem stepY_eq (st : NT ℕ × List ℕ × List ℕ) (y : ℕ) :
    stepY st y = if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2) := by
  rcases st with ⟨t, a, f⟩
  change Bool.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ) (insP t y, y :: a, y :: f) (t, a, f)
    (memP t y) = _
  cases memP t y <;> rfl

theorem foldl_range_getD {β : Type} (F : β → ℕ → β) (d : ℕ) :
    ∀ (l : List ℕ) (st : β),
      (List.range l.length).foldl (fun st i => F st (l.getD i d)) st = l.foldl F st := by
  intro l
  induction l with
  | nil => intro st; rfl
  | cons x l ih =>
    intro st
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map, List.foldl_cons]
    exact ih (F st x)

theorem layerR_eq (gens : List ℕ) (seen : NT ℕ) (acc fr : List ℕ) :
    layerR gens seen acc fr =
      fr.foldl (fun (st : NT ℕ × List ℕ × List ℕ) x =>
          (List.range gens.length).foldl (fun (st : NT ℕ × List ℕ × List ℕ) i =>
            let y := mulP (gens.getD i oneP) x
            if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)) st)
        (seen, acc, []) := by
  rw [layerR, foldR_eq]
  congr 1
  funext st x
  rw [foldR_eq, foldl_range_getD (fun st g => if memP st.1 (mulP g x) then st else
    (insP st.1 (mulP g x), mulP g x :: st.2.1, mulP g x :: st.2.2)) oneP gens st]
  congr 1
  funext st g
  exact stepY_eq st (mulP g x)

theorem prodRec3 (g : NT ℕ → List ℕ → List ℕ → List ℕ) (p : NT ℕ × List ℕ × List ℕ) :
    Prod.rec (motive := fun _ => List ℕ)
      (fun s r => Prod.rec (motive := fun _ => List ℕ) (fun a f => g s a f) r) p =
      g p.1 p.2.1 p.2.2 := by
  rcases p with ⟨s, a, f⟩
  rfl

theorem bfsR_eq (gens : List ℕ) (cap : ℕ) :
    ∀ fuel seen acc fr, bfsR gens cap fuel seen acc fr = bfsP gens cap fuel seen acc fr := by
  intro fuel
  induction fuel with
  | zero => intro seen acc fr; rfl
  | succ n ih =>
    intro seen acc fr
    cases fr with
    | nil => rfl
    | cons x l =>
      rw [bfsP]
      on_goal 2 => exact fun h => List.cons_ne_nil x l h
      change Bool.rec (motive := fun _ => List ℕ) (Prod.rec (motive := fun _ => List ℕ)
            (fun s r => Prod.rec (motive := fun _ => List ℕ) (fun a f => bfsR gens cap n s a f) r)
            (layerR gens seen acc (x :: l)))
          acc (Nat.ble cap (lenR acc)) = _
      rw [lenR_eq, layerR_eq, prodRec3]
      cases hb : Nat.ble cap acc.length with
      | true => exact (if_pos (Nat.le_of_ble_eq_true hb)).symm
      | false =>
        have h : ¬ cap ≤ acc.length := fun h' => by
          rw [Nat.ble_eq_true_of_le h'] at hb
          exact absurd hb (by decide)
        rw [if_neg h]
        exact ih _ _ _

theorem elemsR_eq (gens : List ℕ) (cap : ℕ) : elemsR gens cap = elemsP gens cap :=
  bfsR_eq gens cap 200 _ _ _

theorem elemsFR_eq (gens : List (List ℕ)) (cap : ℕ) : elemsFR gens cap = elemsF gens cap := by
  rw [elemsFR, elemsF, elemsR_eq]

theorem land_two_pow (b u : ℕ) : b &&& 2 ^ u = if b.testBit u then 2 ^ u else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases h : u = j
  · subst h
    cases hb : b.testBit u <;> simp [Nat.testBit_two_pow]
  · cases hb : b.testBit u <;> simp [Nat.testBit_two_pow, h]

theorem bitB_eq (b u : ℕ) : bitB b u = b.testBit u := by
  change Nat.blt 0 (b &&& 1 <<< u) = _
  rw [Nat.one_shiftLeft, land_two_pow]
  cases hb : b.testBit u with
  | true =>
    rw [if_pos rfl, Nat.blt_eq]
    exact Nat.two_pow_pos u
  | false => rfl

theorem testBit_lor_one (b x u : ℕ) :
    (Nat.lor b (Nat.shiftLeft 1 x)).testBit u = (b.testBit u || x == u) := by
  change (b ||| 1 <<< x).testBit u = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : x = u <;> simp [h]

theorem testBit_insAll (l : List ℕ) :
    ∀ b u, (insAll b l).testBit u = (b.testBit u || l.contains u) := by
  induction l with
  | nil => intro b u; simp [insAll, foldR]
  | cons x l ih =>
    intro b u
    change (insAll (Nat.lor b (Nat.shiftLeft 1 x)) l).testBit u = _
    rw [ih, testBit_lor_one, List.contains_cons, beq_symm u x]
    cases b.testBit u <;> cases (x == u) <;> cases l.contains u <;> rfl

def SpanInv (p : List ℕ × ℕ) : Prop := ∀ u, p.2.testBit u = p.1.contains u

theorem spanStep_eq (p : List ℕ × ℕ) (hp : SpanInv p) (v : ℕ) :
    (spanStep p v).1 = (fun S v => if S.contains v then S else S ++ S.map (· ^^^ v)) p.1 v ∧
      SpanInv (spanStep p v) := by
  rcases p with ⟨S, b⟩
  have hv : bitB b v = S.contains v := by rw [bitB_eq]; exact hp v
  have hd : spanStep (S, b) v = Bool.rec (motive := fun _ => List ℕ × ℕ)
      (S ++ S.map (· ^^^ v), insAll b (S.map (· ^^^ v))) (S, b) (bitB b v) := rfl
  rw [hd, hv]
  cases hc : S.contains v
  · refine ⟨?_, ?_⟩
    · change S ++ S.map (· ^^^ v) = if S.contains v = true then S else S ++ S.map (· ^^^ v)
      rw [if_neg (by rw [hc]; exact Bool.false_ne_true)]
    intro u
    change (insAll b (S.map (· ^^^ v))).testBit u = (S ++ S.map (· ^^^ v)).contains u
    rw [testBit_insAll, hp u, List.contains_append]
  · refine ⟨?_, hp⟩
    change S = if S.contains v = true then S else S ++ S.map (· ^^^ v)
    rw [if_pos hc]

theorem spanT_aux (vs : List ℕ) :
    ∀ p, SpanInv p → (foldR spanStep p vs).1 =
        vs.foldl (fun S v => if S.contains v then S else S ++ S.map (· ^^^ v)) p.1 ∧
      SpanInv (foldR spanStep p vs) := by
  induction vs with
  | nil => intro p hp; exact ⟨rfl, hp⟩
  | cons v vs ih =>
    intro p hp
    obtain ⟨h1, h2⟩ := spanStep_eq p hp v
    obtain ⟨h3, h4⟩ := ih (spanStep p v) h2
    refine ⟨?_, h4⟩
    change (foldR spanStep (spanStep p v) vs).1 = _
    rw [h3, h1]
    rfl

theorem spanInv_init : SpanInv ([nat_lit 0], nat_lit 1) := by
  intro u
  change Nat.testBit 1 u = [0].contains u
  rcases u with _ | u
  · rfl
  · simp [Nat.testBit_succ]

theorem spanT_fst (vs : List ℕ) : (spanT vs).1 = spanN vs := (spanT_aux vs _ spanInv_init).1

theorem bitB_spanT (vs : List ℕ) (u : ℕ) : bitB (spanT vs).2 u = (spanN vs).contains u := by
  have h : (spanT vs).2.testBit u = (spanT vs).1.contains u := (spanT_aux vs _ spanInv_init).2 u
  rw [bitB_eq, h, spanT_fst]

theorem rangeAllB_eq (b : ℕ) : ∀ n, rangeAllB b n = (List.range n).all (bitB b) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.all_append, ← ih, List.all_cons, List.all_nil, Bool.and_true]
    change Bool.rec (motive := fun _ => Bool) false (rangeAllB b n) (bitB b n) = _
    cases bitB b n <;> simp

theorem all_range_spanN (vs : List ℕ) :
    (List.range 256).all (Std.HashSet.ofList (spanN vs)).contains = rangeAllB (spanT vs).2 256 := by
  rw [rangeAllB_eq]
  congr 1
  funext u
  rw [Std.HashSet.contains_ofList, bitB_spanT]

end CFSG.KC.Mat8R

end
