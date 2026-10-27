module

public import CFSG.Sporadic.GLQ.RegisterProgram

public section

namespace CFSG.KC.OpsHom

open CFSG.SectionRank.Native CFSG.Sporadic.GLQ

variable {M V M' V' : Type}

structure Hom (O : Ops M V) (O' : Ops M' V') where
  U : M' → M
  W : V' → V
  P : M' → Prop
  Q : V' → Prop
  mul {a b : M'} : P a → P b → O.mul (U a) (U b) = U (O'.mul a b) ∧ P (O'.mul a b)
  one : O.one = U O'.one ∧ P O'.one
  eq {a b : M'} : P a → P b → O.eq (U a) (U b) = O'.eq a b
  vmul {v : V'} {a : M'} : Q v → P a → O.vmul (W v) (U a) = W (O'.vmul v a) ∧ Q (O'.vmul v a)
  unit (k : Nat) : O.unit k = W (O'.unit k) ∧ Q (O'.unit k)
  vne {u v : V'} : Q u → Q v → O.vne (W u) (W v) = O'.vne u v

theorem all_map_congr {α β : Type} (xs : List α) (f : α → β) (p : β → Bool) (q : α → Bool)
    (h : ∀ x ∈ xs, p (f x) = q x) : (xs.map f).all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.all_cons, List.all_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem x hy)]

theorem get_map {α β : Type} [Inhabited α] [Inhabited β] (R : Array α) (f : α → β) {i : Nat}
    (hi : i < R.size) : (R.map f)[i]! = f R[i]! := by
  rw [getElem!_pos (R.map f) i (by simpa using hi), getElem!_pos R i hi, Array.getElem_map]

namespace Hom

variable {O : Ops M V} {O' : Ops M' V'} (H : Hom O O')

theorem pow_U : ∀ (e : Nat) {a : M'}, H.P a →
    O.pow (H.U a) e = H.U (O'.pow a e) ∧ H.P (O'.pow a e) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro a ha
    unfold Ops.pow
    by_cases he : e = 0
    · rw [ite_eq_left he, ite_eq_left he]
      exact H.one
    rw [ite_eq_right he, ite_eq_right he]
    by_cases he1 : e = 1
    · rw [ite_eq_left he1, ite_eq_left he1]
      exact ⟨rfl, ha⟩
    rw [ite_eq_right he1, ite_eq_right he1]
    obtain ⟨m1, p1⟩ := H.mul ha ha
    obtain ⟨y1, q1⟩ := ih (e / 2) (by omega) p1
    simp only
    rw [m1, y1]
    by_cases ho : e % 2 = 1
    · rw [ite_eq_left ho, ite_eq_left ho]
      exact H.mul ha q1
    · rw [ite_eq_right ho, ite_eq_right ho]
      exact ⟨rfl, q1⟩

theorem app_U {a : M'} (ha : H.P a) : ∀ (n : Nat) {v : V'}, H.Q v →
    O.app (H.U a) n (H.W v) = H.W (O'.app a n v) ∧ H.Q (O'.app a n v) := by
  intro n
  induction n with
  | zero => intro v hv; exact ⟨rfl, hv⟩
  | succ n ih =>
    intro v hv
    obtain ⟨e1, q1⟩ := H.vmul hv ha
    change O.app (H.U a) n (O.vmul (H.W v) (H.U a)) = H.W (O'.app a n (O'.vmul v a)) ∧ _
    rw [e1]
    exact ih q1

theorem appBase_U (b : Nat) : ∀ (xs : List M'), (∀ x ∈ xs, H.P x) → ∀ (n : Nat) {v : V'}, H.Q v →
    O.appBase b (xs.map H.U) n (H.W v) = H.W (O'.appBase b xs n v) ∧
      H.Q (O'.appBase b xs n v) := by
  intro xs
  induction xs with
  | nil => intro _ n v hv; exact ⟨rfl, hv⟩
  | cons x xs ih =>
    intro hx n v hv
    obtain ⟨e1, q1⟩ := H.app_U (hx x List.mem_cons_self) (n % b) hv
    change O.appBase b (xs.map H.U) (n / b) (O.app (H.U x) (n % b) (H.W v)) =
      H.W (O'.appBase b xs (n / b) (O'.app x (n % b) v)) ∧ _
    rw [e1]
    exact ih (fun y hy => hx y (List.mem_cons_of_mem x hy)) _ q1

theorem sqOK_U {a : M'} (ha : H.P a) : sqOK O (H.U a) = sqOK O' a := by
  unfold sqOK
  obtain ⟨m1, p1⟩ := H.mul ha ha
  rw [m1, H.one.1, H.eq p1 H.one.2]

theorem commOK_U {a b : M'} (ha : H.P a) (hb : H.P b) :
    O.commOK (H.U a) (H.U b) = O'.commOK a b := by
  unfold Ops.commOK
  rw [(H.mul ha hb).1, (H.mul hb ha).1, H.eq (H.mul ha hb).2 (H.mul hb ha).2]

theorem commsOK_U : ∀ (xs : List M'), (∀ x ∈ xs, H.P x) → O.commsOK (xs.map H.U) = O'.commsOK xs
  | [], _ => rfl
  | x :: xs, hx => by
    have hx' : ∀ y ∈ xs, H.P y := fun y hy => hx y (List.mem_cons_of_mem x hy)
    change ((xs.map H.U).all (O.commOK (H.U x)) && O.commsOK (xs.map H.U)) =
      (xs.all (O'.commOK x) && O'.commsOK xs)
    rw [commsOK_U xs hx', all_map_congr xs H.U _ _
      fun y hy => H.commOK_U (hx x List.mem_cons_self) (hx' y hy)]

theorem kerOK2_U {xs : List M'} (hx : ∀ x ∈ xs, H.P x) (tests : List Nat) :
    kerOK2 O (xs.map H.U) tests = kerOK2 O' xs tests := by
  unfold kerOK2
  rw [List.length_map]
  apply List.all_congr rfl
  intro n
  apply List.any_congr rfl
  intro t
  obtain ⟨u1, uq⟩ := H.unit t
  obtain ⟨a1, aq⟩ := H.appBase_U 2 xs hx (n + 1) uq
  rw [u1, a1, H.vne aq uq]

theorem elem2OK_U {xs : List M'} (hx : ∀ x ∈ xs, H.P x) (tests : List Nat) :
    elem2OK O (xs.map H.U) tests = elem2OK O' xs tests := by
  unfold elem2OK
  rw [H.commsOK_U xs hx, H.kerOK2_U hx, all_map_congr xs H.U _ _ fun x hx' => H.sqOK_U (hx x hx')]

@[expose] def UU (p : M' × M') : M × M := (H.U p.1, H.U p.2)

@[expose] def PP (p : M' × M') : Prop := H.P p.1 ∧ H.P p.2

theorem initRegsN_U [Inhabited M'] (n : Nat) (x y : M' × M') :
    initRegsN O n (H.UU x) (H.UU y) = (initRegsN O' n x y).map H.UU := by
  unfold initRegsN
  rw [Array.map_ofFn]
  congr 1
  funext r
  simp only [Function.comp_apply]
  split
  · rfl
  · split
    · rfl
    · rw [UU, H.one.1]

theorem initRegsN_P [Inhabited M'] {n : Nat} {x y : M' × M'} (hx : H.PP x) (hy : H.PP y) :
    ∀ r < (initRegsN O' n x y).size, H.PP (initRegsN O' n x y)[r]! := by
  intro r hr
  have hr' : r < n := by simpa [initRegsN] using hr
  unfold initRegsN
  rw [getElem!_pos _ r (by simpa using hr'), Array.getElem_ofFn]
  simp only
  split
  · exact hx
  · split
    · exact hy
    · exact ⟨H.one.2, H.one.2⟩

theorem runN_U [Inhabited M] [Inhabited M'] {R : Array (M' × M')}
    (hR : ∀ r < R.size, H.PP R[r]!) (ins : Instr) (hins : ins.lt R.size = true) :
    Instr.runN O (R.map H.UU) ins = (Instr.runN O' R ins).map H.UU ∧
      (Instr.runN O' R ins).size = R.size ∧
      ∀ r < (Instr.runN O' R ins).size, H.PP (Instr.runN O' R ins)[r]! := by
  have setP : ∀ (k : Nat) (x : M' × M'), H.PP x →
      ∀ r < (R.setIfInBounds k x).size, H.PP (R.setIfInBounds k x)[r]! := by
    intro k x hx r hr
    have hr' : r < R.size := by simpa using hr
    rw [getElem!_pos _ r hr, Array.getElem_setIfInBounds hr']
    split
    · exact hx
    · rw [← getElem!_pos R r hr']
      exact hR r hr'
  cases ins with
  | mu i j k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
    obtain ⟨⟨hi, hj⟩, -⟩ := hins
    obtain ⟨pi1, pi2⟩ := hR i hi
    obtain ⟨pj1, pj2⟩ := hR j hj
    refine ⟨?_, by simp [Instr.runN], setP k _ ⟨(H.mul pi1 pj1).2, (H.mul pj2 pi2).2⟩⟩
    simp only [Instr.runN, Array.map_setIfInBounds]
    rw [get_map R H.UU hi, get_map R H.UU hj]
    simp only [UU, (H.mul pi1 pj1).1, (H.mul pj2 pi2).1]
  | iv i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
    obtain ⟨hi, -⟩ := hins
    obtain ⟨pi1, pi2⟩ := hR i hi
    refine ⟨?_, by simp [Instr.runN], setP k _ ⟨pi2, pi1⟩⟩
    simp only [Instr.runN, Array.map_setIfInBounds]
    rw [get_map R H.UU hi]
    rfl
  | pwr e i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
    obtain ⟨hi, -⟩ := hins
    obtain ⟨pi1, pi2⟩ := hR i hi
    refine ⟨?_, by simp [Instr.runN], setP k _ ⟨(H.pow_U e pi1).2, (H.pow_U e pi2).2⟩⟩
    simp only [Instr.runN, Array.map_setIfInBounds]
    rw [get_map R H.UU hi]
    simp only [UU, (H.pow_U e pi1).1, (H.pow_U e pi2).1]

theorem runProgN_U [Inhabited M] [Inhabited M'] (n : Nat) :
    ∀ (prog : List Instr), prog.all (Instr.lt n) = true → ∀ (R : Array (M' × M')), R.size = n →
      (∀ r < R.size, H.PP R[r]!) →
      runProgN O (R.map H.UU) prog = (runProgN O' R prog).map H.UU ∧
        (runProgN O' R prog).size = n ∧
        ∀ r < (runProgN O' R prog).size, H.PP (runProgN O' R prog)[r]!
  | [], _, R, hs, hR => ⟨rfl, hs, hR⟩
  | ins :: prog, hp, R, hs, hR => by
    rw [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨e1, s1, p1⟩ := H.runN_U hR ins (by rw [hs]; exact hp.1)
    change runProgN O (Instr.runN O (R.map H.UU) ins) prog =
      (runProgN O' (Instr.runN O' R ins) prog).map H.UU ∧ _
    rw [e1]
    exact runProgN_U n prog hp.2 _ (s1.trans hs) p1

theorem letterN_U {x y : M' × M'} (hx : H.PP x) (hy : H.PP y) (l : Int) :
    letterN O (H.UU x) (H.UU y) l = H.U (letterN O' x y l) ∧ H.P (letterN O' x y l) := by
  unfold letterN
  split
  · exact ⟨rfl, hx.1⟩
  · split
    · exact ⟨rfl, hx.2⟩
    · split
      · exact ⟨rfl, hy.1⟩
      · split
        · exact ⟨rfl, hy.2⟩
        · exact H.one

theorem signedWordN_U {x y : M' × M'} (hx : H.PP x) (hy : H.PP y) :
    ∀ w : List Int, signedWordN O (H.UU x) (H.UU y) w = H.U (signedWordN O' x y w) ∧
      H.P (signedWordN O' x y w)
  | [] => H.one
  | l :: w => by
    obtain ⟨e1, p1⟩ := H.letterN_U hx hy l
    obtain ⟨e2, p2⟩ := signedWordN_U hx hy w
    change O.mul (letterN O (H.UU x) (H.UU y) l) (signedWordN O (H.UU x) (H.UU y) w) =
      H.U (O'.mul (letterN O' x y l) (signedWordN O' x y w)) ∧ _
    rw [e1, e2]
    exact H.mul p1 p2

end Hom

end CFSG.KC.OpsHom

end
