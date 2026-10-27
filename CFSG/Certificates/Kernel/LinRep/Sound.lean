module

public import CFSG.Certificates.Kernel.Spor.BfsReplay

public section

namespace CFSG.KC.LinRepSound

open CFSG.PSL3Four.Native CFSG.KS.BfsReplay

@[expose] def term (b : Bool) (x : Nat) : Nat := if b then x else 0

@[expose] def ev (c : Nat → Nat) (v : Nat) : Nat :=
  term (v.testBit 0) (c 0) ^^^ term (v.testBit 1) (c 1) ^^^ term (v.testBit 2) (c 2) ^^^
    term (v.testBit 3) (c 3) ^^^ term (v.testBit 4) (c 4) ^^^ term (v.testBit 5) (c 5)

@[expose] def linTab (c : Nat → Nat) : Tab := Array.ofFn (n := 64) fun v => ev c v.val

@[expose] def col (w i : Nat) : Nat := Nat.land (Nat.shiftRight w (Nat.mul 6 i)) 63

theorem foldl_eq_ev (c : Nat → Nat) (v : Nat) :
    (List.range 6).foldl (fun r i => if v.testBit i then r ^^^ c i else r) 0 = ev c v := by
  have e : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  rw [e]
  simp only [List.foldl_cons, List.foldl_nil, ev, term]
  cases v.testBit 0 <;> cases v.testBit 1 <;> cases v.testBit 2 <;> cases v.testBit 3 <;>
    cases v.testBit 4 <;> cases v.testBit 5 <;> simp

theorem term_xor (b b' : Bool) (x : Nat) : term (b ^^ b') x = term b x ^^^ term b' x := by
  cases b <;> cases b' <;> simp [term]

theorem ev_xor (c : Nat → Nat) (u v : Nat) : ev c (u ^^^ v) = ev c u ^^^ ev c v := by
  simp only [ev, Nat.testBit_xor, term_xor]
  ac_rfl

theorem ev_zero (c : Nat → Nat) : ev c 0 = 0 := by
  simp [ev, term]

theorem ev_term (c : Nat → Nat) (b : Bool) (x : Nat) : ev c (term b x) = term b (ev c x) := by
  cases b
  · simp [term, ev_zero]
  · rfl

theorem ev_congr {a b : Nat → Nat} (h : ∀ i < 6, a i = b i) (v : Nat) : ev a v = ev b v := by
  simp only [ev, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega)]

theorem term_lt {b : Bool} {x : Nat} (h : x < 64) : term b x < 64 := by
  cases b <;> simp [term, h]

theorem ev_lt {c : Nat → Nat} (h : ∀ i < 6, c i < 64) (v : Nat) : ev c v < 64 := by
  have hx : ∀ {x y : Nat}, x < 2 ^ 6 → y < 2 ^ 6 → x ^^^ y < 2 ^ 6 := fun hx hy =>
    Nat.xor_lt_two_pow hx hy
  have ht : ∀ i < 6, ∀ b, term b (c i) < 2 ^ 6 := fun i hi b => term_lt (h i hi)
  exact hx (hx (hx (hx (hx (ht 0 (by omega) _) (ht 1 (by omega) _)) (ht 2 (by omega) _))
    (ht 3 (by omega) _)) (ht 4 (by omega) _)) (ht 5 (by omega) _)

theorem ev_eq (c : Nat → Nat) (v : Nat) : ev c v =
    term (v.testBit 0) (c 0) ^^^ term (v.testBit 1) (c 1) ^^^ term (v.testBit 2) (c 2) ^^^
      term (v.testBit 3) (c 3) ^^^ term (v.testBit 4) (c 4) ^^^ term (v.testBit 5) (c 5) := rfl

theorem ev_ev (a b : Nat → Nat) (v : Nat) : ev a (ev b v) = ev (fun i => ev a (b i)) v := by
  rw [ev_eq b v]
  simp only [ev_xor, ev_term]
  rfl

theorem six_cases {i : Nat} (hi : i < 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  omega

theorem ev_two_pow (c : Nat → Nat) {i : Nat} (hi : i < 6) : ev c (2 ^ i) = c i := by
  simp only [ev, Nat.testBit_two_pow]
  rcases six_cases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [term]

theorem two_pow_lt {i : Nat} (hi : i < 6) : 2 ^ i < 64 := by
  rcases six_cases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ev_id : ∀ v < 64, ev (fun i => 2 ^ i) v = v := by decide

theorem linTab_get (c : Nat → Nat) {v : Nat} (hv : v < 64) : (linTab c)[v]! = ev c v := by
  rw [getElem!_pos (linTab c) v (by simpa [linTab] using hv)]
  simp [linTab]

theorem linTab_congr {a b : Nat → Nat} (h : ∀ i < 6, a i = b i) : linTab a = linTab b := by
  unfold linTab
  congr 1
  funext v
  exact ev_congr h _

theorem linTab_get_two_pow (c : Nat → Nat) {i : Nat} (hi : i < 6) : (linTab c)[2 ^ i]! = c i := by
  rw [linTab_get c (two_pow_lt hi), ev_two_pow c hi]

theorem linTab_inj {a b : Nat → Nat} (h : linTab a = linTab b) : ∀ i < 6, a i = b i := by
  intro i hi
  rw [← linTab_get_two_pow a hi, ← linTab_get_two_pow b hi, h]

theorem linTab_two_pow : linTab (fun i => 2 ^ i) = idTab 64 := by
  unfold linTab idTab
  congr 1
  funext v
  exact ev_id v.val v.isLt

theorem linTab_eq_id {c : Nat → Nat} (h : ∀ i < 6, c i = 2 ^ i) : linTab c = idTab 64 := by
  rw [linTab_congr h, linTab_two_pow]

theorem comp_linTab (a : Nat → Nat) {b : Nat → Nat} (hb : ∀ i < 6, b i < 64) :
    comp 64 (linTab a) (linTab b) = linTab (fun i => ev a (b i)) := by
  have e : linTab (fun i => ev a (b i)) =
      Array.ofFn (n := 64) fun v => ev (fun i => ev a (b i)) v.val := rfl
  unfold comp
  rw [e]
  refine congrArg (Array.ofFn (n := 64)) (funext fun v => ?_)
  rw [linTab_get b v.isLt, linTab_get a (ev_lt hb v), ev_ev]

theorem comp3_linTab {a b c : Nat → Nat} (hb : ∀ i < 6, b i < 64) (hc : ∀ i < 6, c i < 64) :
    comp 64 (linTab a) (comp 64 (linTab b) (comp 64 (linTab c) (linTab c))) =
      linTab (fun i => ev a (ev b (ev c (c i)))) := by
  have h1 : ∀ i < 6, ev c (c i) < 64 := fun i _ => ev_lt hc _
  have h2 : ∀ i < 6, ev b (ev c (c i)) < 64 := fun i _ => ev_lt hb _
  rw [comp_linTab c hc, comp_linTab b h1, comp_linTab a h2]

theorem col_lt (w i : Nat) : col w i < 64 := by
  unfold col
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem testBit_col (w : Nat) {i j : Nat} (hj : j < 6) :
    (col w i).testBit j = w.testBit (6 * i + j) := by
  have e : (63 : Nat) = 2 ^ 6 - 1 := rfl
  change ((w >>> (6 * i)) &&& 63).testBit j = _
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  simp [hj]

theorem col_inj {a b : Nat} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) (h : ∀ i < 6, col a i = col b i) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 36
  · have e : n = 6 * (n / 6) + n % 6 := (Nat.div_add_mod n 6).symm
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    rw [e, ← testBit_col a hm, ← testBit_col b hm, h _ (by omega)]
  · have hp : 2 ^ 36 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem leftStep_lin {gens : Array Tab} {gc : Nat → Nat → Nat} {step : Nat → Nat → Nat} {j : Nat}
    (hg : (∀ i < 6, gc j i < 64) ∧ gens[j]! = linTab (gc j))
    (hs : ∀ w, ∀ i < 6, col (step j w) i = ev (gc j) (col w i)) (w : Nat) :
    leftStep 64 gens j (linTab (col w)) = linTab (col (step j w)) := by
  unfold leftStep
  rw [hg.2, comp_linTab _ (fun i _ => col_lt w i)]
  exact linTab_congr fun i hi => (hs w i hi).symm

theorem replay_of_words {cnt : Nat} {gens : Array Tab} {gc : Nat → Nat → Nat}
    {step : Nat → Nat → Nat} {M par lab : Nat → Nat} {pos : Nat → Nat → Nat}
    (hg : ∀ j < gens.size, (∀ i < 6, gc j i < 64) ∧ gens[j]! = linTab (gc j))
    (hstep : ∀ j < gens.size, ∀ w, ∀ i < 6, col (step j w) i = ev (gc j) (col w i))
    (hpos : 0 < cnt) (h0 : ∀ i < 6, col (M 0) i = 2 ^ i) (hp0 : par 0 = 0) (hl0 : lab 0 = 0)
    (hlt : ∀ a < cnt, M a < 2 ^ 36)
    (hinj : ∀ a < cnt, ∀ b < cnt, M a = M b → a = b)
    (htree : ∀ i, 0 < i → i < cnt →
      par i < i ∧ lab i < gens.size ∧ M i = step (lab i) (M (par i)))
    (horder : ∀ i, 0 < i → i + 1 < cnt → LexLt (par i) (lab i) (par (i + 1)) (lab (i + 1)))
    (hclose : ∀ h < cnt, ∀ j < gens.size, pos h j < cnt ∧ step j (M h) = M (pos h j) ∧
      (pos h j = 0 ∨ ¬ LexLt h j (par (pos h j)) (lab (pos h j)))) :
    Replay (leftStep 64 gens) gens.size (idTab 64) cnt (fun i => linTab (col (M i))) par lab pos where
  pos_cnt := hpos
  root_eq := linTab_eq_id h0
  par_zero := hp0
  lab_zero := hl0
  inj a ha b hb e := hinj a ha b hb (col_inj (hlt a ha) (hlt b hb) (linTab_inj e))
  tree i hi hc := by
    obtain ⟨h1, h2, h3⟩ := htree i hi hc
    refine ⟨h1, h2, ?_⟩
    rw [leftStep_lin (hg _ h2) (hstep _ h2), ← h3]
  order := horder
  close h hh j hj := by
    obtain ⟨h1, h2, h3⟩ := hclose h hh j hj
    refine ⟨h1, ?_, h3⟩
    rw [leftStep_lin (hg j hj) (hstep j hj), h2]

theorem enum_of_words {cnt cap : Nat} {gens : Array Tab} {gc : Nat → Nat → Nat}
    {step : Nat → Nat → Nat} {M par lab : Nat → Nat} {pos : Nat → Nat → Nat}
    (hg : ∀ j < gens.size, (∀ i < 6, gc j i < 64) ∧ gens[j]! = linTab (gc j))
    (hstep : ∀ j < gens.size, ∀ w, ∀ i < 6, col (step j w) i = ev (gc j) (col w i))
    (hpos : 0 < cnt) (h0 : ∀ i < 6, col (M 0) i = 2 ^ i) (hp0 : par 0 = 0) (hl0 : lab 0 = 0)
    (hlt : ∀ a < cnt, M a < 2 ^ 36)
    (hinj : ∀ a < cnt, ∀ b < cnt, M a = M b → a = b)
    (htree : ∀ i, 0 < i → i < cnt →
      par i < i ∧ lab i < gens.size ∧ M i = step (lab i) (M (par i)))
    (horder : ∀ i, 0 < i → i + 1 < cnt → LexLt (par i) (lab i) (par (i + 1)) (lab (i + 1)))
    (hclose : ∀ h < cnt, ∀ j < gens.size, pos h j < cnt ∧ step j (M h) = M (pos h j) ∧
      (pos h j = 0 ∨ ¬ LexLt h j (par (pos h j)) (lab (pos h j))))
    (hcap : cnt ≤ cap) :
    enumOK 64 gens (enumBFS 64 gens cap) = true ∧ (enumBFS 64 gens cap).tabs.size = cnt ∧
      ∀ i < cnt, (enumBFS 64 gens cap).tabs[i]! = linTab (col (M i)) := by
  obtain ⟨e, ok⟩ := enumBFS_replay
    (replay_of_words hg hstep hpos h0 hp0 hl0 hlt hinj htree horder hclose) hcap
  rw [e]
  refine ⟨ok, by simp, fun i hi => ?_⟩
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

end CFSG.KC.LinRepSound

end
