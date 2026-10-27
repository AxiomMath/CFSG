module

public import Certificates.Data.CFSGNative.MonsterVis.Frame
public import CFSG.Certificates.Kernel.MonsterB.BfsCore
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.KSearch

open CFSG.Monster.VisCert.Native CFSG.KC.Bfs

theorem forIn_yield_eq {β : Type} (l : List ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (G : β → ℕ → β) (h : ∀ a b, f a b = ForInStep.yield (G b a)) :
    forIn l init f = (l.foldl G init : β) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.foldl_cons, h]
    exact ih _

theorem foldl_idle {β : Type} (C : β → Prop) [DecidablePred C] (F : β → β) (l : List ℕ) (b : β)
    (hb : ¬ C b) : l.foldl (fun s _ => if C s then F s else s) b = b := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, if_neg hb]; exact ih

theorem forIn_break_eq {β : Type} (l : List ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (C : β → Prop) [DecidablePred C] (F : β → β)
    (h : ∀ a b, f a b = if C b then ForInStep.yield (F b) else ForInStep.done b) :
    forIn l init f = (l.foldl (fun s _ => if C s then F s else s) init : β) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.foldl_cons, h]
    by_cases hc : C init
    · rw [if_pos hc, if_pos hc]
      exact ih _
    · rw [if_neg hc, if_neg hc]
      exact (foldl_idle C F l init hc).symm

theorem get!_eq (b : ByteArray) (i : ℕ) : b.get! i = b[i]! := by
  rcases b with ⟨bs⟩
  by_cases h : i < bs.size
  · rw [getElem!_pos (⟨bs⟩ : ByteArray) i h]
    change bs[i]! = bs[i]
    rw [getElem!_pos bs i h]
  · rw [getElem!_neg (⟨bs⟩ : ByteArray) i h]
    change bs[i]! = default
    rw [getElem!_neg bs i h]

theorem rd8_eq (b : ByteArray) (i : ℕ) : rd8 b i = b[i]!.toNat := by
  unfold rd8
  rw [get!_eq]

theorem rd8_lt (b : ByteArray) (i : ℕ) : rd8 b i < 256 := by
  unfold rd8
  exact UInt8.toNat_lt _

theorem rd8_of_le {b : ByteArray} {i : ℕ} (h : b.size ≤ i) : rd8 b i = 0 := by
  rw [rd8_eq, getElem!_neg b i (by omega)]
  rfl

@[simp] theorem size_wr8 (b : ByteArray) (i x : ℕ) : (wr8 b i x).size = b.size := by
  unfold wr8
  exact ByteArray.size_set! _ _ _

theorem rd8_wr8 {b : ByteArray} {i : ℕ} (hi : i < b.size) (x j : ℕ) :
    rd8 (wr8 b i x) j = if i = j then x % 256 else rd8 b j := by
  unfold wr8
  rw [rd8_eq, rd8_eq, ByteArray.getElem!_set! _ _ _ _ hi]
  split
  · simp
  · rfl

theorem rd8_wr8_self {b : ByteArray} {i : ℕ} (hi : i < b.size) (x : ℕ) :
    rd8 (wr8 b i x) i = x % 256 := by
  rw [rd8_wr8 hi, if_pos rfl]

theorem rd8_wr8_ne {b : ByteArray} {i j : ℕ} (hi : i < b.size) (x : ℕ) (h : i ≠ j) :
    rd8 (wr8 b i x) j = rd8 b j := by
  rw [rd8_wr8 hi, if_neg h]

theorem get!_set!_ne' (b : ByteArray) (i j : ℕ) (v : UInt8) (h : i ≠ j) :
    (b.set! i v).get! j = b.get! j := by
  rw [get!_eq, get!_eq, ByteArray.getElem!_set!_ne _ _ _ _ h]

theorem get!_set!_self' {b : ByteArray} {i : ℕ} (v : UInt8) (h : i < b.size) :
    (b.set! i v).get! i = v := by
  rw [get!_eq, ByteArray.getElem!_set!_self _ _ _ h]

@[simp] theorem size_wr32 (b : ByteArray) (i x : ℕ) : (wr32 b i x).size = b.size := by
  unfold wr32
  simp only [ByteArray.size_set!]

theorem wr32_get_ne (b : ByteArray) (i x m : ℕ) (h0 : 4 * i ≠ m) (h1 : 4 * i + 1 ≠ m)
    (h2 : 4 * i + 2 ≠ m) (h3 : 4 * i + 3 ≠ m) : (wr32 b i x).get! m = b.get! m := by
  unfold wr32
  dsimp only
  rw [get!_set!_ne' _ _ _ _ h3, get!_set!_ne' _ _ _ _ h2, get!_set!_ne' _ _ _ _ h1,
    get!_set!_ne' _ _ _ _ h0]

theorem rd32_wr32_ne (b : ByteArray) {i j : ℕ} (x : ℕ) (h : i ≠ j) :
    rd32 (wr32 b i x) j = rd32 b j := by
  unfold rd32
  dsimp only
  rw [wr32_get_ne _ _ _ _ (by omega) (by omega) (by omega) (by omega),
    wr32_get_ne _ _ _ (4 * j + 1) (by omega) (by omega) (by omega) (by omega),
    wr32_get_ne _ _ _ (4 * j + 2) (by omega) (by omega) (by omega) (by omega),
    wr32_get_ne _ _ _ (4 * j + 3) (by omega) (by omega) (by omega) (by omega)]

theorem bytes_eq {x : ℕ} (hx : x < 2 ^ 32) :
    x % 256 ||| (x >>> 8 % 256) <<< 8 ||| (x >>> 16 % 256) <<< 16 ||| (x >>> 24 % 256) <<< 24 =
      x := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow]
  by_cases h32 : j < 32
  · interval_cases j <;> simp
  · have : x.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hx
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this, show ¬ j < 8 by omega, show ¬ j - 8 < 8 by omega, show ¬ j - 16 < 8 by omega,
      show ¬ j - 24 < 8 by omega]

theorem wr32_get {b : ByteArray} {i : ℕ} (hi : 4 * i + 3 < b.size) (x : ℕ) :
    (wr32 b i x).get! (4 * i) = UInt8.ofNat x ∧
      (wr32 b i x).get! (4 * i + 1) = UInt8.ofNat (x >>> 8) ∧
      (wr32 b i x).get! (4 * i + 2) = UInt8.ofNat (x >>> 16) ∧
      (wr32 b i x).get! (4 * i + 3) = UInt8.ofNat (x >>> 24) := by
  unfold wr32
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [get!_set!_ne' _ _ _ _ (by omega), get!_set!_ne' _ _ _ _ (by omega),
      get!_set!_ne' _ _ _ _ (by omega), get!_set!_self' _ (by omega)]
  · rw [get!_set!_ne' _ _ _ _ (by omega), get!_set!_ne' _ _ _ _ (by omega),
      get!_set!_self' _ (by simp only [ByteArray.size_set!]; omega)]
  · rw [get!_set!_ne' _ _ _ _ (by omega), get!_set!_self' _ (by simp only [ByteArray.size_set!]; omega)]
  · rw [get!_set!_self' _ (by simp only [ByteArray.size_set!]; omega)]

theorem rd32_wr32_self {b : ByteArray} {i : ℕ} (hi : 4 * i + 3 < b.size) {x : ℕ}
    (hx : x < 2 ^ 32) : rd32 (wr32 b i x) i = x := by
  obtain ⟨g0, g1, g2, g3⟩ := wr32_get hi x
  unfold rd32
  dsimp only
  rw [g0, g1, g2, g3]
  simp only [UInt8.toNat_ofNat', show (2 : ℕ) ^ 8 = 256 by norm_num]
  exact bytes_eq hx

theorem zeros_fold : ∀ (l : List ℕ) (b : ByteArray), (∀ i, b.get! i = 0) →
    (l.foldl (fun b _ => b.push 0) b).size = b.size + l.length ∧
      ∀ i, (l.foldl (fun b _ => b.push 0) b).get! i = 0
  | [], b, h => ⟨rfl, h⟩
  | a :: l, b, h => by
    rw [List.foldl_cons]
    have h' : ∀ i, (b.push 0).get! i = 0 := by
      intro i
      rw [get!_eq, ByteArray.getElem!_push]
      split
      · rfl
      · rw [← get!_eq]
        exact h i
    obtain ⟨e1, e2⟩ := zeros_fold l _ h'
    refine ⟨?_, e2⟩
    rw [e1, ByteArray.size_push, List.length_cons]
    omega

theorem range_size (n : ℕ) : [:n].size = n := by
  simp [Std.Legacy.Range.size]

theorem zeros_eq (n : ℕ) :
    zeros n = (List.range' 0 n).foldl (fun b _ => b.push 0) (ByteArray.emptyWithCapacity n) := by
  unfold zeros
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', range_size, bind_pure]
  exact forIn_yield_eq _ _ _ _ fun _ _ => rfl

theorem zeros_spec (n : ℕ) : (zeros n).size = n ∧ ∀ i, rd8 (zeros n) i = 0 := by
  have h0 : ∀ i, (ByteArray.emptyWithCapacity n).get! i = 0 := by
    intro i
    have : (ByteArray.emptyWithCapacity n).size = 0 := rfl
    rw [get!_eq, getElem!_neg _ i (by omega)]
    rfl
  obtain ⟨e1, e2⟩ := zeros_fold (List.range' 0 n) _ h0
  rw [zeros_eq]
  refine ⟨?_, fun i => ?_⟩
  · have : (ByteArray.emptyWithCapacity n).size = 0 := rfl
    rw [e1, List.length_range']
    omega
  · unfold rd8
    rw [e2 i]
    rfl


abbrev IState := ByteArray × ByteArray × ByteArray × Array ℕ

abbrev OState := ByteArray × ByteArray × ByteArray × Array ℕ × ℕ

@[expose] def kInner (F : ℕ → ℕ → ℕ) (v lv : ℕ) (s : IState) (g : ℕ) : IState :=
  if (rd8 s.1 (F g v) == 0) = true then
    (wr8 s.1 (F g v) (lv + 1), wr8 s.2.1 (F g v) g, wr32 s.2.2.1 (F g v) v, s.2.2.2.push (F g v))
  else s

@[expose] def kStep (F : ℕ → ℕ → ℕ) (m : ℕ) (s : OState) : OState :=
  (fun r : IState => (r.1, r.2.1, r.2.2.1, r.2.2.2, s.2.2.2.2 + 1))
    ((List.range' 0 m).foldl (kInner F s.2.2.2.1[s.2.2.2.2]! (rd8 s.1 s.2.2.2.1[s.2.2.2.2]!))
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1))

@[expose] def kInit (N seed : ℕ) : OState :=
  (wr8 (zeros N) seed 1, zeros N, zeros (4 * N), (Array.mkEmpty N).push seed, 0)

@[expose] def kRun (F : ℕ → ℕ → ℕ) (m N seed : ℕ) : OState :=
  (List.range' 0 N).foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s)
    (kInit N seed)

theorem kSearch_eq (tabs : Array (Array ℕ)) (seed : ℕ) :
    kSearch tabs seed = (fun s : OState => (s.1, s.2.1, s.2.2.1, s.2.2.2.1))
      (kRun (fun g v => fastAct tabs[g]! v) tabs.size (1 <<< 24) seed) := by
  unfold kSearch
  dsimp only
  generalize (1 <<< 24 : ℕ) = n
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', range_size]
  rw [forIn_break_eq _ _ _ (fun s : OState => s.2.2.2.2 < s.2.2.2.1.size)
    (kStep (fun g v => fastAct tabs[g]! v) tabs.size)]
  · rfl
  · intro a s
    obtain ⟨lev, lab, par, q, qh⟩ := s
    dsimp only
    split
    · next hq =>
      rw [forIn_yield_eq _ _ _ (kInner (fun g v => fastAct tabs[g]! v) q[qh]! (rd8 lev q[qh]!))]
      · rfl
      · intro g t
        obtain ⟨a1, a2, a3, a4⟩ := t
        dsimp only
        unfold kInner
        split <;> rfl
    · rfl

inductive RIn (F : ℕ → ℕ → ℕ) (m seed : ℕ) : ℕ → ℕ → Prop
  | root : RIn F m seed 0 seed
  | mono {k u : ℕ} : RIn F m seed k u → RIn F m seed (k + 1) u
  | step {k u : ℕ} (g : ℕ) : g < m → RIn F m seed k u → RIn F m seed (k + 1) (F g u)

section Dist

variable {F : ℕ → ℕ → ℕ} {m seed : ℕ}

theorem RIn.reach {k u : ℕ} (h : RIn F m seed k u) : Reach F m seed u := by
  induction h with
  | root => exact Reach.root
  | mono _ ih => exact ih
  | step g hg _ ih => exact Reach.step g hg ih

theorem RIn.le {k u : ℕ} (h : RIn F m seed k u) : ∀ {k'}, k ≤ k' → RIn F m seed k' u := by
  intro k' hk
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this
    exact h
  | succ k' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk' | hk'
    · exact RIn.mono (ih (by omega))
    · rw [← hk']
      exact h

theorem RIn.zero {u : ℕ} (h : RIn F m seed 0 u) : u = seed := by
  cases h
  rfl

open Classical in
noncomputable def kd (F : ℕ → ℕ → ℕ) (m seed u : ℕ) : ℕ :=
  if h : ∃ k, RIn F m seed k u then Nat.find h else 0

theorem kd_spec {u : ℕ} (h : ∃ k, RIn F m seed k u) :
    RIn F m seed (kd F m seed u) u ∧ ∀ k, RIn F m seed k u → kd F m seed u ≤ k := by
  classical
  unfold kd
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact ⟨Nat.find_spec h, fun k hk => Nat.find_min' h hk⟩

theorem kd_seed : kd F m seed seed = 0 :=
  Nat.le_zero.1 ((kd_spec ⟨0, RIn.root⟩).2 0 RIn.root)

theorem kd_eq_zero {u : ℕ} (h : ∃ k, RIn F m seed k u) (h0 : kd F m seed u = 0) : u = seed := by
  have := (kd_spec h).1
  rw [h0] at this
  exact this.zero

theorem kd_step {u g : ℕ} (h : ∃ k, RIn F m seed k u) (hg : g < m) :
    (∃ k, RIn F m seed k (F g u)) ∧ kd F m seed (F g u) ≤ kd F m seed u + 1 := by
  have h1 := RIn.step g hg (kd_spec h).1
  exact ⟨⟨_, h1⟩, (kd_spec ⟨_, h1⟩).2 _ h1⟩

theorem kd_pred {u : ℕ} (h : ∃ k, RIn F m seed k u) (hne : u ≠ seed) :
    ∃ p g, g < m ∧ (∃ k, RIn F m seed k p) ∧ F g p = u ∧ kd F m seed p + 1 = kd F m seed u := by
  obtain ⟨hr, hmin⟩ := kd_spec h
  generalize hk : kd F m seed u = k at hr hmin
  cases k with
  | zero => exact absurd hr.zero hne
  | succ k =>
    cases hr with
    | mono h' => exact absurd (hmin k h') (by omega)
    | step g hg h' =>
      refine ⟨_, g, hg, ⟨k, h'⟩, rfl, ?_⟩
      have h1 := (kd_spec ⟨k, h'⟩).2 k h'
      have h2 := (kd_step (g := g) ⟨k, h'⟩ hg).2
      have h3 := hmin _ (kd_spec (F := F) (m := m) (seed := seed) ⟨_, RIn.step g hg h'⟩).1
      omega

end Dist

section Inv

variable {F : ℕ → ℕ → ℕ} {m seed N : ℕ}

structure Core (F : ℕ → ℕ → ℕ) (m seed N : ℕ) (lev lab par : ByteArray) (q : Array ℕ)
    (P : ℕ → ℕ → Prop) (h : ℕ) : Prop where
  szL : lev.size = N
  szB : lab.size = N
  szP : par.size = 4 * N
  pos : 0 < q.size
  q0 : q[0]! = seed
  hle : h ≤ q.size
  h0 : h = 0 → q.size = 1
  mem : ∀ i < q.size, q[i]! < N ∧ (∃ k, RIn F m seed k q[i]!) ∧
    rd8 lev q[i]! = kd F m seed q[i]! + 1
  found : ∀ v, rd8 lev v ≠ 0 → ∃ i < q.size, q[i]! = v
  nodup : ∀ i j, i < j → j < q.size → q[i]! ≠ q[j]!
  sorted : ∀ i j, i ≤ j → j < q.size → kd F m seed q[i]! ≤ kd F m seed q[j]!
  front : 0 < h → ∀ j < q.size, kd F m seed q[j]! ≤ kd F m seed q[h - 1]! + 1
  closed : ∀ i < q.size, ∀ g < m, P i g → rd8 lev (F g q[i]!) ≠ 0
  tree : ∀ i, 0 < i → i < q.size → rd32 par q[i]! < N ∧ rd8 lab q[i]! < m ∧
    F (rd8 lab q[i]!) (rd32 par q[i]!) = q[i]! ∧ rd8 lev (rd32 par q[i]!) + 1 = rd8 lev q[i]!

theorem Core.found_le {lev lab par : ByteArray} {q : Array ℕ} {P : ℕ → ℕ → Prop} {h : ℕ}
    (C : Core F m seed N lev lab par q P h) (hP : ∀ i, i + 1 < h → ∀ g < m, P i g) (hh : 0 < h) :
    ∀ u, (∃ k, RIn F m seed k u) → kd F m seed u ≤ kd F m seed q[h - 1]! → rd8 lev u ≠ 0 := by
  intro u
  induction hd : kd F m seed u using Nat.strong_induction_on generalizing u with
  | _ d ih =>
    intro hu hle
    by_cases hs : u = seed
    · subst hs
      rw [← C.q0, (C.mem 0 C.pos).2.2]
      omega
    · obtain ⟨p, g, hg, hp, e, hdp⟩ := kd_pred hu hs
      have hlp := ih _ (by omega) p rfl hp (by omega)
      obtain ⟨i, hi, rfl⟩ := C.found p hlp
      have hih : i + 1 < h := by
        by_contra hc
        have := C.sorted (h - 1) i (by omega) hi
        omega
      rw [← e]
      exact C.closed i hi g hg (hP i hih g hg)

end Inv


section Steps

variable {F : ℕ → ℕ → ℕ} {m seed N : ℕ}

@[expose] def PIn (c k i g : ℕ) : Prop := i < c ∨ (i = c ∧ g < k)

theorem kInner_ext (v lv : ℕ) (s : IState) (g : ℕ) :
    s.2.2.2.size ≤ (kInner F v lv s g).2.2.2.size ∧
      ∀ i < s.2.2.2.size, (kInner F v lv s g).2.2.2[i]! = s.2.2.2[i]! := by
  unfold kInner
  split
  · exact ⟨by simp, fun i hi => push_get_lt _ _ hi⟩
  · exact ⟨le_rfl, fun _ _ => rfl⟩

theorem kInner_core (hF : ∀ g < m, ∀ v < N, F g v < N) (hm : m ≤ 256) (hN : N ≤ 2 ^ 32)
    (hD : ∀ u, (∃ k, RIn F m seed k u) → kd F m seed u ≤ 253)
    {lev lab par : ByteArray} {q : Array ℕ} {c k v lv : ℕ}
    (C : Core F m seed N lev lab par q (PIn c k) (c + 1)) (hk : k < m) (hv : q[c]! = v)
    (hlv : lv = kd F m seed v + 1) :
    Core F m seed N (kInner F v lv (lev, lab, par, q) k).1 (kInner F v lv (lev, lab, par, q) k).2.1
      (kInner F v lv (lev, lab, par, q) k).2.2.1 (kInner F v lv (lev, lab, par, q) k).2.2.2
      (PIn c (k + 1)) (c + 1) := by
  have hc : c < q.size := C.hle
  obtain ⟨hvN, hvE, hvl⟩ := C.mem c hc
  rw [hv] at hvN hvE hvl
  have hwN : F k v < N := hF k hk v hvN
  obtain ⟨hwE, hwd⟩ := kd_step hvE hk (F := F) (m := m) (seed := seed)
  unfold kInner
  dsimp only
  by_cases h0 : rd8 lev (F k v) = 0
  · rw [if_pos (by rw [h0]; rfl)]
    have hfl := C.found_le (fun i hi g _ => Or.inl (by omega)) (by omega)
    have hdw : kd F m seed (F k v) = kd F m seed v + 1 := by
      by_contra hne
      have hle : kd F m seed (F k v) ≤ kd F m seed q[c + 1 - 1]! := by
        rw [show c + 1 - 1 = c by omega, hv]
        omega
      exact hfl _ hwE hle h0
    have hvd := hD v hvE
    have hnotin : ∀ i < q.size, q[i]! ≠ F k v := by
      intro i hi e
      have := (C.mem i hi).2.2
      rw [e, h0] at this
      omega
    have hvw : v ≠ F k v := fun e => hnotin c hc (by rw [hv]; exact e)
    have L : ∀ u, rd8 (wr8 lev (F k v) (lv + 1)) u =
        if u = F k v then kd F m seed (F k v) + 1 else rd8 lev u := by
      intro u
      rw [rd8_wr8 (by rw [C.szL]; exact hwN)]
      by_cases e : u = F k v
      · rw [if_pos e.symm, if_pos e, hlv, hdw, Nat.mod_eq_of_lt (by omega)]
      · rw [if_neg (Ne.symm e), if_neg e]
    have Lb : ∀ u, u ≠ F k v → rd8 (wr8 lab (F k v) k) u = rd8 lab u := fun u e =>
      rd8_wr8_ne (by rw [C.szB]; exact hwN) _ (Ne.symm e)
    have Lbw : rd8 (wr8 lab (F k v) k) (F k v) = k := by
      rw [rd8_wr8_self (by rw [C.szB]; exact hwN), Nat.mod_eq_of_lt (by omega)]
    have Pw : rd32 (wr32 par (F k v) v) (F k v) = v :=
      rd32_wr32_self (by rw [C.szP]; omega) (by omega)
    have Pu : ∀ u, u ≠ F k v → rd32 (wr32 par (F k v) v) u = rd32 par u := fun u e =>
      rd32_wr32_ne _ _ (Ne.symm e)
    have Q : ∀ i < q.size, (q.push (F k v))[i]! = q[i]! := fun i hi => push_get_lt _ _ hi
    have Qs : (q.push (F k v))[q.size]! = F k v := push_get_size _ _
    have Sz : (q.push (F k v)).size = q.size + 1 := Array.size_push _
    change Core F m seed N (wr8 lev (F k v) (lv + 1)) (wr8 lab (F k v) k) (wr32 par (F k v) v)
      (q.push (F k v)) (PIn c (k + 1)) (c + 1)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [size_wr8]
      exact C.szL
    · rw [size_wr8]
      exact C.szB
    · rw [size_wr32]
      exact C.szP
    · rw [Sz]
      omega
    · rw [Q 0 C.pos]
      exact C.q0
    · rw [Sz]
      omega
    · intro h
      omega
    · intro i hi
      rw [Sz] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Q i hi]
        obtain ⟨a1, a2, a3⟩ := C.mem i hi
        refine ⟨a1, a2, ?_⟩
        rw [L, if_neg (hnotin i hi)]
        exact a3
      · rw [Qs]
        exact ⟨hwN, hwE, by rw [L, if_pos rfl]⟩
    · intro u hu
      rw [L] at hu
      by_cases e : u = F k v
      · exact ⟨q.size, by omega, by rw [Qs, e]⟩
      · rw [if_neg e] at hu
        obtain ⟨i, hi, rfl⟩ := C.found u hu
        exact ⟨i, by omega, Q i hi⟩
    · intro i j hij hj
      rw [Sz] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [Q i (by omega), Q j hj]
        exact C.nodup i j hij hj
      · rw [Q i hij, Qs]
        exact hnotin i hij
    · intro i j hij hj
      rw [Sz] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [Q i (by omega), Q j hj]
        exact C.sorted i j hij hj
      · rw [Qs]
        rcases Nat.lt_or_ge i q.size with hi | hi
        · rw [Q i hi]
          have := C.front (by omega) i hi
          rw [show c + 1 - 1 = c by omega, hv] at this
          omega
        · rw [show i = q.size by omega, Qs]
    · intro _ j hj
      rw [Sz] at hj
      rw [show c + 1 - 1 = c by omega, Q c hc, hv]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [Q j hj]
        have := C.front (by omega) j hj
        rwa [show c + 1 - 1 = c by omega, hv] at this
      · rw [Qs]
        omega
    · intro i hi g hg hP
      rw [Sz] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Q i hi, L]
        split
        · omega
        · next e =>
          rcases hP with hP | ⟨rfl, hg'⟩
          · exact C.closed i hi g hg (Or.inl hP)
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hg' with hg' | rfl
            · exact C.closed i hi g hg (Or.inr ⟨rfl, hg'⟩)
            · exact absurd (by rw [hv]) e
      · rcases hP with hP | ⟨hP, -⟩ <;> omega
    · intro i hi0 hi
      rw [Sz] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Q i hi]
        obtain ⟨t1, t2, t3, t4⟩ := C.tree i hi0 hi
        have hiw := hnotin i hi
        have hpw : rd32 par q[i]! ≠ F k v := by
          intro e
          rw [e, h0] at t4
          have hkd : kd F m seed q[i]! = 0 := by
            rw [(C.mem i hi).2.2] at t4
            omega
          exact C.nodup 0 i hi0 hi (by rw [C.q0, kd_eq_zero (C.mem i hi).2.1 hkd])
        rw [Pu _ hiw, Lb _ hiw, L, if_neg hpw, L, if_neg hiw]
        exact ⟨t1, t2, t3, t4⟩
      · rw [Qs, Pw, Lbw, L, if_neg hvw, L, if_pos rfl, hvl, hdw]
        exact ⟨hvN, hk, rfl, rfl⟩
  · rw [if_neg (by rw [beq_iff_eq]; exact h0)]
    exact { C with
      closed := fun i hi g hg hP => by
        rcases hP with hP | ⟨rfl, hg'⟩
        · exact C.closed i hi g hg (Or.inl hP)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hg' with hg' | rfl
          · exact C.closed i hi g hg (Or.inr ⟨rfl, hg'⟩)
          · rw [hv]
            exact h0 }

theorem kInner_fold (hF : ∀ g < m, ∀ v < N, F g v < N) (hm : m ≤ 256) (hN : N ≤ 2 ^ 32)
    (hD : ∀ u, (∃ k, RIn F m seed k u) → kd F m seed u ≤ 253)
    {lev lab par : ByteArray} {q : Array ℕ} {c v lv : ℕ}
    (C : Core F m seed N lev lab par q (PIn c 0) (c + 1)) (hv : q[c]! = v)
    (hlv : lv = kd F m seed v + 1) : ∀ k ≤ m,
    Core F m seed N ((List.range' 0 k).foldl (kInner F v lv) (lev, lab, par, q)).1
      ((List.range' 0 k).foldl (kInner F v lv) (lev, lab, par, q)).2.1
      ((List.range' 0 k).foldl (kInner F v lv) (lev, lab, par, q)).2.2.1
      ((List.range' 0 k).foldl (kInner F v lv) (lev, lab, par, q)).2.2.2 (PIn c k) (c + 1) ∧
    ((List.range' 0 k).foldl (kInner F v lv) (lev, lab, par, q)).2.2.2[c]! = v := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨C, hv⟩
  | succ k ih =>
    intro hk
    obtain ⟨C', hv'⟩ := ih (by omega)
    rw [← List.range_eq_range', List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.range_eq_range']
    generalize (List.range' 0 k).foldl (kInner F v lv) (lev, lab, par, q) = t at C' hv'
    obtain ⟨a1, a2, a3, a4⟩ := t
    refine ⟨kInner_core hF hm hN hD C' (by omega) hv' hlv, ?_⟩
    have hc : c < a4.size := C'.hle
    rw [(kInner_ext v lv (a1, a2, a3, a4) k).2 c hc]
    exact hv'

theorem kStep_core (hF : ∀ g < m, ∀ v < N, F g v < N) (hm : m ≤ 256) (hN : N ≤ 2 ^ 32)
    (hD : ∀ u, (∃ k, RIn F m seed k u) → kd F m seed u ≤ 253)
    {lev lab par : ByteArray} {q : Array ℕ} {qh : ℕ}
    (C : Core F m seed N lev lab par q (fun i _ => i < qh) qh) (hq : qh < q.size) :
    Core F m seed N (kStep F m (lev, lab, par, q, qh)).1 (kStep F m (lev, lab, par, q, qh)).2.1
      (kStep F m (lev, lab, par, q, qh)).2.2.1 (kStep F m (lev, lab, par, q, qh)).2.2.2.1
      (fun i _ => i < (kStep F m (lev, lab, par, q, qh)).2.2.2.2)
      (kStep F m (lev, lab, par, q, qh)).2.2.2.2 := by
  have C0 : Core F m seed N lev lab par q (PIn qh 0) (qh + 1) :=
    { C with
      hle := hq
      h0 := fun h => absurd h (by omega)
      front := fun _ j hj => by
        rw [show qh + 1 - 1 = qh by omega]
        by_cases hq0 : qh = 0
        · subst hq0
          have := C.h0 rfl
          rw [show j = 0 by omega]
          omega
        · have h1 := C.front (by omega) j hj
          have h2 := C.sorted (qh - 1) qh (by omega) hq
          omega
      closed := fun i hi g hg hP => by
        rcases hP with hP | ⟨-, hg0⟩
        · exact C.closed i hi g hg hP
        · omega }
  obtain ⟨F1, -⟩ := kInner_fold hF hm hN hD C0 rfl (C.mem qh hq).2.2 m le_rfl
  unfold kStep
  dsimp only
  exact { F1 with
    closed := fun i hi g hg hP => F1.closed i hi g hg (by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hP with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hg⟩) }

theorem Core.size_le {lev lab par : ByteArray} {q : Array ℕ} {P : ℕ → ℕ → Prop} {h : ℕ}
    (C : Core F m seed N lev lab par q P h) {S : Finset ℕ}
    (hS : ∀ u, (∃ k, RIn F m seed k u) → u ∈ S) : q.size ≤ S.card := by
  have := Finset.card_le_card_of_injOn (s := Finset.range q.size) (t := S) (fun i => q[i]!)
    (fun i hi => hS _ (C.mem i (Finset.mem_range.1 hi)).2.1)
    (fun a ha b hb e => by
      have ha' := Finset.mem_range.1 ha
      have hb' := Finset.mem_range.1 hb
      rcases lt_trichotomy a b with hab | rfl | hab
      · exact absurd e (C.nodup a b hab hb')
      · rfl
      · exact absurd e.symm (C.nodup b a hab ha'))
  rwa [Finset.card_range] at this

theorem kRun_fold (hF : ∀ g < m, ∀ v < N, F g v < N) (hm : m ≤ 256) (hN : N ≤ 2 ^ 32)
    (hD : ∀ u, (∃ k, RIn F m seed k u) → kd F m seed u ≤ 253) :
    ∀ (l : List ℕ) (s : OState) (t : ℕ),
      Core F m seed N s.1 s.2.1 s.2.2.1 s.2.2.2.1 (fun i _ => i < s.2.2.2.2) s.2.2.2.2 →
      (s.2.2.2.2 = s.2.2.2.1.size ∨ t ≤ s.2.2.2.2) →
      Core F m seed N
          (l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).1
          (l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).2.1
          (l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).2.2.1
          (l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).2.2.2.1
          (fun i _ => i <
            (l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).2.2.2.2)
          (l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).2.2.2.2 ∧
      ((l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).2.2.2.2 =
          (l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).2.2.2.1.size ∨
        t + l.length ≤
          (l.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then kStep F m s else s) s).2.2.2.2)
  | [], _, _, C, h => ⟨C, by simpa using h⟩
  | a :: l, s, t, C, h => by
    rw [List.foldl_cons]
    obtain ⟨lev, lab, par, q, qh⟩ := s
    dsimp only at C h ⊢
    by_cases hq : qh < q.size
    · rw [if_pos hq]
      have C' := kStep_core hF hm hN hD C hq
      have e : (kStep F m (lev, lab, par, q, qh)).2.2.2.2 = qh + 1 := rfl
      have := kRun_fold hF hm hN hD l _ (t + 1) C' (Or.inr (by rw [e]; omega))
      rw [List.length_cons, show t + (l.length + 1) = t + 1 + l.length by omega]
      exact this
    · rw [if_neg hq]
      have idle : ∀ l' : List ℕ, l'.foldl (fun s _ => if s.2.2.2.2 < s.2.2.2.1.size then
          kStep F m s else s) (lev, lab, par, q, qh) = (lev, lab, par, q, qh) := by
        intro l'
        induction l' with
        | nil => rfl
        | cons b l' ih =>
          rw [List.foldl_cons, if_neg hq]
          exact ih
      rw [idle l]
      refine ⟨C, Or.inl ?_⟩
      change qh = q.size
      have := C.hle
      omega

end Steps


section Spec

variable {F : ℕ → ℕ → ℕ} {m seed N : ℕ}

theorem core_init (hseed : seed < N) :
    Core F m seed N (kInit N seed).1 (kInit N seed).2.1 (kInit N seed).2.2.1 (kInit N seed).2.2.2.1
      (fun i _ => i < (kInit N seed).2.2.2.2) (kInit N seed).2.2.2.2 := by
  obtain ⟨z1, z2⟩ := zeros_spec N
  obtain ⟨z3, z4⟩ := zeros_spec (4 * N)
  have L : ∀ u, rd8 (wr8 (zeros N) seed 1) u = if u = seed then 1 else 0 := by
    intro u
    rw [rd8_wr8 (by rw [z1]; exact hseed)]
    by_cases e : u = seed
    · rw [if_pos e.symm, if_pos e]
    · rw [if_neg (Ne.symm e), if_neg e, z2]
  have Q : ((Array.mkEmpty N).push seed : Array ℕ) = #[seed] := rfl
  change Core F m seed N (wr8 (zeros N) seed 1) (zeros N) (zeros (4 * N)) #[seed]
    (fun i _ => i < 0) 0
  refine ⟨by rw [size_wr8, z1], z1, z3, by simp, rfl, by simp, fun _ => rfl, ?_, ?_, ?_, ?_,
    fun h => absurd h (by omega), fun _ _ _ _ h => absurd h (by omega), ?_⟩
  · intro i hi
    have : i = 0 := by simpa using hi
    subst this
    refine ⟨hseed, ⟨0, RIn.root⟩, ?_⟩
    change rd8 (wr8 (zeros N) seed 1) seed = kd F m seed seed + 1
    rw [L, if_pos rfl, kd_seed]
  · intro u hu
    rw [L] at hu
    by_cases e : u = seed
    · exact ⟨0, by simp, by rw [e]; rfl⟩
    · rw [if_neg e] at hu
      exact absurd rfl hu
  · intro i j hij hj
    simp at hj
    omega
  · intro i j hij hj
    have : j = 0 := by simpa using hj
    subst this
    rw [show i = 0 by omega]
  · intro i hi0 hi
    simp at hi
    omega

theorem kRun_spec (hseed : seed < N) (hF : ∀ g < m, ∀ v < N, F g v < N) (hm : m ≤ 256)
    (hN : N ≤ 2 ^ 32) (hS : ∃ S : Finset ℕ, (∀ u, Reach F m seed u → u ∈ S) ∧ S.card ≤ N)
    (hD : ∀ u, Reach F m seed u → RIn F m seed 253 u) :
    (kRun F m N seed).1.size = N ∧
      (∀ u, rd8 (kRun F m N seed).1 u ≠ 0 ↔ Reach F m seed u) ∧
      (∀ u, Reach F m seed u → (rd8 (kRun F m N seed).1 u = 1 ↔ u = seed)) ∧
      (∀ u, Reach F m seed u → u ≠ seed →
        rd32 (kRun F m N seed).2.2.1 u < N ∧ rd8 (kRun F m N seed).2.1 u < m ∧
        F (rd8 (kRun F m N seed).2.1 u) (rd32 (kRun F m N seed).2.2.1 u) = u ∧
        rd8 (kRun F m N seed).1 (rd32 (kRun F m N seed).2.2.1 u) + 1 =
          rd8 (kRun F m N seed).1 u) := by
  have hD' : ∀ u, (∃ k, RIn F m seed k u) → kd F m seed u ≤ 253 := by
    rintro u ⟨k, hk⟩
    exact (kd_spec ⟨k, hk⟩).2 253 (hD u hk.reach)
  obtain ⟨S, hS1, hS2⟩ := hS
  obtain ⟨Cf, hfin⟩ := kRun_fold hF hm hN hD' (List.range' 0 N) (kInit N seed) 0
    (core_init hseed) (Or.inr le_rfl)
  rw [List.length_range', Nat.zero_add] at hfin
  change Core F m seed N (kRun F m N seed).1 (kRun F m N seed).2.1 (kRun F m N seed).2.2.1
    (kRun F m N seed).2.2.2.1 (fun i _ => i < (kRun F m N seed).2.2.2.2)
    (kRun F m N seed).2.2.2.2 at Cf
  change (kRun F m N seed).2.2.2.2 = (kRun F m N seed).2.2.2.1.size ∨
    N ≤ (kRun F m N seed).2.2.2.2 at hfin
  generalize kRun F m N seed = r at Cf hfin ⊢
  obtain ⟨lev, lab, par, q, qh⟩ := r
  dsimp only at Cf hfin ⊢
  have hsz := Cf.size_le (S := S) fun u ⟨k, hk⟩ => hS1 u hk.reach
  have hqh : qh = q.size := by
    rcases hfin with h | h
    · exact h
    · have := Cf.hle
      omega
  have hall : ∀ u, Reach F m seed u → ∃ i < q.size, q[i]! = u := by
    intro u hu
    induction hu with
    | root => exact ⟨0, Cf.pos, Cf.q0⟩
    | step g hg _ ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      exact Cf.found _ (Cf.closed i hi g hg (by omega))
  refine ⟨Cf.szL, fun u => ⟨fun h => ?_, fun h => ?_⟩, fun u hu => ?_, fun u hu hne => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Cf.found u h
    obtain ⟨k, hk⟩ := (Cf.mem i hi).2.1
    exact hk.reach
  · obtain ⟨i, hi, rfl⟩ := hall u h
    rw [(Cf.mem i hi).2.2]
    omega
  · obtain ⟨i, hi, rfl⟩ := hall u hu
    rw [(Cf.mem i hi).2.2]
    constructor
    · intro h
      exact kd_eq_zero (Cf.mem i hi).2.1 (by omega)
    · intro h
      rw [h, kd_seed]
  · obtain ⟨i, hi, rfl⟩ := hall u hu
    have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h, Cf.q0] at hne
        exact absurd rfl hne
      · exact h
    exact Cf.tree i hi0 hi

end Spec


section Fast

theorem actGo_acc (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, actGo rows v n acc = acc ^^^ actGo rows v n 0
  | 0, acc => by simp [actGo]
  | n + 1, acc => by
    rw [actGo, actGo, actGo_acc rows v n, actGo_acc rows v n (if v.testBit n then 0 ^^^ rows[n]! else 0)]
    split <;> simp [Nat.xor_assoc]

theorem actGo_xor (rows : Array ℕ) (a b : ℕ) :
    ∀ n, actGo rows (a ^^^ b) n 0 = actGo rows a n 0 ^^^ actGo rows b n 0
  | 0 => by simp [actGo]
  | n + 1 => by
    rw [actGo, actGo, actGo, actGo_acc, actGo_acc rows a n, actGo_acc rows b n, actGo_xor rows a b n,
      Nat.testBit_xor]
    cases a.testBit n <;> cases b.testBit n <;> simp <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      simp only [Nat.testBit_xor] <;> cases (actGo rows a n 0).testBit j <;>
      cases (actGo rows b n 0).testBit j <;> cases rows[n]!.testBit j <;> rfl

theorem actRows_xor (rows : Array ℕ) (a b : ℕ) :
    actRows rows (a ^^^ b) = actRows rows a ^^^ actRows rows b := actGo_xor rows a b 24

theorem push_fold {α : Type} [Inhabited α] (f : ℕ → α) : ∀ (k : ℕ) (t : Array α),
    ((List.range' 0 k).foldl (fun t x => t.push (f x)) t).size = t.size + k ∧
      (∀ i < t.size, ((List.range' 0 k).foldl (fun t x => t.push (f x)) t)[i]! = t[i]!) ∧
      ∀ x < k, ((List.range' 0 k).foldl (fun t x => t.push (f x)) t)[t.size + x]! = f x := by
  intro k
  induction k with
  | zero => intro t; exact ⟨rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro t
    rw [← List.range_eq_range', List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.range_eq_range']
    obtain ⟨h1, h2, h3⟩ := ih t
    refine ⟨by rw [Array.size_push, h1]; omega, fun i hi => ?_, fun x hx => ?_⟩
    · rw [push_get_lt _ _ (by omega), h2 i hi]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
      · rw [push_get_lt _ _ (by omega), h3 x hx]
      · rw [← h1, push_get_size]

theorem fastTables_eq (rows : Array ℕ) :
    fastTables rows = (List.range' 0 3).foldl (fun t b => (List.range' 0 256).foldl
      (fun t x => t.push (actRows rows (x <<< (8 * b)))) t) (Array.mkEmpty 768) := by
  unfold fastTables
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', range_size, bind_pure]
  refine forIn_yield_eq _ _ _ _ fun b t => ?_
  rw [forIn_yield_eq _ _ _ (fun t x => t.push (actRows rows (x <<< (8 * b))))]
  · rfl
  · intro _ _
    rfl

theorem fastTables_spec (rows : Array ℕ) :
    ∀ b < 3, ∀ x < 256, (fastTables rows)[256 * b + x]! = actRows rows (x <<< (8 * b)) := by
  have H : ∀ k ≤ 3, ((List.range' 0 k).foldl (fun t b => (List.range' 0 256).foldl
      (fun t x => t.push (actRows rows (x <<< (8 * b)))) t) (Array.mkEmpty 768 : Array ℕ)).size =
        256 * k ∧ ∀ b < k, ∀ x < 256, ((List.range' 0 k).foldl (fun t b => (List.range' 0 256).foldl
      (fun t x => t.push (actRows rows (x <<< (8 * b)))) t) (Array.mkEmpty 768 : Array ℕ))[256 * b + x]! =
        actRows rows (x <<< (8 * b)) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range'_concat (n := k), List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.one_mul, Nat.zero_add]
      generalize (List.range' 0 k).foldl (fun t b => (List.range' 0 256).foldl
        (fun t x => t.push (actRows rows (x <<< (8 * b)))) t) (Array.mkEmpty 768 : Array ℕ) = t at h1 h2
      obtain ⟨g1, g2, g3⟩ := push_fold (fun x => actRows rows (x <<< (8 * k))) 256 t
      refine ⟨by rw [g1, h1]; omega, fun b hb x hx => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · rw [g2 _ (by rw [h1]; omega), h2 b hb x hx]
      · rw [← h1, g3 x hx]
  intro b hb x hx
  rw [fastTables_eq]
  exact (H 3 le_rfl).2 b hb x hx

theorem bytes3 {v : ℕ} (hv : v < 2 ^ 24) :
    (v &&& 255) ^^^ (((v >>> 8) &&& 255) <<< 8) ^^^ (((v >>> 16) &&& 255) <<< 16) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  by_cases h : j < 24
  · interval_cases j <;> simp
  · have : v.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h8 : ∀ a, (v.testBit (a + j) && decide (j < 8)) = false := fun a => by simp; omega
    simp only [this, show ¬ j < 8 by omega, decide_false, Bool.and_false, Bool.false_xor]
    by_cases h8' : 8 ≤ j
    · by_cases h16 : 16 ≤ j
      · simp [h8', h16, show ¬ j - 8 < 8 by omega, show ¬ j - 16 < 8 by omega]
      · omega
    · omega

theorem fastAct_fastTables (rows : Array ℕ) {v : ℕ} (hv : v < 2 ^ 24) :
    fastAct (fastTables rows) v = actRows rows v := by
  unfold fastAct
  have e0 := fastTables_spec rows 0 (by norm_num) (v &&& 255) (by
    have := Nat.and_le_right (n := v) (m := 255); omega)
  have e1 := fastTables_spec rows 1 (by norm_num) ((v >>> 8) &&& 255) (by
    have := Nat.and_le_right (n := v >>> 8) (m := 255); omega)
  have e2 := fastTables_spec rows 2 (by norm_num) ((v >>> 16) &&& 255) (by
    have := Nat.and_le_right (n := v >>> 16) (m := 255); omega)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.shiftLeft_zero, Nat.mul_one] at e0 e1 e2
  rw [e0, e1, e2, ← actRows_xor, ← actRows_xor, bytes3 hv]

end Fast

section Congr

variable {F G : ℕ → ℕ → ℕ} {m N seed : ℕ}

theorem reach_congr (hseed : seed < N) (hG : ∀ g < m, ∀ v < N, G g v < N)
    (hFG : ∀ g < m, ∀ v < N, F g v = G g v) (u : ℕ) : Reach F m seed u ↔ Reach G m seed u := by
  constructor
  · intro h
    suffices u < N ∧ Reach G m seed u from this.2
    induction h with
    | root => exact ⟨hseed, Reach.root⟩
    | step g hg _ ih => rw [hFG g hg _ ih.1]; exact ⟨hG g hg _ ih.1, Reach.step g hg ih.2⟩
  · intro h
    suffices u < N ∧ Reach F m seed u from this.2
    induction h with
    | root => exact ⟨hseed, Reach.root⟩
    | step g hg _ ih =>
      refine ⟨hG g hg _ ih.1, ?_⟩
      rw [← hFG g hg _ ih.1]
      exact Reach.step g hg ih.2

theorem rin_congr (hseed : seed < N) (hG : ∀ g < m, ∀ v < N, G g v < N)
    (hFG : ∀ g < m, ∀ v < N, F g v = G g v) {k u : ℕ} (h : RIn G m seed k u) : RIn F m seed k u := by
  suffices u < N ∧ RIn F m seed k u from this.2
  induction h with
  | root => exact ⟨hseed, RIn.root⟩
  | mono _ ih => exact ⟨ih.1, ih.2.mono⟩
  | step g hg _ ih =>
    refine ⟨hG g hg _ ih.1, ?_⟩
    rw [← hFG g hg _ ih.1]
    exact RIn.step g hg ih.2

end Congr

end CFSG.KC.KSearch

end
