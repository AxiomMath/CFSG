module

public import Certificates.Data.CFSGNative.Recognition.HSPinnedData
public import CFSG.Certificates.Kernel.Spor.BfsReplay

public section

namespace CFSG.KC.HSPinnedBfs

open CFSG.Sporadic.Recognition.HSPinned.Native CFSG.Sporadic.Th.Native CFSG.KS.BfsReplay

@[expose] def img (A : Array Nat) (v : Nat) : Nat := pairCode A[v / 100]! A[v % 100]!

abbrev PSt := Array Nat × Array Nat × Array Nat × Array Nat × Array Nat × Array Nat

@[expose] def pIns {β : Type} (q h l : Nat) (pos pts par lab : Array Nat)
    (k : Array Nat → Array Nat → Array Nat → Array Nat → β) : β :=
  if (pos[q]! == 10000) = true then k (pos.set! q pts.size) (pts.push q) (par.push h) (lab.push l)
  else k pos pts par lab

@[expose] def pBody (A B : Array Nat) (h : Nat) (s : PSt) : Id (ForInStep PSt) :=
  if h < s.2.1.size then
    pIns (img A s.2.1[h]!) h 1 s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 fun pos pts par lab =>
      pIns (img B s.2.1[h]!) h 2 pos pts par lab fun pos' pts' par' lab' =>
        pure (.yield (pos', pts', s.2.2.1.push pos[img A s.2.1[h]!]!,
          s.2.2.2.1.push pos'[img B s.2.1[h]!]!, par', lab'))
  else pure (.done s)

@[expose] def pInit (root : Nat) : PSt :=
  ((Array.replicate 10000 10000).set! root 0, #[root], #[], #[], #[0], #[0])

theorem pairBFS_eq_bind (A B : Array Nat) (root : Nat) :
    pairBFS A B root =
      (do
        let s ← forIn (List.range' 0 10000) (pInit root) (pBody A B)
        pure (⟨s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2, s.1⟩ : POrbit) : Id POrbit) := by
  unfold pairBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Id.run]
  congr 1

theorem pairBFS_eq (A B : Array Nat) (root : Nat) :
    pairBFS A B root =
      ⟨(forIn (List.range' 0 10000) (pInit root) (pBody A B) : Id PSt).2.1,
        (forIn (List.range' 0 10000) (pInit root) (pBody A B) : Id PSt).2.2.1,
        (forIn (List.range' 0 10000) (pInit root) (pBody A B) : Id PSt).2.2.2.1,
        (forIn (List.range' 0 10000) (pInit root) (pBody A B) : Id PSt).2.2.2.2.1,
        (forIn (List.range' 0 10000) (pInit root) (pBody A B) : Id PSt).2.2.2.2.2,
        (forIn (List.range' 0 10000) (pInit root) (pBody A B) : Id PSt).1⟩ := by
  rw [pairBFS_eq_bind]
  rfl

theorem pIns_eq {β : Type} (q h l : Nat) (pos pts par lab : Array Nat)
    (k : Array Nat → Array Nat → Array Nat → Array Nat → β) :
    pIns q h l pos pts par lab k =
      k (if (pos[q]! == 10000) = true then pos.set! q pts.size else pos)
        (if (pos[q]! == 10000) = true then pts.push q else pts)
        (if (pos[q]! == 10000) = true then par.push h else par)
        (if (pos[q]! == 10000) = true then lab.push l else lab) := by
  unfold pIns
  split <;> rfl

theorem rangeArr_get {p : Nat → Nat} {m y : Nat} (hy : y < m) :
    ((List.range m).map p).toArray[y]! = p y := by
  rw [getElem!_pos _ y (by simpa using hy)]
  simp

theorem rangeArr_size (p : Nat → Nat) (m : Nat) : ((List.range m).map p).toArray.size = m := by
  simp

theorem rangeArr_push (p : Nat → Nat) (m : Nat) :
    (((List.range m).map p).toArray).push (p m) = ((List.range (m + 1)).map p).toArray := by
  rw [List.range_succ, List.map_append]
  simp

theorem ext_rangeArr {a : Array Nat} {N : Nat} {f : Nat → Nat} (hs : a.size = N)
    (hf : ∀ v < N, a[v]! = f v) : a = ((List.range N).map f).toArray := by
  apply Array.ext
  · rw [hs, rangeArr_size]
  · intro v h1 h2
    rw [← getElem!_pos a v h1, ← getElem!_pos _ v h2, rangeArr_get (by omega), hf v (by omega)]

theorem allIn_congr {lo hi : Nat} {f g : Nat → Bool} (h : ∀ i, lo ≤ i → i < hi → f i = g i) :
    allIn lo hi f = allIn lo hi g := by
  unfold allIn
  congr 1
  funext k hk
  exact h _ (by omega) (by omega)

theorem allIn_iff' {lo hi : Nat} {f : Nat → Bool} :
    allIn lo hi f = true ↔ ∀ i, lo ≤ i → i < hi → f i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i h1 h2
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' h1] using this
  · intro h ⟨k, hk⟩ _
    exact h (lo + k) (by omega) (by omega)

@[expose] def foOf (pr lb : Nat → Nat) (y : Nat) : Nat := 2 * pr y + lb y - 1

theorem fo_mono' {n : Nat} {fo : Nat → Nat} (h : ∀ y, 1 ≤ y → y + 1 < n → fo y < fo (y + 1)) :
    ∀ y z, 1 ≤ y → y < z → z < n → fo y < fo z := by
  intro y z hy hyz hz
  induction z with
  | zero => omega
  | succ z ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hyz with h1 | h1
    · exact Nat.lt_trans (ih h1 (by omega)) (h z (by omega) hz)
    · subst h1
      exact h y hy hz

structure PInv (n : Nat) (p pr lb fo : Nat → Nat) (k m : Nat) (pos pts par lab : Array Nat) :
    Prop where
  pts_eq : pts = ((List.range m).map p).toArray
  par_eq : par = ((List.range m).map pr).toArray
  lab_eq : lab = ((List.range m).map lb).toArray
  m_pos : 1 ≤ m
  m_le : m ≤ n
  disc : ∀ y, 1 ≤ y → y < n → (y < m ↔ fo y < k)
  size : pos.size = 10000
  hit : ∀ y < m, pos[p y]! = y
  miss : ∀ v < 10000, (∀ y < m, p y ≠ v) → pos[v]! = 10000

theorem ins_step {n k m h l x : Nat} {p pr lb fo : Nat → Nat} {pos pts par lab : Array Nat}
    (hlt : ∀ y < n, p y < 10000) (hinj : ∀ i < n, ∀ j < n, p i = p j → i = j)
    (hmono : ∀ y z, 1 ≤ y → y < z → z < n → fo y < fo z)
    (H : PInv n p pr lb fo k m pos pts par lab) (hx : x < n) (hn : n ≤ 10000)
    (hnew : ∀ y, 1 ≤ y → y < n → fo y = k → y = x) (hrd : x = 0 ∨ fo x ≤ k)
    (hpl : 1 ≤ x → fo x = k → pr x = h ∧ lb x = l) :
    ∃ m', PInv n p pr lb fo (k + 1) m'
        (if (pos[p x]! == 10000) = true then pos.set! (p x) pts.size else pos)
        (if (pos[p x]! == 10000) = true then pts.push (p x) else pts)
        (if (pos[p x]! == 10000) = true then par.push h else par)
        (if (pos[p x]! == 10000) = true then lab.push l else lab) ∧
      (if (pos[p x]! == 10000) = true then pos.set! (p x) pts.size else pos)[p x]! = x := by
  have hsz : pts.size = m := by rw [H.pts_eq, rangeArr_size]
  by_cases hc : x < m
  · have hget := H.hit x hc
    have hne : (pos[p x]! == 10000) = false := by
      rw [hget]
      exact beq_false_of_ne (by have := H.m_le; omega)
    rw [hne]
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨m, ⟨H.pts_eq, H.par_eq, H.lab_eq, H.m_pos, H.m_le, fun y hy1 hyn => ?_, H.size, H.hit,
      H.miss⟩, hget⟩
    rw [H.disc y hy1 hyn]
    constructor
    · intro e
      omega
    · intro e
      rcases Nat.lt_succ_iff_lt_or_eq.1 e with e1 | e1
      · exact e1
      · have := hnew y hy1 hyn e1
        subst this
        exact absurd ((H.disc y hy1 hyn).1 hc) (by omega)
  · have hx0 : x ≠ 0 := by have := H.m_pos; omega
    have hfx : fo x = k := by
      rcases hrd with e | e
      · exact absurd e hx0
      · have : ¬ fo x < k := fun e' => hc ((H.disc x (by omega) hx).2 e')
        omega
    have hxm : x = m := by
      refine Classical.byContradiction fun hne => ?_
      have hmx : m < x := by omega
      have h1 := hmono m x H.m_pos hmx hx
      have h2 : ¬ fo m < k := fun e' => Nat.lt_irrefl m ((H.disc m H.m_pos (by omega)).2 e')
      omega
    obtain ⟨hpx, hlx⟩ := hpl (by omega) hfx
    subst hxm
    have hmiss : pos[p x]! = 10000 :=
      H.miss (p x) (hlt x hx) fun y hy e => by
        have := hinj y (by omega) x hx e
        omega
    have hcond : (pos[p x]! == 10000) = true := by rw [hmiss]; rfl
    rw [hcond]
    simp only [ite_true]
    have hself : (pos.set! (p x) pts.size)[p x]! = x := by
      rw [Array.getElem!_set!_self _ _ _ (by rw [H.size]; exact hlt x hx), hsz]
    refine ⟨x + 1, ⟨?_, ?_, ?_, by omega, by omega, fun y hy1 hyn => ?_,
      by rw [Array.size_set!, H.size], fun y hy => ?_, fun v hv hall => ?_⟩, hself⟩
    · rw [H.pts_eq, rangeArr_push]
    · rw [H.par_eq, ← hpx, rangeArr_push]
    · rw [H.lab_eq, ← hlx, rangeArr_push]
    · constructor
      · intro e
        rcases Nat.lt_succ_iff_lt_or_eq.1 e with e1 | e1
        · have := (H.disc y hy1 hyn).1 e1
          omega
        · subst e1
          omega
      · intro e
        refine Classical.byContradiction fun hge => ?_
        have := hmono x y (by omega) (by omega) hyn
        omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hy with e1 | e1
      · have hne : p x ≠ p y := fun e => by
          have := hinj x hx y (by omega) e
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ hne]
        exact H.hit y e1
      · subst e1
        exact hself
    · have hne : p x ≠ v := hall x (Nat.lt_succ_self x)
      rw [Array.getElem!_set!_ne _ _ _ _ hne]
      exact H.miss v hv fun y hy => hall y (by omega)

structure PairData (A B : Array Nat) (n : Nat) (p a b pr lb ps : Nat → Nat) : Prop where
  n_pos : 0 < n
  n_le : n ≤ 10000
  p_lt : ∀ y < n, p y < 10000
  a_lt : ∀ y < n, a y < n
  b_lt : ∀ y < n, b y < n
  img_a : ∀ y < n, img A (p y) = p (a y)
  img_b : ∀ y < n, img B (p y) = p (b y)
  ps_hit : ∀ y < n, ps (p y) = y
  ps_miss : ∀ v < 10000, (∀ y < n, p y ≠ v) → ps v = 10000
  pr_zero : pr 0 = 0
  lb_zero : lb 0 = 0
  tree : ∀ y, 1 ≤ y → y < n →
    pr y < y ∧ ((lb y = 1 ∧ a (pr y) = y) ∨ (lb y = 2 ∧ b (pr y) = y))
  order : ∀ y, 1 ≤ y → y + 1 < n → LexLt (pr y) (lb y) (pr (y + 1)) (lb (y + 1))
  ready_a : ∀ y < n, a y = 0 ∨ ¬ LexLt y 1 (pr (a y)) (lb (a y))
  ready_b : ∀ y < n, b y = 0 ∨ ¬ LexLt y 2 (pr (b y)) (lb (b y))

theorem pairBFS_sim {A B : Array Nat} {n : Nat} {p a b pr lb ps : Nat → Nat}
    (D : PairData A B n p a b pr lb ps) :
    pairBFS A B (p 0) = ⟨((List.range n).map p).toArray, ((List.range n).map a).toArray,
      ((List.range n).map b).toArray, ((List.range n).map pr).toArray,
      ((List.range n).map lb).toArray, ((List.range 10000).map ps).toArray⟩ := by
  obtain ⟨hn0, hn, hlt, ha, hb, hA, hB, hhit, hmiss, hpr0, hlb0, htree, horder, hrdA, hrdB⟩ := D
  have key : ∀ y, 1 ≤ y → y < n → pr y < y ∧
      ((foOf pr lb y = 2 * pr y ∧ lb y = 1 ∧ a (pr y) = y) ∨
        (foOf pr lb y = 2 * pr y + 1 ∧ lb y = 2 ∧ b (pr y) = y)) := by
    intro y h1 h2
    obtain ⟨e0, e | e⟩ := htree y h1 h2
    · refine ⟨e0, Or.inl ⟨?_, e⟩⟩
      unfold foOf
      omega
    · refine ⟨e0, Or.inr ⟨?_, e⟩⟩
      unfold foOf
      omega
  have hinj : ∀ i < n, ∀ j < n, p i = p j → i = j := fun i hi j hj e => by
    rw [← hhit i hi, ← hhit j hj, e]
  have hfo1 : ∀ y, 1 ≤ y → y + 1 < n → foOf pr lb y < foOf pr lb (y + 1) := fun y h1 h2 => by
    have e1 := horder y h1 h2
    have e2 := key y h1 (by omega)
    have e3 := key (y + 1) (by omega) h2
    unfold LexLt at e1
    omega
  have hmono := fo_mono' hfo1
  have hstep : ∀ j (s : PSt), j < n →
      (∃ m, PInv n p pr lb (foOf pr lb) (2 * j) m s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧
        s.2.2.1 = ((List.range j).map a).toArray ∧ s.2.2.2.1 = ((List.range j).map b).toArray) →
      ∃ s', pBody A B j s = pure (.yield s') ∧
        ∃ m, PInv n p pr lb (foOf pr lb) (2 * (j + 1)) m s'.1 s'.2.1 s'.2.2.2.2.1 s'.2.2.2.2.2 ∧
          s'.2.2.1 = ((List.range (j + 1)).map a).toArray ∧
          s'.2.2.2.1 = ((List.range (j + 1)).map b).toArray := by
    rintro j ⟨pos, pts, al, be, par, lab⟩ hj ⟨m, H, hal, hbe⟩
    dsimp only at H hal hbe
    have hsz : pts.size = m := by rw [H.pts_eq, rangeArr_size]
    have hjm : j < m := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · have := H.m_pos
        omega
      · refine (H.disc j h0 hj).2 ?_
        have := key j h0 hj
        omega
    have hv : pts[j]! = p j := by rw [H.pts_eq, rangeArr_get hjm]
    have hjlt : j < pts.size := by omega
    unfold pBody
    simp only [hjlt, ite_true, hv, hA j hj, hB j hj, pIns_eq]
    obtain ⟨m1, H1, h1⟩ := ins_step (x := a j) (h := j) (l := 1) hlt hinj hmono H (ha j hj) hn
      (fun y hy1 hyn e => by
        have := key y hy1 hyn
        rcases this with ⟨-, ⟨e1, -, e3⟩ | ⟨e1, -, -⟩⟩
        · have : pr y = j := by omega
          rw [← this, e3]
        · omega)
      (by
        rcases hrdA j hj with e | e
        · exact Or.inl e
        · rcases Nat.eq_zero_or_pos (a j) with e0 | e0
          · exact Or.inl e0
          · right
            have := key (a j) e0 (ha j hj)
            unfold LexLt at e
            omega)
      (fun hx1 hfx => by
        have := key (a j) hx1 (ha j hj)
        omega)
    obtain ⟨m2, H2, h2⟩ := ins_step (x := b j) (h := j) (l := 2) hlt hinj hmono H1 (hb j hj) hn
      (fun y hy1 hyn e => by
        have := key y hy1 hyn
        rcases this with ⟨-, ⟨e1, -, -⟩ | ⟨e1, -, e3⟩⟩
        · omega
        · have : pr y = j := by omega
          rw [← this, e3])
      (by
        rcases hrdB j hj with e | e
        · exact Or.inl e
        · rcases Nat.eq_zero_or_pos (b j) with e0 | e0
          · exact Or.inl e0
          · right
            have := key (b j) e0 (hb j hj)
            unfold LexLt at e
            omega)
      (fun hx1 hfx => by
        have := key (b j) hx1 (hb j hj)
        omega)
    refine ⟨_, rfl, m2, ?_, ?_, ?_⟩
    · have e : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [e]
      exact H2
    · dsimp only
      rw [h1, hal, List.range_succ, List.map_append]
      simp
    · dsimp only
      rw [h2, hbe, List.range_succ, List.map_append]
      simp
  have hinit : ∃ m, PInv n p pr lb (foOf pr lb) (2 * 0) m (pInit (p 0)).1 (pInit (p 0)).2.1
      (pInit (p 0)).2.2.2.2.1 (pInit (p 0)).2.2.2.2.2 ∧
      (pInit (p 0)).2.2.1 = ((List.range 0).map a).toArray ∧
      (pInit (p 0)).2.2.2.1 = ((List.range 0).map b).toArray := by
    have hrs : (Array.replicate 10000 10000).size = 10000 := Array.size_replicate
    refine ⟨1, ⟨by simp [pInit], by simp [pInit, hpr0], by simp [pInit, hlb0], Nat.le_refl 1, hn0,
      fun y hy1 _ => by omega, by simp [pInit], fun y hy => ?_, fun v hv hall => ?_⟩,
      by simp [pInit], by simp [pInit]⟩
    · have : y = 0 := by omega
      subst this
      simp only [pInit]
      rw [Array.getElem!_set!_self _ _ _ (by rw [hrs]; exact hlt 0 hn0)]
    · simp only [pInit]
      rw [Array.getElem!_set!_ne _ _ _ _ (hall 0 Nat.zero_lt_one),
        getElem!_pos _ v (by rw [hrs]; exact hv)]
      simp
  have hend : ∃ m, PInv n p pr lb (foOf pr lb) (2 * n) m
      (Id.run (forIn (List.range' 0 10000) (pInit (p 0)) (pBody A B))).1
      (Id.run (forIn (List.range' 0 10000) (pInit (p 0)) (pBody A B))).2.1
      (Id.run (forIn (List.range' 0 10000) (pInit (p 0)) (pBody A B))).2.2.2.2.1
      (Id.run (forIn (List.range' 0 10000) (pInit (p 0)) (pBody A B))).2.2.2.2.2 ∧
      (Id.run (forIn (List.range' 0 10000) (pInit (p 0)) (pBody A B))).2.2.1 =
        ((List.range n).map a).toArray ∧
      (Id.run (forIn (List.range' 0 10000) (pInit (p 0)) (pBody A B))).2.2.2.1 =
        ((List.range n).map b).toArray := by
    refine forIn_range'_done 10000 0 (pInit (p 0)) (pBody A B)
      (fun j s => j ≤ n ∧ ∃ m, PInv n p pr lb (foOf pr lb) (2 * j) m s.1 s.2.1 s.2.2.2.2.1
        s.2.2.2.2.2 ∧ s.2.2.1 = ((List.range j).map a).toArray ∧
        s.2.2.2.1 = ((List.range j).map b).toArray)
      (fun s => ∃ m, PInv n p pr lb (foOf pr lb) (2 * n) m s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧
        s.2.2.1 = ((List.range n).map a).toArray ∧ s.2.2.2.1 = ((List.range n).map b).toArray)
      (fun j _ s hP => ?_) (fun s hP => ?_) ⟨Nat.zero_le _, hinit⟩
    · rw [Nat.zero_add]
      rcases Nat.lt_or_ge j n with hjn | hjn
      · obtain ⟨s', e, hs'⟩ := hstep j s hjn hP.2
        exact Or.inl ⟨s', e, by omega, hs'⟩
      · obtain ⟨hjle, hR⟩ := hP
        have e : j = n := by omega
        subst e
        right
        refine ⟨s, ?_, hR⟩
        obtain ⟨m, H, -, -⟩ := hR
        have : ¬ j < s.2.1.size := by
          rw [H.pts_eq, rangeArr_size]
          have := H.m_le
          omega
        unfold pBody
        simp only [this, ite_false]
    · obtain ⟨hle, hR⟩ := hP
      have e : n = 10000 := by omega
      subst e
      exact hR
  rw [pairBFS_eq]
  obtain ⟨m, H, hal, hbe⟩ := hend
  generalize (forIn (List.range' 0 10000) (pInit (p 0)) (pBody A B) : Id PSt) = s at H hal hbe ⊢
  simp only [Id.run] at H hal hbe
  have hmn : m = n := by
    refine Classical.byContradiction fun hne => ?_
    have hlt' : m < n := by have := H.m_le; omega
    have h1 : ¬ foOf pr lb m < 2 * n := fun e' => Nat.lt_irrefl m ((H.disc m H.m_pos hlt').2 e')
    have h2 := key m H.m_pos hlt'
    omega
  rw [hmn] at H
  have hpos : s.1 = ((List.range 10000).map ps).toArray := by
    refine ext_rangeArr H.size fun v hv => ?_
    by_cases hex : ∃ y < n, p y = v
    · obtain ⟨y, hy, rfl⟩ := hex
      rw [H.hit y hy, hhit y hy]
    · have hall : ∀ y < n, p y ≠ v := fun y hy e => hex ⟨y, hy, e⟩
      rw [H.miss v hv hall, hmiss v hv hall]
  rw [← H.pts_eq, ← hal, ← hbe, ← H.par_eq, ← H.lab_eq, ← hpos]

theorem pairOrbOK_eq {A B : Array Nat} {n : Nat} {p a b pr lb ps : Nat → Nat}
    (D : PairData A B n p a b pr lb ps) (hAs : A.size = 100) (hBs : B.size = 100)
    (cov : Nat → Nat → Bool) :
    pairOrbOK A B (p 0) cov =
      allIn 0 100 fun x => allIn 0 100 fun y => !cov x y || decide (ps (pairCode x y) < n) := by
  have hcov : (allIn 0 100 fun x => allIn 0 100 fun y =>
      !cov x y || decide (((List.range 10000).map ps).toArray[pairCode x y]! < n)) =
      allIn 0 100 fun x => allIn 0 100 fun y => !cov x y || decide (ps (pairCode x y) < n) :=
    allIn_congr fun x _ hx => allIn_congr fun y _ hy => by
      rw [rangeArr_get (by unfold pairCode; omega)]
  unfold pairOrbOK
  rw [pairBFS_sim D]
  dsimp only
  simp only [rangeArr_size]
  rw [hcov, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAs, hBs⟩, D.n_pos⟩, D.n_le⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩,
      rangeArr_get D.n_pos⟩, ?_⟩, ?_⟩, ?_⟩, h⟩
    · refine allIn_iff'.2 fun i _ hi => ?_
      simp only [rangeArr_get (p := p) hi, rangeArr_get (p := a) hi, rangeArr_get (p := b) hi]
      simp only [rangeArr_get (p := p) (D.a_lt i hi), rangeArr_get (p := p) (D.b_lt i hi),
        Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨D.p_lt i hi, D.a_lt i hi⟩, (D.img_a i hi).symm⟩, D.b_lt i hi⟩, (D.img_b i hi).symm⟩
    · refine allIn_iff'.2 fun i h1 hi => ?_
      have t := D.tree i h1 hi
      simp only [rangeArr_get (p := pr) hi, rangeArr_get (p := lb) hi]
      simp only [rangeArr_get (p := a) (Nat.lt_trans t.1 hi),
        rangeArr_get (p := b) (Nat.lt_trans t.1 hi), Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq]
      exact t
    · refine allIn_iff'.2 fun v _ hv => ?_
      simp only [rangeArr_get (p := ps) hv, decide_eq_true_eq]
      intro hlt
      rw [rangeArr_get hlt]
      by_cases hex : ∃ y < n, p y = v
      · obtain ⟨y, hy, rfl⟩ := hex
        rw [D.ps_hit y hy]
      · have := D.ps_miss v hv fun y hy e => hex ⟨y, hy, e⟩
        have := D.n_le
        omega

end CFSG.KC.HSPinnedBfs

end
