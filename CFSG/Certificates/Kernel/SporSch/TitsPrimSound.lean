module

public import Certificates.Data.Kernel.SporSch.TitsPrim
public import CFSG.Certificates.Kernel.SporSch.TitsStabSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Tits

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem foldBlk_add {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i s, f i s = s + g i)
    (b : Nat) : ∀ len s, foldBlk b f len s = s + ∑ l ∈ Finset.range len, g (b + l)
  | 0, s => by simp [foldBlk]
  | len + 1, s => by
    change strictN (f (Nat.add b len) s) (foldBlk b f len) = _
    rw [strictN_eq, foldBlk_add hf b len, hf, Finset.sum_range_succ]
    simp only [Nat.add_eq]
    ring

theorem foldN_add {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i s, f i s = s + g i)
    (n s : Nat) : foldN n f s = s + ∑ i ∈ Finset.range n, g i := by
  have sl : ∀ a, Nat.shiftLeft a (nat_lit 6) = 64 * a := fun a => by
    rw [Nat.mul_comm]
    exact Nat.shiftLeft_eq a 6
  have key : ∀ q s', Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q s' =
      s' + ∑ i ∈ Finset.range (64 * q), g i := by
    intro q
    induction q with
    | zero => intro s'; simp
    | succ h ih =>
      intro s'
      change strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s') _ = _
      rw [strictN_eq, ih, foldBlk_add hf, Nat.mul_succ, Finset.sum_range_add, sl]
      ring
  have e1 : Nat.land n (nat_lit 63) = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
  have e2 : Nat.shiftRight n (nat_lit 6) = n / 64 := Nat.shiftRight_eq_div_pow n 6
  unfold foldN
  dsimp only
  rw [key, foldBlk_add hf, e1, e2, sl]
  conv_rhs => rw [← Nat.div_add_mod n 64, Finset.sum_range_add]
  ring

theorem cntK_sound (n w LAB c : Nat) : labelCount n (unpack n w LAB) c = cntK n w LAB c := by
  have hc : ∀ (p : Nat → Bool) (m : Nat),
      (List.range m).countP p = ∑ i ∈ Finset.range m, if p i then 1 else 0 := by
    intro p m
    induction m with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]; simp
  unfold labelCount cntK
  rw [hc, foldN_add (g := fun x => if Nat.beq (pgW w LAB x) c then 1 else 0)]
  · rw [Nat.zero_add]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [unpackW_get (Finset.mem_range.1 hx), pgW_eq]
    congr 1
  · intro i s
    cases Nat.beq (pgW w LAB i) c <;> rfl

private theorem strictB_eqM (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bIfT_iff (c e : Bool) :
    Bool.rec (motive := fun _ => Bool) e true c = true ↔ c = true ∨ e = true := by
  cases c <;> simp

private theorem allLt_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    allLt n p = true := by
  unfold allLt
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.all_succ, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (by omega), h n (by omega)⟩

private theorem gens_lt {n w kG : Nat} {GS : Nat → Nat}
    (hc : allN kG (fun i => canonK n w (mask w) (n * w) (GS i)) = true) :
    ∀ i < kG, ∀ y < n, pgW w (GS i) y < n := by
  intro i hi y hy
  have h1 := allN_spec hc i hi
  unfold canonK at h1
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h1
  obtain ⟨-, h3⟩ := (bAnd_iff _ _).1 h2
  rw [pgW_eq]
  exact Nat.blt_eq.mp (allN_spec h3 y hy)

private theorem bIf_cases {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

private theorem blt_false {a b : Nat} (h : Nat.blt a b = false) : b ≤ a :=
  Nat.not_lt.1 fun hlt => by
    rw [Nat.blt_eq.mpr hlt] at h
    exact Bool.noConfusion h

private theorem ble_false {a b : Nat} (h : Nat.ble a b = false) : b < a :=
  Nat.not_le.1 fun hle => by
    rw [Nat.ble_eq.mpr hle] at h
    exact Bool.noConfusion h

private theorem set_getT {a : Array Nat} {i j : Nat} {v : Nat} (hi : i < a.size) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by simpa using hj
    rw [getElem!_pos _ j hj', getElem!_pos a j hj]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
  · have hj' : ¬ j < (a.set! i v).size := by simpa using hj
    have hij : j ≠ i := by omega
    rw [getElem!_neg _ j hj', getElem!_neg a j hj, ite_eq_right hij]

private theorem forIn_invT {β : Type} (R : Nat → β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    ∀ k a (init : β), a + k ≤ E → R a init → R (a + k) (forIn (List.range' a k) init f)
  | 0, _, _, _, h => h
  | k + 1, a, init, hE, h => by
    obtain ⟨b', hb, hR⟩ := hf a init (by omega) h
    rw [List.range'_succ, List.forIn_cons, hb]
    have e : a + (k + 1) = a + 1 + k := by omega
    rw [e]
    exact forIn_invT R E f hf k (a + 1) b' (by omega) hR

private theorem forIn_rng {β : Type} (k : Nat) (init : β) (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id) [0:k] init f = forIn (List.range' 0 k) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hl : List.range' [0:k].start [0:k].size [0:k].step = List.range' 0 k := by
    simp [Std.Legacy.Range.size]
  rw [hl]

private theorem scanK_succ (w : Nat) (GS : Nat → Nat) (POS LAB DEP PAR GL x c' f i c : Nat) :
    scanK w GS POS LAB DEP PAR GL x c' (f + 1) i c =
      strictB (pgW w (GS i) x) (fun y => strictB (pgW w POS y) (fun py =>
        bIf(Nat.ble c py,
          bAnd(Nat.beq py c, bAnd(Nat.beq (pgW w LAB y) (pgW w LAB x),
            bAnd(Nat.beq (pgW w DEP y) (Nat.succ (pgW w DEP x)), bAnd(Nat.beq (pgW w PAR y) x,
            bAnd(Nat.beq (pgW w GL y) i,
              scanK w GS POS LAB DEP PAR GL x c' f (Nat.succ i) (Nat.succ c)))))),
          scanK w GS POS LAB DEP PAR GL x c' f (Nat.succ i) c))) := rfl

private theorem scanK_step {w : Nat} {GS : Nat → Nat} {POS LAB DEP PAR GL x c' f i c : Nat}
    (h : scanK w GS POS LAB DEP PAR GL x c' (f + 1) i c = true) :
    (pgW w POS (pgW w (GS i) x) = c ∧ pgW w LAB (pgW w (GS i) x) = pgW w LAB x ∧
      pgW w DEP (pgW w (GS i) x) = pgW w DEP x + 1 ∧ pgW w PAR (pgW w (GS i) x) = x ∧
      pgW w GL (pgW w (GS i) x) = i ∧
      scanK w GS POS LAB DEP PAR GL x c' f (i + 1) (c + 1) = true) ∨
    (pgW w POS (pgW w (GS i) x) < c ∧ scanK w GS POS LAB DEP PAR GL x c' f (i + 1) c = true) := by
  rw [scanK_succ] at h
  simp only [strictB_eqM] at h
  rcases bIf_cases h with ⟨-, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨e1, h2⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨e2, h2⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨e3, h2⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨e4, h2⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨e5, h2⟩ := (bAnd_iff _ _).1 h2
    exact Or.inl ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3,
      Nat.eq_of_beq_eq_true e4, Nat.eq_of_beq_eq_true e5, h2⟩
  · exact Or.inr ⟨ble_false h1, h2⟩

private theorem scanK_le {w : Nat} {GS : Nat → Nat} {POS LAB DEP PAR GL x c' : Nat} :
    ∀ {f i c : Nat}, scanK w GS POS LAB DEP PAR GL x c' f i c = true → c ≤ c'
  | 0, _, c, h => by
    have h' : Nat.beq c c' = true := h
    exact Nat.le_of_eq (Nat.eq_of_beq_eq_true h')
  | f + 1, _, _, h => by
    rcases scanK_step h with ⟨-, -, -, -, -, h'⟩ | ⟨-, h'⟩
    · exact Nat.le_of_succ_le (scanK_le h')
    · exact scanK_le h'

private theorem scanK_push {n N w kG Q : Nat} {GS : Nat → Nat} {POS LAB DEP PAR GL x c' : Nat}
    (hGx : ∀ j < kG, pgW w (GS j) x < n) (hc'N : c' ≤ N)
    (hPQ : ∀ y < n, pgW w POS y < N → pgW w Q (pgW w POS y) = y) :
    ∀ {f i c : Nat}, i + f = kG → scanK w GS POS LAB DEP PAR GL x c' f i c = true →
      ∀ q, c ≤ q → q < c' → pgW w DEP (pgW w Q q) = pgW w DEP x + 1
  | 0, _, c, _, h, q, h1, h2 => by
    have h' : Nat.beq c c' = true := h
    have := Nat.eq_of_beq_eq_true h'
    omega
  | f + 1, i, c, hi, h, q, h1, h2 => by
    rcases scanK_step h with ⟨e1, -, e3, -, -, h'⟩ | ⟨-, h'⟩
    · rcases Nat.eq_or_lt_of_le h1 with e | e
      · have hyn := hGx i (by omega)
        rw [← e, ← e1, hPQ _ hyn (by omega), e3]
      · exact scanK_push hGx hc'N hPQ (by omega) h' q e h2
    · exact scanK_push hGx hc'N hPQ (by omega) h' q h1 h2

private theorem head_lt {N : Nat} {Cf Df : Nat → Nat} (hCN : Cf N = N)
    (hpush : ∀ h < N, ∀ q, Cf h ≤ q → q < Cf (h + 1) → Df q = Df h + 1) :
    ∀ h < N, h < Cf h := by
  intro h0 hh0
  by_contra hle
  replace hle : Cf h0 ≤ h0 := Nat.le_of_not_lt hle
  have hfind : ∀ q k, Cf h0 ≤ q → q < Cf (h0 + k) →
      ∃ h, h0 ≤ h ∧ h < h0 + k ∧ Cf h ≤ q ∧ q < Cf (h + 1) := by
    intro q k
    induction k with
    | zero =>
      intro h1 h2
      rw [Nat.add_zero] at h2
      omega
    | succ k ih =>
      intro h1 h2
      by_cases h3 : q < Cf (h0 + k)
      · obtain ⟨h, a, b, c, d⟩ := ih h1 h3
        exact ⟨h, a, by omega, c, d⟩
      · exact ⟨h0 + k, by omega, by omega, by omega, h2⟩
  have key : ∀ d q, Df q = d → Cf h0 ≤ q → q < N → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro q hq h1 h2
      have e : h0 + (N - h0) = N := by omega
      obtain ⟨h, a, b, c, d'⟩ := hfind q (N - h0) h1 (by rw [e, hCN]; exact h2)
      have := hpush h (by omega) q c d'
      exact ih (Df h) (by omega) h rfl (by omega) (by omega)
  exact key _ h0 rfl hle hh0

private abbrev ISt := Array Nat × Array Nat × Array Nat × Array Nat × Array Nat

private abbrev OSt := Array Nat × Array Nat × Array Nat × Array Nat × Array Nat × Nat

private def fInit (reps : Array Nat) (c : Nat) (s : Array Nat × Array Nat) :
    Id (ForInStep (Array Nat × Array Nat)) :=
  pure (.yield (s.1.set! reps[c]! c, s.2.push reps[c]!))

private def fInner (gens : Array (Array Nat)) (m x i : Nat) (s : ISt) : Id (ForInStep ISt) :=
  if (s.1[(gens[i]!)[x]!]! == m) = true then
    pure (.yield (s.1.set! (gens[i]!)[x]! s.1[x]!, s.2.1.set! (gens[i]!)[x]! (s.2.1[x]! + 1),
      s.2.2.1.set! (gens[i]!)[x]! x, s.2.2.2.1.set! (gens[i]!)[x]! i,
      s.2.2.2.2.push (gens[i]!)[x]!))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

private def fOuter (gens : Array (Array Nat)) (m : Nat) (_ : Nat) (s : OSt) : Id (ForInStep OSt) :=
  if s.2.2.2.2.2 < s.2.2.2.2.1.size then do
    let s' ← forIn [0:gens.size] (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1)
      (fInner gens m s.2.2.2.2.1[s.2.2.2.2.2]!)
    pure (.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2.1, s'.2.2.2.2, s.2.2.2.2.2 + 1))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

private theorem orbitForest_eq (n : Nat) (gens : Array (Array Nat)) (reps : Array Nat) :
    orbitForest n gens reps =
      (let s0 := (forIn [0:reps.size] (Array.replicate n reps.size, (#[] : Array Nat))
          (fInit reps) : Id (Array Nat × Array Nat))
       let s := (forIn [0:n] (s0.1, Array.replicate n 0, Array.replicate n 0, Array.replicate n 0,
          s0.2, 0) (fOuter gens reps.size) : Id OSt)
       (s.1, s.2.1, s.2.2.1, s.2.2.2.1)) := rfl

private def BInv (n w m POS Q LAB DEP PAR GL c : Nat) (s : ISt) : Prop :=
  s.1.size = n ∧ s.2.1.size = n ∧ s.2.2.1.size = n ∧ s.2.2.2.1.size = n ∧
    s.2.2.2.2.size = c ∧ (∀ k < c, s.2.2.2.2[k]! = pgW w Q k ∧ pgW w LAB (pgW w Q k) < m) ∧
    ∀ y < n, s.1[y]! = (if pgW w POS y < c then pgW w LAB y else m) ∧
      s.2.1[y]! = (if pgW w POS y < c then pgW w DEP y else 0) ∧
      s.2.2.1[y]! = (if pgW w POS y < c then pgW w PAR y else 0) ∧
      s.2.2.2.1[y]! = (if pgW w POS y < c then pgW w GL y else 0)

theorem bfsTK_sound {n w kG m REP N Q POS C LAB DEP PAR GL : Nat} {GS : Nat → Nat}
    {gens : Array (Array Nat)} {reps : Array Nat} (_hw : n + 1 < 2 ^ w)
    (hg : gens.size = kG ∧ ∀ i < kG, gens[i]! = unpack n w (GS i))
    (hc : allN kG (fun i => canonK n w (mask w) (n * w) (GS i)) = true)
    (hr : reps.size = m ∧ ∀ c < m, reps[c]! = pg w (mask w) REP c)
    (h : bfsTK n w GS kG m REP N Q POS C LAB DEP PAR GL = true) :
    orbitForest n gens reps = (unpack n w LAB, unpack n w DEP, unpack n w PAR, unpack n w GL) := by
  obtain ⟨hgs, hgv⟩ := hg
  obtain ⟨hrs, hrv⟩ := hr
  have hGn := gens_lt hc
  have U : ∀ P y, y < n → (unpack n w P)[y]! = pgW w P y := fun P y hy => by
    rw [unpackW_get hy, pgW_eq]
  have US : ∀ P, (unpack n w P).size = n := fun P => by
    unfold unpack
    rw [Array.size_ofFn]
  have G : ∀ i < kG, ∀ y < n, (gens[i]!)[y]! = pgW w (GS i) y := fun i hi y hy => by
    rw [hgv i hi, U _ y hy]
  unfold bfsTK at h
  obtain ⟨hmN, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hNn, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hC0, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hCN, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hroots, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hqueue, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hpos, hscan⟩ := (bAnd_iff _ _).1 h
  replace hmN : m ≤ N := Nat.ble_eq.mp hmN
  replace hNn : N ≤ n := Nat.ble_eq.mp hNn
  replace hC0 : pgW w C 0 = m := Nat.eq_of_beq_eq_true hC0
  replace hCN : pgW w C N = N := Nat.eq_of_beq_eq_true hCN
  have RT : ∀ c < m, pgW w Q c = pgW w REP c ∧ pgW w LAB (pgW w REP c) = c ∧
      pgW w DEP (pgW w REP c) = 0 ∧ pgW w PAR (pgW w REP c) = 0 ∧
      pgW w GL (pgW w REP c) = 0 := by
    intro c hc'
    have h1 := allN_spec hroots c hc'
    simp only [strictB_eqM] at h1
    obtain ⟨e1, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨e2, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨e3, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨e4, e5⟩ := (bAnd_iff _ _).1 h1
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3,
      Nat.eq_of_beq_eq_true e4, Nat.eq_of_beq_eq_true e5⟩
  have QF : ∀ k < N, pgW w Q k < n ∧ pgW w POS (pgW w Q k) = k := by
    intro k hk
    have h1 := allN_spec hqueue k hk
    simp only [strictB_eqM] at h1
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 h1
    exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩
  have PF : ∀ y < n, (pgW w POS y < N ∧ pgW w Q (pgW w POS y) = y) ∨
      (N ≤ pgW w POS y ∧ pgW w LAB y = m ∧ pgW w DEP y = 0 ∧ pgW w PAR y = 0 ∧
        pgW w GL y = 0) := by
    intro y hy
    have h1 := allN_spec hpos y hy
    simp only [strictB_eqM] at h1
    rcases bIf_cases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩
    · obtain ⟨e3, e2⟩ := (bAnd_iff _ _).1 e2
      obtain ⟨e4, e2⟩ := (bAnd_iff _ _).1 e2
      obtain ⟨e5, e6⟩ := (bAnd_iff _ _).1 e2
      exact Or.inr ⟨blt_false e1, Nat.eq_of_beq_eq_true e3, Nat.eq_of_beq_eq_true e4,
        Nat.eq_of_beq_eq_true e5, Nat.eq_of_beq_eq_true e6⟩
  have PQ : ∀ y < n, pgW w POS y < N → pgW w Q (pgW w POS y) = y := fun y hy hp => by
    rcases PF y hy with h1 | h1
    · exact h1.2
    · omega
  have DZ : ∀ y < n, pgW w POS y < m →
      pgW w DEP y = 0 ∧ pgW w PAR y = 0 ∧ pgW w GL y = 0 := by
    intro y hy hp
    have e : pgW w REP (pgW w POS y) = y := by rw [← (RT _ hp).1, PQ y hy (by omega)]
    obtain ⟨-, -, d0, p0, g0⟩ := RT _ hp
    rw [e] at d0 p0 g0
    exact ⟨d0, p0, g0⟩
  have SC : ∀ h < N, scanK w GS POS LAB DEP PAR GL (pgW w Q h) (pgW w C (h + 1)) kG 0
      (pgW w C h) = true := fun h hh => allN_spec hscan h hh
  have CM : ∀ h < N, pgW w C h ≤ pgW w C (h + 1) := fun h hh => scanK_le (SC h hh)
  have CN : ∀ h ≤ N, pgW w C h ≤ N := by
    have : ∀ k h, h + k = N → pgW w C h ≤ N := by
      intro k
      induction k with
      | zero =>
        intro h hk
        rw [Nat.add_zero] at hk
        rw [hk, hCN]
      | succ k ih =>
        intro h hk
        exact Nat.le_trans (CM h (by omega)) (ih (h + 1) (by omega))
    intro h hh
    exact this (N - h) h (by omega)
  have PU : ∀ h < N, ∀ q, pgW w C h ≤ q → q < pgW w C (h + 1) →
      pgW w DEP (pgW w Q q) = pgW w DEP (pgW w Q h) + 1 := fun h hh =>
    scanK_push (fun j hj => hGn j hj _ (QF h hh).1) (CN (h + 1) hh) PQ (Nat.zero_add kG) (SC h hh)
  have HL : ∀ h < N, h < pgW w C h :=
    head_lt (Cf := fun h => pgW w C h) (Df := fun q => pgW w DEP (pgW w Q q)) hCN PU
  have hreps : ∀ c < m, reps[c]! = pgW w Q c := fun c hc' => by
    rw [hrv c hc', ← pgW_eq, (RT c hc').1]
  have I0 : ∀ s0 : Array Nat × Array Nat,
      forIn (m := Id) [0:m] (Array.replicate n m, (#[] : Array Nat)) (fInit reps) = s0 →
      s0.1.size = n ∧ s0.2.size = m ∧ (∀ k < m, s0.2[k]! = pgW w Q k) ∧
        ∀ y < n, s0.1[y]! = if pgW w POS y < m then pgW w LAB y else m := by
    intro s0 hs0
    rw [forIn_rng] at hs0
    subst hs0
    have STEP0 : ∀ c (s : Array Nat × Array Nat), c < m →
        (s.1.size = n ∧ s.2.size = c ∧ (∀ k < c, s.2[k]! = pgW w Q k) ∧
          ∀ y < n, s.1[y]! = if pgW w POS y < c then pgW w LAB y else m) →
        ∃ s', fInit reps c s = pure (.yield s') ∧
          (s'.1.size = n ∧ s'.2.size = c + 1 ∧ (∀ k < c + 1, s'.2[k]! = pgW w Q k) ∧
            ∀ y < n, s'.1[y]! = if pgW w POS y < c + 1 then pgW w LAB y else m) := by
      intro c s hcm ⟨s1, s2, s3, s4⟩
      have hq := QF c (by omega)
      refine ⟨(s.1.set! (pgW w Q c) c, s.2.push (pgW w Q c)), by unfold fInit; rw [hreps c hcm],
        ?_, ?_, ?_, ?_⟩
      · dsimp only
        rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, s1]
      · dsimp only
        rw [Array.size_push, s2]
      · intro k hk
        dsimp only
        rw [getElem!_pos _ k (by rw [Array.size_push, s2]; exact hk), Array.getElem_push]
        split
        · rename_i hk'
          rw [← getElem!_pos _ k hk']
          exact s3 k (by omega)
        · have hkc : k = c := by omega
          rw [hkc]
      · intro y hy
        dsimp only
        rw [set_getT (by rw [s1]; exact hq.1), s4 y hy]
        by_cases hyq : y = pgW w Q c
        · rw [ite_eq_left hyq, hyq, hq.2, ite_eq_left (Nat.lt_succ_self c), (RT c hcm).1, (RT c hcm).2.1]
        · have hne : pgW w POS y ≠ c := fun e' => hyq (by rw [← PQ y hy (by omega), e'])
          rw [ite_eq_right hyq]
          by_cases hp : pgW w POS y < c
          · rw [ite_eq_left hp, ite_eq_left (by omega)]
          · rw [ite_eq_right hp, ite_eq_right (by omega)]
    have INIT0 : (Array.replicate n m, (#[] : Array Nat)).1.size = n ∧
        (Array.replicate n m, (#[] : Array Nat)).2.size = 0 ∧
        (∀ k < 0, (Array.replicate n m, (#[] : Array Nat)).2[k]! = pgW w Q k) ∧
        ∀ y < n, (Array.replicate n m, (#[] : Array Nat)).1[y]! =
          if pgW w POS y < 0 then pgW w LAB y else m := by
      refine ⟨by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), fun y hy => ?_⟩
      dsimp only
      rw [ite_eq_right (Nat.not_lt_zero _), getElem!_pos _ y (by simpa using hy),
        Array.getElem_replicate]
    have := forIn_invT (fun c (s : Array Nat × Array Nat) => s.1.size = n ∧ s.2.size = c ∧
        (∀ k < c, s.2[k]! = pgW w Q k) ∧
        ∀ y < n, s.1[y]! = if pgW w POS y < c then pgW w LAB y else m) m (fInit reps) STEP0 m 0
      (Array.replicate n m, (#[] : Array Nat)) (Nat.le_of_eq (Nat.zero_add m)) INIT0
    rw [Nat.zero_add] at this
    exact this
  have INNER : ∀ j < N, ∀ s : ISt, BInv n w m POS Q LAB DEP PAR GL (pgW w C j) s → ∀ s' : ISt,
      forIn (m := Id) [0:gens.size] s (fInner gens m (pgW w Q j)) = s' →
      BInv n w m POS Q LAB DEP PAR GL (pgW w C (j + 1)) s' := by
    intro j hj s hs s' hs'
    rw [hgs, forIn_rng] at hs'
    subst hs'
    have hx := (QF j hj).1
    have hjC := HL j hj
    have ISTEP : ∀ i (t : ISt), i < kG →
        (∃ c, pgW w C j ≤ c ∧ BInv n w m POS Q LAB DEP PAR GL c t ∧
          scanK w GS POS LAB DEP PAR GL (pgW w Q j) (pgW w C (j + 1)) (kG - i) i c = true) →
        ∃ t', fInner gens m (pgW w Q j) i t = pure (.yield t') ∧
          (∃ c, pgW w C j ≤ c ∧ BInv n w m POS Q LAB DEP PAR GL c t' ∧
            scanK w GS POS LAB DEP PAR GL (pgW w Q j) (pgW w C (j + 1)) (kG - (i + 1)) (i + 1)
              c = true) := by
      intro i t hi ⟨c, hjc, ht, hsc⟩
      obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := ht
      have e : kG - i = (kG - (i + 1)) + 1 := by omega
      rw [e] at hsc
      have hyn := hGn i hi _ hx
      have hxc : pgW w POS (pgW w Q j) < c := by rw [(QF j hj).2]; omega
      have hcN : c ≤ N := Nat.le_trans (scanK_le hsc) (CN (j + 1) hj)
      rcases scanK_step hsc with ⟨e1, e2, e3, e4, e5, hsc'⟩ | ⟨e1, hsc'⟩
      ·
        have hc1 := scanK_le hsc'
        have hcN' : c < N := by
          have := CN (j + 1) hj
          omega
        have hQc : pgW w Q c = pgW w (GS i) (pgW w Q j) := by
          rw [← e1]
          exact PQ _ hyn (by omega)
        have hly : t.1[pgW w (GS i) (pgW w Q j)]! = m := by
          rw [(t7 _ hyn).1, ite_eq_right (by omega)]
        refine ⟨(t.1.set! (pgW w (GS i) (pgW w Q j)) t.1[pgW w Q j]!,
          t.2.1.set! (pgW w (GS i) (pgW w Q j)) (t.2.1[pgW w Q j]! + 1),
          t.2.2.1.set! (pgW w (GS i) (pgW w Q j)) (pgW w Q j),
          t.2.2.2.1.set! (pgW w (GS i) (pgW w Q j)) i,
          t.2.2.2.2.push (pgW w (GS i) (pgW w Q j))),
          by unfold fInner; rw [G i hi _ hx, hly, ite_eq_left (beq_self_eq_true m)],
          c + 1, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hsc'⟩
        · dsimp only
          rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, t1]
        · dsimp only
          rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, t2]
        · dsimp only
          rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, t3]
        · dsimp only
          rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, t4]
        · dsimp only
          rw [Array.size_push, t5]
        · intro k hk
          dsimp only
          rw [getElem!_pos _ k (by rw [Array.size_push, t5]; exact hk), Array.getElem_push]
          split
          · rename_i hk'
            rw [← getElem!_pos _ k hk']
            exact t6 k (by omega)
          · have hkc : k = c := by omega
            rw [hkc, hQc, e2]
            exact ⟨rfl, (t6 j (by omega)).2⟩
        · intro z hz
          dsimp only
          rw [set_getT (by rw [t1]; exact hyn), set_getT (by rw [t2]; exact hyn),
            set_getT (by rw [t3]; exact hyn), set_getT (by rw [t4]; exact hyn)]
          by_cases hzy : z = pgW w (GS i) (pgW w Q j)
          · have hpy : pgW w POS (pgW w (GS i) (pgW w Q j)) < c + 1 := by omega
            rw [ite_eq_left hzy, ite_eq_left hzy, ite_eq_left hzy, ite_eq_left hzy, hzy, ite_eq_left hpy, ite_eq_left hpy,
              ite_eq_left hpy, ite_eq_left hpy, (t7 _ hx).1, (t7 _ hx).2.1, ite_eq_left hxc, ite_eq_left hxc, e2, e3,
              e4, e5]
            exact ⟨rfl, rfl, rfl, rfl⟩
          · have hzc : pgW w POS z ≠ c := fun e' => hzy (by
              rw [← PQ z hz (by omega), e', hQc])
            rw [ite_eq_right hzy, ite_eq_right hzy, ite_eq_right hzy, ite_eq_right hzy]
            have hiff : (pgW w POS z < c + 1) ↔ (pgW w POS z < c) := by omega
            simp only [hiff]
            exact t7 z hz
      ·
        have hyQ := PQ _ hyn (by omega)
        have hlab : pgW w LAB (pgW w (GS i) (pgW w Q j)) < m := by
          have := (t6 _ e1).2
          rwa [hyQ] at this
        have hly : t.1[pgW w (GS i) (pgW w Q j)]! = pgW w LAB (pgW w (GS i) (pgW w Q j)) := by
          rw [(t7 _ hyn).1, ite_eq_left e1]
        refine ⟨(t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2),
          by unfold fInner; rw [G i hi _ hx, hly, ite_eq_right (by rw [beq_iff_eq]; omega)],
          c, hjc, ⟨t1, t2, t3, t4, t5, t6, t7⟩, hsc'⟩
    have := forIn_invT (fun i (t : ISt) => ∃ c, pgW w C j ≤ c ∧
        BInv n w m POS Q LAB DEP PAR GL c t ∧
        scanK w GS POS LAB DEP PAR GL (pgW w Q j) (pgW w C (j + 1)) (kG - i) i c = true)
      kG (fInner gens m (pgW w Q j)) ISTEP kG 0 s (Nat.le_of_eq (Nat.zero_add kG))
      ⟨pgW w C j, Nat.le_refl _, hs, by rw [Nat.sub_zero]; exact SC j hj⟩
    rw [Nat.zero_add] at this
    obtain ⟨c, -, hc1, hc2⟩ := this
    rw [Nat.sub_self] at hc2
    have hc2' : Nat.beq c (pgW w C (j + 1)) = true := hc2
    rw [← Nat.eq_of_beq_eq_true hc2']
    exact hc1
  have OUT : ∀ s0 : Array Nat × Array Nat,
      (s0.1.size = n ∧ s0.2.size = m ∧ (∀ k < m, s0.2[k]! = pgW w Q k) ∧
        ∀ y < n, s0.1[y]! = if pgW w POS y < m then pgW w LAB y else m) →
      ∀ s : OSt, forIn (m := Id) [0:n] (s0.1, Array.replicate n 0, Array.replicate n 0,
        Array.replicate n 0, s0.2, 0) (fOuter gens m) = s →
      BInv n w m POS Q LAB DEP PAR GL N (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1) := by
    intro s0 ⟨i1, i2, i3, i4⟩ s hs
    rw [forIn_rng] at hs
    subst hs
    have OSTEP : ∀ j (b : OSt), j < n →
        (b.2.2.2.2.2 = min j N ∧ BInv n w m POS Q LAB DEP PAR GL (pgW w C (min j N))
          (b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1)) →
        ∃ b', fOuter gens m j b = pure (.yield b') ∧
          (b'.2.2.2.2.2 = min (j + 1) N ∧ BInv n w m POS Q LAB DEP PAR GL (pgW w C (min (j + 1) N))
            (b'.1, b'.2.1, b'.2.2.1, b'.2.2.2.1, b'.2.2.2.2.1)) := by
      intro j b _ ⟨hb1, hb2⟩
      by_cases hjN : j < N
      · rw [Nat.min_eq_left (Nat.le_of_lt hjN)] at hb1 hb2
        obtain ⟨-, -, -, -, q5, q6, -⟩ := id hb2
        dsimp only at q5 q6
        have hlt : b.2.2.2.2.2 < b.2.2.2.2.1.size := by
          rw [hb1, q5]
          exact HL j hjN
        have hx : b.2.2.2.2.1[b.2.2.2.2.2]! = pgW w Q j := by
          rw [hb1]
          exact (q6 j (HL j hjN)).1
        obtain ⟨s', hs'⟩ : ∃ s' : ISt, forIn (m := Id) [0:gens.size]
            (b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1) (fInner gens m (pgW w Q j)) = s' :=
          ⟨_, rfl⟩
        refine ⟨(s'.1, s'.2.1, s'.2.2.1, s'.2.2.2.1, s'.2.2.2.2, b.2.2.2.2.2 + 1), ?_, ?_, ?_⟩
        · unfold fOuter
          rw [ite_eq_left hlt, hx, hs']
          rfl
        · dsimp only
          rw [hb1, Nat.min_eq_left (by omega : j + 1 ≤ N)]
        · rw [Nat.min_eq_left (by omega : j + 1 ≤ N)]
          exact INNER j hjN _ hb2 s' hs'
      · have hjN' : N ≤ j := Nat.le_of_not_lt hjN
        rw [Nat.min_eq_right hjN', hCN] at hb2
        rw [Nat.min_eq_right hjN'] at hb1
        have hlt : ¬ b.2.2.2.2.2 < b.2.2.2.2.1.size := by
          obtain ⟨-, -, -, -, q5, -⟩ := id hb2
          dsimp only at q5
          rw [hb1, q5]
          exact Nat.lt_irrefl N
        refine ⟨(b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2),
          by unfold fOuter; rw [ite_eq_right hlt], ?_, ?_⟩
        · dsimp only
          rw [hb1, Nat.min_eq_right (by omega : N ≤ j + 1)]
        · rw [Nat.min_eq_right (by omega : N ≤ j + 1), hCN]
          exact hb2
    have hr0 : ∀ y < n, (Array.replicate n 0)[y]! = 0 := fun y hy => by
      rw [getElem!_pos _ y (by simpa using hy), Array.getElem_replicate]
    have INIT : (s0.1, Array.replicate n 0, Array.replicate n 0, Array.replicate n 0, s0.2,
          (0 : Nat)).2.2.2.2.2 = min 0 N ∧
        BInv n w m POS Q LAB DEP PAR GL (pgW w C (min 0 N))
          (s0.1, Array.replicate n 0, Array.replicate n 0, Array.replicate n 0, s0.2) := by
      rw [Nat.zero_min, hC0]
      refine ⟨rfl, i1, by simp, by simp, by simp, i2, fun k hk => ⟨i3 k hk, ?_⟩, fun y hy => ?_⟩
      · rw [(RT k hk).1, (RT k hk).2.1]
        exact hk
      · dsimp only
        refine ⟨i4 y hy, ?_, ?_, ?_⟩
        all_goals
          rw [hr0 y hy]
          by_cases hp : pgW w POS y < m
          · rw [ite_eq_left hp]
            simp [DZ y hy hp]
          · rw [ite_eq_right hp]
    have := forIn_invT (fun j (b : OSt) => b.2.2.2.2.2 = min j N ∧
        BInv n w m POS Q LAB DEP PAR GL (pgW w C (min j N))
          (b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1)) n (fOuter gens m) OSTEP n 0 _
      (Nat.le_of_eq (Nat.zero_add n)) INIT
    rw [Nat.zero_add, Nat.min_eq_right hNn, hCN] at this
    exact this.2
  have AE : ∀ (a : Array Nat) (P d : Nat), a.size = n →
      (∀ y < n, a[y]! = if pgW w POS y < N then pgW w P y else d) →
      (∀ y < n, N ≤ pgW w POS y → pgW w P y = d) → a = unpack n w P := by
    intro a P d hs ha hd
    refine Array.ext (by rw [hs, US]) fun y h1 h2 => ?_
    have hy : y < n := by omega
    rw [← getElem!_pos a y h1, ← getElem!_pos (unpack n w P) y h2, ha y hy, U P y hy]
    by_cases hp : pgW w POS y < N
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp, hd y hy (by omega)]
  have key : ∀ s : OSt,
      BInv n w m POS Q LAB DEP PAR GL N (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1) →
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1) =
        (unpack n w LAB, unpack n w DEP, unpack n w PAR, unpack n w GL) := by
    rintro s ⟨h1, h2, h3, h4, -, -, h7⟩
    dsimp only at h1 h2 h3 h4 h7
    have LD : ∀ y < n, N ≤ pgW w POS y → pgW w LAB y = m ∧ pgW w DEP y = 0 ∧
        pgW w PAR y = 0 ∧ pgW w GL y = 0 := fun y hy hp => by
      rcases PF y hy with h | h
      · omega
      · exact h.2
    rw [AE s.1 LAB m h1 (fun y hy => (h7 y hy).1) (fun y hy hp => (LD y hy hp).1),
      AE s.2.1 DEP 0 h2 (fun y hy => (h7 y hy).2.1) (fun y hy hp => (LD y hy hp).2.1),
      AE s.2.2.1 PAR 0 h3 (fun y hy => (h7 y hy).2.2.1) (fun y hy hp => (LD y hy hp).2.2.1),
      AE s.2.2.2.1 GL 0 h4 (fun y hy => (h7 y hy).2.2.2) (fun y hy hp => (LD y hy hp).2.2.2)]
  rw [orbitForest_eq, hrs]
  exact key _ (OUT _ (I0 _ rfl) _ rfl)

theorem labOKK_sound {n w kG m REP LAB DEP PAR GL : Nat} {GS : Nat → Nat}
    {gens : Array (Array Nat)} {reps : Array Nat} (_hw : n + 1 < 2 ^ w)
    (hg : gens.size = kG ∧ ∀ i < kG, gens[i]! = unpack n w (GS i))
    (hc : allN kG (fun i => canonK n w (mask w) (n * w) (GS i)) = true)
    (hr : reps.size = m ∧ ∀ c < m, reps[c]! = pg w (mask w) REP c)
    (h : labOKK n w GS kG m LAB REP DEP PAR GL = true) :
    orbitLabelOK n gens m (unpack n w LAB) reps (unpack n w DEP) (unpack n w PAR)
      (unpack n w GL) = true := by
  obtain ⟨hgs, hgv⟩ := hg
  obtain ⟨-, hrv⟩ := hr
  unfold labOKK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  have hGn := gens_lt hc
  have U : ∀ P y, y < n → (unpack n w P)[y]! = pgW w P y := fun P y hy => by
    rw [unpackW_get hy, pgW_eq]
  have G : ∀ i < kG, ∀ y < n, (gens[i]!)[y]! = pgW w (GS i) y := fun i hi y hy => by
    rw [hgv i hi, U _ y hy]
  have R : ∀ c < m, reps[c]! = pgW w REP c := fun c hc => by rw [hrv c hc, pgW_eq]
  have L : ∀ x < n, pgW w LAB x < m := fun x hx => Nat.blt_eq.mp (allN_spec h1 x hx)
  unfold orbitLabelOK
  simp only [Bool.and_eq_true]
  rw [hgs]
  refine ⟨⟨⟨allLt_of fun x hx => ?_, allLt_of fun i hi => allLt_of fun x hx => ?_⟩,
    allLt_of fun c hc => ?_⟩, allLt_of fun x hx => ?_⟩
  · rw [U LAB x hx]
    exact decide_eq_true (L x hx)
  · rw [G i hi x hx, U LAB _ (hGn i hi x hx), U LAB x hx]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true (allN_spec (allN_spec h2 i hi) x hx))
  · have h5 := allN_spec h3 c hc
    simp only [strictB_eqM] at h5
    obtain ⟨e1, h5⟩ := (bAnd_iff _ _).1 h5
    obtain ⟨e2, e3⟩ := (bAnd_iff _ _).1 h5
    have hrn := Nat.blt_eq.mp e1
    rw [R c hc, U LAB _ hrn, U DEP _ hrn, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3]
    simp [hrn]
  · have h5 := allN_spec h4 x hx
    rcases (bIfT_iff _ _).1 h5 with h5 | h5
    · obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 h5
      rw [Bool.or_eq_true, U DEP x hx, U LAB x hx, R _ (L x hx), Nat.eq_of_beq_eq_true e1,
        Nat.eq_of_beq_eq_true e2]
      simp
    · simp only [strictB_eqM] at h5
      obtain ⟨e1, h5⟩ := (bAnd_iff _ _).1 h5
      obtain ⟨e2, h5⟩ := (bAnd_iff _ _).1 h5
      obtain ⟨e3, h5⟩ := (bAnd_iff _ _).1 h5
      obtain ⟨e4, e5⟩ := (bAnd_iff _ _).1 h5
      have hd := Nat.blt_eq.mp e1
      have hp := Nat.blt_eq.mp e2
      have hg' := Nat.blt_eq.mp e4
      have e3' : pgW w DEP (pgW w PAR x) + 1 = pgW w DEP x := Nat.eq_of_beq_eq_true e3
      rw [Bool.or_eq_true]
      refine Or.inr ?_
      simp only [Bool.and_eq_true, U DEP x hx, U PAR x hx, U GL x hx, U DEP _ hp, G _ hg' _ hp,
        Nat.eq_of_beq_eq_true e5, e3', beq_self_eq_true, decide_eq_true_eq, and_true]
      omega

theorem hexAt_one (b : ByteArray) (o : Nat) : hexAt b o 1 = hexVal (b.get! o) := by
  simp [hexAt]

theorem hexAt_three (b : ByteArray) (o : Nat) :
    hexAt b o 3 = (hexAt b o 1 * 16 + hexAt b (o + 1) 1) * 16 + hexAt b (o + 2) 1 := by
  simp [hexAt]

end CFSG.KS.SporSch

end
