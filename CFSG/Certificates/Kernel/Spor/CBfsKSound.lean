module

public import Certificates.Data.Kernel.Spor.CBfsK
public import Certificates.Data.CFSGNative.ONSchreier.Compact
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.CB

open CFSG.KC.Enum CFSG.ONSchreier.Native

private abbrev CSt := Array Nat × Array Nat × Array Nat × Array Nat

private def cInner (n : Nat) (st : Array (Array Nat)) (x h : Nat) (j : Nat) (s : CSt) :
    Id (ForInStep CSt) :=
  if (s.1[st[j]![x]!]! == n) = true then
    pure (.yield (s.1.set! st[j]![x]! s.2.1.size, s.2.1.push st[j]![x]!, s.2.2.1.push h,
      s.2.2.2.push j))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private def cOuter (n : Nat) (st : Array (Array Nat)) (h : Nat) (s : CSt) : Id (ForInStep CSt) :=
  if h < s.2.1.size then do
    let s' ← forIn [0:st.size] (s.1, s.2.1, s.2.2.1, s.2.2.2) (cInner n st s.2.1[h]! h)
    pure (.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2))
  else pure (.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

private theorem cbfs_eq (n root : Nat) (st : Array (Array Nat)) :
    cbfs n root st =
      (let s := (forIn [0:n] ((Array.replicate n n).set! root 0, #[root], #[0], #[0])
        (cOuter n st) : Id CSt)
      ⟨s.2.1, s.1, s.2.2.1, s.2.2.2⟩) := rfl

private theorem forIn_inv {β : Type} (R : Nat → β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    ∀ k a (init : β), a + k ≤ E → R a init → R (a + k) (forIn (List.range' a k) init f)
  | 0, _, _, _, h => h
  | k + 1, a, init, hE, h => by
    obtain ⟨b', hb, hR⟩ := hf a init (by omega) h
    rw [List.range'_succ, List.forIn_cons, hb]
    have e : a + (k + 1) = a + 1 + k := by omega
    rw [e]
    exact forIn_inv R E f hf k (a + 1) b' (by omega) hR

private theorem forIn_brk {β : Type} (P : Nat → β → Prop) (Q : β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ h b, h < E → P h b →
      (∃ b', f h b = pure (.yield b') ∧ P (h + 1) b') ∨ (∃ b', f h b = pure (.done b') ∧ Q b'))
    (hE : ∀ b, P E b → Q b) :
    ∀ k a (init : β), a + k = E → P a init → Q (forIn (List.range' a k) init f)
  | 0, a, init, hk, h => by
    have e : a = E := hk
    subst e
    exact hE init h
  | k + 1, a, init, hk, h => by
    rcases hf a init (by omega) h with ⟨b', hb, hP⟩ | ⟨b', hb, hQ⟩
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact forIn_brk P Q E f hf hE k (a + 1) b' (by omega) hP
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact hQ

private theorem strictB_eqC (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bIf_true_iff (c e : Bool) :
    Bool.rec (motive := fun _ => Bool) e true c = true ↔ c = true ∨ e = true := by
  cases c <;> simp

private theorem lexLt_iff (a b c d : Nat) : lexLt a b c d = true ↔ a < c ∨ (a = c ∧ b < d) := by
  unfold lexLt
  rw [bIf_true_iff, CFSG.KS.bAnd_iff]
  simp only [Nat.blt_eq, Nat.beq_eq]

private theorem lex_key {a b c d r : Nat} (hb : b < r) (hd : d < r) :
    (a < c ∨ (a = c ∧ b < d)) ↔ a * r + b < c * r + d := by
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · have : (a + 1) * r ≤ c * r := Nat.mul_le_mul_right r h
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · omega
  · intro h
    rcases Nat.lt_trichotomy a c with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h1, by subst h1; omega⟩
    · have : (c + 1) * r ≤ a * r := Nat.mul_le_mul_right r h1
      rw [Nat.add_mul, Nat.one_mul] at this
      omega

private theorem key_inj {a b c d r : Nat} (hb : b < r) (hd : d < r) (h : a * r + b = c * r + d) :
    a = c ∧ b = d := by
  rcases Nat.lt_trichotomy a c with h1 | h1 | h1
  · have := (lex_key hb hd).1 (Or.inl h1)
    omega
  · subst h1
    exact ⟨rfl, by omega⟩
  · have := (lex_key hd hb).1 (Or.inl h1)
    omega

private theorem head_facts {n m root : Nat} {PTS PAR LAB : Nat → Nat}
    (h : cbHead n m root PTS PAR LAB = true) :
    0 < m ∧ m ≤ n ∧ PTS 0 = root ∧ PAR 0 = 0 ∧ LAB 0 = 0 := by
  unfold cbHead at h
  simp only [CFSG.KS.bAnd_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  exact h

private theorem pos_facts {n m z : Nat} {PTS POS : Nat → Nat} (h : cbPos n m PTS POS z = true) :
    POS z = n ∨ (POS z < m ∧ PTS (POS z) = z) := by
  unfold cbPos at h
  simp only [strictB_eqC, bIf_true_iff, CFSG.KS.bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

private theorem pt_facts {n m r k : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : cbPt n m r STEP PTS POS PAR LAB k = true) :
    PTS k < n ∧ POS (PTS k) = k ∧
      (k ≠ 0 → PAR k < k ∧ LAB k < r ∧ STEP (LAB k) (PTS (PAR k)) = PTS k) ∧
      (k ≠ 0 → k + 1 < m → lexLt (PAR k) (LAB k) (PAR (k + 1)) (LAB (k + 1)) = true) ∧
      (∀ j < r, STEP j (PTS k) < n ∧ POS (STEP j (PTS k)) < m ∧
        (POS (STEP j (PTS k)) ≠ 0 →
          lexLt k j (PAR (POS (STEP j (PTS k)))) (LAB (POS (STEP j (PTS k)))) = false)) := by
  unfold cbPt at h
  simp only [strictB_eqC] at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2, fun hk => ?_, fun hk hk1 => ?_,
    fun j hj => ?_⟩
  · rcases (bIf_true_iff _ _).1 h3 with h3 | h3
    · exact absurd (Nat.eq_of_beq_eq_true h3) hk
    · simp only [CFSG.KS.bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h3
      exact h3
  · rcases (bIf_true_iff _ _).1 h4 with h4 | h4
    · exact absurd (Nat.eq_of_beq_eq_true h4) hk
    · have hb : Nat.blt (k + 1) m = true := Nat.blt_eq.mpr hk1
      rw [Nat.succ_eq_add_one, hb] at h4
      exact h4
  · have h6 := CFSG.KS.allN_spec h5 j hj
    obtain ⟨h7, h6⟩ := (CFSG.KS.bAnd_iff _ _).1 h6
    obtain ⟨h8, h6⟩ := (CFSG.KS.bAnd_iff _ _).1 h6
    refine ⟨Nat.le_of_ble_eq_true h7, Nat.le_of_ble_eq_true h8, fun hk => ?_⟩
    rcases (bIf_true_iff _ _).1 h6 with h6 | h6
    · exact absurd (Nat.eq_of_beq_eq_true h6) hk
    · simpa using h6

private theorem set_getC {a : Array Nat} {i j : Nat} {v : Nat} (hi : i < a.size) :
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

private def AR (a : Array Nat) (c : Nat) (f : Nat → Nat) : Prop :=
  a.size = c ∧ ∀ k < c, a[k]! = f k

private theorem AR_push {a : Array Nat} {c : Nat} {f : Nat → Nat} {v : Nat} (h : AR a c f)
    (hv : f c = v) : AR (a.push v) (c + 1) f := by
  refine ⟨by rw [Array.size_push, h.1], fun k hk => ?_⟩
  rw [getElem!_pos _ k (by rw [Array.size_push, h.1]; exact hk), Array.getElem_push]
  split
  · rename_i hk'
    rw [← getElem!_pos a k hk']
    exact h.2 k (by rw [← h.1]; exact hk')
  · have : k = c := by have := h.1; omega
    rw [this, hv]

private theorem AR_eq {a : Array Nat} {c : Nat} {f : Nat → Nat} (h : AR a c f) :
    a = Array.ofFn (n := c) fun k => f k.val := by
  refine Array.ext (by rw [h.1, Array.size_ofFn]) fun k h1 _ => ?_
  have := h.2 k (by rw [← h.1]; exact h1)
  rw [getElem!_pos a k h1] at this
  rw [this, Array.getElem_ofFn]

private def CInv (n m r : Nat) (PTS POS PAR LAB : Nat → Nat) (t : Nat) (s : CSt) : Prop :=
  ∃ c, 1 ≤ c ∧ c ≤ m ∧ AR s.2.1 c PTS ∧ AR s.2.2.1 c PAR ∧ AR s.2.2.2 c LAB ∧ s.1.size = n ∧
    (∀ z < n, s.1[z]! = if POS z < c then POS z else n) ∧
    (∀ k, 1 ≤ k → k < m → (k < c ↔ PAR k * r + LAB k < t))

theorem cbfsK_sound {n m r root : Nat} {st : Array (Array Nat)} {STEP : Nat → Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat}
    (hst : st.size = r ∧ ∀ j < r, ∀ x < n, st[j]![x]! = STEP j x)
    (hh : cbHead n m root PTS PAR LAB = true)
    (hp : ∀ k < m, cbPt n m r STEP PTS POS PAR LAB k = true)
    (hz : ∀ z < n, cbPos n m PTS POS z = true) :
    cbfs n root st = ⟨Array.ofFn (n := m) fun k => PTS k.val, Array.ofFn (n := n) fun z => POS z.val,
      Array.ofFn (n := m) fun k => PAR k.val, Array.ofFn (n := m) fun k => LAB k.val⟩ := by
  obtain ⟨hsz, hstv⟩ := hst
  obtain ⟨hm0, hmn, hroot, hpar0, hlab0⟩ := head_facts hh
  have P := fun k (hk : k < m) => pt_facts (hp k hk)
  have Z := fun z (hz' : z < n) => pos_facts (hz z hz')
  have Kstep : ∀ k, 1 ≤ k → k + 1 < m →
      PAR k * r + LAB k < PAR (k + 1) * r + LAB (k + 1) := fun k hk hk1 => by
    have h1 := (P k (by omega)).2.2.1 (by omega)
    have h2 := (P (k + 1) hk1).2.2.1 (by omega)
    exact (lex_key h1.2.1 h2.2.1).1
      ((lexLt_iff _ _ _ _).1 ((P k (by omega)).2.2.2.1 (by omega) hk1))
  have Kmono : ∀ k k', 1 ≤ k → k < k' → k' < m →
      PAR k * r + LAB k < PAR k' * r + LAB k' := by
    intro k k' hk hkk hk'
    induction k' with
    | zero => omega
    | succ k' ih =>
      rcases Nat.lt_or_ge k k' with h | h
      · exact Nat.lt_trans (ih h (by omega)) (Kstep k' (by omega) hk')
      · have e : k = k' := by omega
        rw [e] at hk ⊢
        exact Kstep k' hk hk'
  have hfin : ∀ t s, CInv n m r PTS POS PAR LAB t s →
      (∀ c, AR s.2.1 c PTS → c * r ≤ t) →
      AR s.2.1 m PTS ∧ AR s.2.2.1 m PAR ∧ AR s.2.2.2 m LAB ∧ s.1.size = n ∧
        ∀ z < n, s.1[z]! = POS z := by
    intro t s ⟨c, hc1, hcm, hpts, hpar, hlab, hps, hpos, hord⟩ hct
    have hc : c = m := by
      by_contra hne
      have hc' : c < m := by omega
      obtain ⟨hpc, hlc, -⟩ := (P c hc').2.2.1 (by omega)
      have h1 : (PAR c + 1) * r ≤ c * r := Nat.mul_le_mul_right r hpc
      rw [Nat.add_mul, Nat.one_mul] at h1
      have h2 := hct c hpts
      have := (hord c hc1 hc').2 (by omega)
      omega
    subst hc
    refine ⟨hpts, hpar, hlab, hps, fun z hz' => ?_⟩
    rw [hpos z hz']
    rcases Z z hz' with h | h
    · rw [h, ite_eq_right (by omega)]
    · rw [ite_eq_left h.1]
  have hinner : ∀ h (b : CSt), h < n → CInv n m r PTS POS PAR LAB (h * r) b → h < b.2.1.size →
      ∀ k, k = r → CInv n m r PTS POS PAR LAB ((h + 1) * r)
        (forIn (m := Id) (List.range' 0 k) b (cInner n st b.2.1[h]! h)) := by
    intro h b hn hb hc k hk
    subst hk
    obtain ⟨c0, -, hc0m, hpts0, -⟩ := id hb
    have hx : b.2.1[h]! = PTS h := hpts0.2 h (by rw [← hpts0.1]; exact hc)
    have hhm : h < m := by have := hpts0.1; omega
    rw [hx]
    have e : (h + 1) * k = h * k + (0 + k) := by rw [Nat.add_mul, Nat.one_mul, Nat.zero_add]
    rw [e]
    refine forIn_inv (fun j s => CInv n m k PTS POS PAR LAB (h * k + j) s) k _ ?_ k 0 b
      (by omega) hb
    intro j s hj hs
    obtain ⟨c, hc1, hcm, hpts, hpar, hlab, hps, hpos, hord⟩ := hs
    have hPh := P h hhm
    obtain ⟨hyn, hkm, hklex⟩ := hPh.2.2.2.2 j hj
    have hy : st[j]![PTS h]! = STEP j (PTS h) := hstv j (by omega) (PTS h) hPh.1
    generalize hydef : STEP j (PTS h) = y at hy hyn hkm hklex
    have hPy : PTS (POS y) = y := by
      rcases Z y hyn with h' | h'
      · omega
      · exact h'.2
    unfold cInner
    rw [hy, hpos y hyn]
    by_cases hkc : POS y < c
    · rw [ite_eq_left hkc]
      have hne : (POS y == n) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      rw [hne, ite_eq_right Bool.false_ne_true]
      refine ⟨_, rfl, c, hc1, hcm, hpts, hpar, hlab, hps, hpos, fun k' hk1 hkm' => ?_⟩
      rw [hord k' hk1 hkm']
      constructor
      · intro h'
        omega
      · intro h'
        rcases Nat.lt_or_ge (PAR k' * k + LAB k') (h * k + j) with h2 | h2
        · exact h2
        · exfalso
          have heq : PAR k' * k + LAB k' = h * k + j := by omega
          obtain ⟨-, hlk, hsk⟩ := (P k' hkm').2.2.1 (by omega)
          obtain ⟨e1, e2⟩ := key_inj hlk hj heq
          have hk'y : PTS k' = y := by rw [← hsk, e1, e2, hydef]
          have hk' : POS y = k' := by rw [← hk'y]; exact (P k' hkm').2.1
          rw [hk'] at hkc
          have := (hord k' hk1 hkm').1 hkc
          omega
    · rw [ite_eq_right hkc, ite_eq_left (beq_self_eq_true n)]
      have hk0 : POS y ≠ 0 := by omega
      have hlexf := hklex hk0
      obtain ⟨-, hlk, -⟩ := (P (POS y) hkm).2.2.1 hk0
      have hle : PAR (POS y) * k + LAB (POS y) ≤ h * k + j := by
        by_contra hgt
        have h3 := (lex_key (a := h) (c := PAR (POS y)) hj hlk).2 (by omega)
        rw [← lexLt_iff, hlexf] at h3
        exact Bool.false_ne_true h3
      have hge : ¬ PAR (POS y) * k + LAB (POS y) < h * k + j := fun h' =>
        hkc ((hord _ (by omega) hkm).2 h')
      have hKeq : PAR (POS y) * k + LAB (POS y) = h * k + j := by omega
      have hkc' : POS y = c := by
        by_contra hne
        have hlt : c < POS y := by omega
        have h3 := Kmono c (POS y) hc1 hlt hkm
        have h4 := (hord c hc1 (by omega)).2 (by omega)
        omega
      rw [hkc'] at hKeq hlk hkm
      obtain ⟨e1, e2⟩ := key_inj hlk hj hKeq
      refine ⟨_, rfl, c + 1, by omega, by omega, AR_push hpts (by rw [← hkc', hPy]),
        AR_push hpar e1, AR_push hlab e2, by simp [hps], fun z hz' => ?_, fun k' hk1 hkm' => ?_⟩
      · dsimp only
        rw [set_getC (by rw [hps]; exact hyn), hpts.1]
        by_cases hzy : z = y
        · rw [ite_eq_left hzy, hzy, hkc', ite_eq_left (by omega)]
        · rw [ite_eq_right hzy, hpos z hz']
          have hzc : POS z ≠ c := by
            intro e'
            rcases Z z hz' with h' | h'
            · omega
            · exact hzy (by rw [← h'.2, e', ← hkc', hPy])
          by_cases h3 : POS z < c
          · rw [ite_eq_left h3, ite_eq_left (by omega)]
          · rw [ite_eq_right h3, ite_eq_right (by omega)]
      · constructor
        · intro hk'
          rcases Nat.lt_or_ge k' c with h3 | h3
          · have := (hord k' hk1 hkm').1 h3
            omega
          · have e' : k' = c := by omega
            rw [e']
            omega
        · intro hk'
          by_contra h3
          have h4 := Kmono c k' hc1 (by omega) hkm'
          omega
  have key : ∀ s : CSt, (AR s.2.1 m PTS ∧ AR s.2.2.1 m PAR ∧ AR s.2.2.2 m LAB ∧ s.1.size = n ∧
      ∀ z < n, s.1[z]! = POS z) →
      (⟨s.2.1, s.1, s.2.2.1, s.2.2.2⟩ : CLevel) = ⟨Array.ofFn (n := m) fun k => PTS k.val,
        Array.ofFn (n := n) fun z => POS z.val, Array.ofFn (n := m) fun k => PAR k.val,
        Array.ofFn (n := m) fun k => LAB k.val⟩ := by
    intro s ⟨h1, h2, h3, h4, h5⟩
    simp only [CLevel.mk.injEq]
    refine ⟨AR_eq h1, Array.ext (by rw [h4, Array.size_ofFn]) fun z hz1 _ => ?_, AR_eq h2, AR_eq h3⟩
    rw [← getElem!_pos s.1 z hz1, h5 z (by omega), Array.getElem_ofFn]
  rw [cbfs_eq]
  refine key _ ?_
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hroot' : root < n := hroot ▸ (P 0 hm0).1
  have hl : List.range' [0:n].start [0:n].size [0:n].step = List.range' 0 n := by
    simp [Std.Legacy.Range.size]
  rw [hl]
  refine forIn_brk (fun h s => CInv n m r PTS POS PAR LAB (h * r) s)
    (fun s : CSt => AR s.2.1 m PTS ∧ AR s.2.2.1 m PAR ∧ AR s.2.2.2 m LAB ∧ s.1.size = n ∧
      ∀ z < n, s.1[z]! = POS z) n (cOuter n st)
    (fun h b hn hb => ?_) (fun b hb => ?_) n 0 _ (Nat.zero_add n) ?_
  · by_cases hc : h < b.2.1.size
    · refine Or.inl ⟨_, by unfold cOuter; rw [ite_eq_left hc]; rfl, ?_⟩
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact hinner h b hn hb hc _ (by simp [Std.Legacy.Range.size, hsz])
    · refine Or.inr ⟨_, by unfold cOuter; rw [ite_eq_right hc], ?_⟩
      exact hfin (h * r) b hb fun c hcAR => Nat.mul_le_mul_right r (by rw [← hcAR.1]; omega)
  · refine hfin (n * r) b hb fun c hcAR => Nat.mul_le_mul_right r ?_
    obtain ⟨c', -, hc'm, hpts, -⟩ := hb
    rw [← hcAR.1, hpts.1]
    omega
  · refine ⟨1, Nat.le_refl 1, hm0, ⟨rfl, fun k hk => ?_⟩, ⟨rfl, fun k hk => ?_⟩,
      ⟨rfl, fun k hk => ?_⟩, by simp, fun z hz' => ?_, fun k hk1 hkm => ?_⟩
    · have e : k = 0 := by omega
      subst e
      simp [hroot]
    · have e : k = 0 := by omega
      subst e
      simp [hpar0]
    · have e : k = 0 := by omega
      subst e
      simp [hlab0]
    · dsimp only
      rw [set_getC (by simpa using hroot')]
      by_cases hzr : z = root
      · rw [ite_eq_left hzr]
        have e : POS z = 0 := by rw [hzr, ← hroot]; exact (P 0 hm0).2.1
        rw [e, ite_eq_left Nat.one_pos]
      · rw [ite_eq_right hzr, getElem!_pos _ z (by simpa using hz'), Array.getElem_replicate]
        rcases Z z hz' with h' | h'
        · rw [h', ite_eq_right (by omega)]
        · have e : POS z ≠ 0 := fun e => hzr (by rw [← h'.2, e, hroot])
          rw [ite_eq_right (by omega)]
    · constructor
      · intro h'
        omega
      · intro h'
        simp at h'

theorem set_loop {N v : Nat} {D : Array Nat} :
    ∀ {m : Nat}, (∀ i < m, D[i]! < N) → (∀ i < m, ∀ j < i, D[j]! ≠ D[i]!) →
      ((List.range' 0 m).foldl (fun p i => p.set! D[i]! i) (Array.replicate N v)).size = N ∧
      ∀ i < m, ((List.range' 0 m).foldl (fun p i => p.set! D[i]! i) (Array.replicate N v))[D[i]!]! = i
  | 0, _, _ => ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | m + 1, hD, hd => by
    obtain ⟨hs, hv⟩ := set_loop (N := N) (v := v) (D := D) (m := m) (fun i hi => hD i (by omega))
      (fun i hi j hj => hd i (by omega) j hj)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add]
    generalize (List.range' 0 m).foldl (fun p i => p.set! D[i]! i) (Array.replicate N v) = q at hs hv
    have hm : D[m]! < N := hD m (by omega)
    have hsz : (q.set! D[m]! m).size = N := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs]
    refine ⟨hsz, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i m with h | h
    · have hne : D[i]! ≠ D[m]! := fun e => hd m (by omega) i h e
      have hi' : D[i]! < N := hD i (by omega)
      rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simp [hs]; omega),
        Array.getElem_setIfInBounds_ne (by rw [hs]; exact hi') (Ne.symm hne),
        ← getElem!_pos q _ (by rw [hs]; exact hi')]
      exact hv i h
    · have e : i = m := by omega
      subst e
      rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simp [hs]; omega),
        Array.getElem_setIfInBounds_self]

theorem pinvCand_get {n : Nat} {T U : Nat → Nat} (hT : ∀ x < n, T x < n)
    (hUT : ∀ x < n, U (T x) = x) {y : Nat} (hy : y < n) :
    (pinvCand n (Array.ofFn (n := n) fun i => T i.val))[y]! = U y := by
  have hget : ∀ i < n, (Array.ofFn (n := n) fun i => T i.val)[i]! = T i := fun i hi => by
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have hD : ∀ i < n, (Array.ofFn (n := n) fun i => T i.val)[i]! < n := fun i hi => by
    rw [hget i hi]
    exact hT i hi
  have hd : ∀ i < n, ∀ j < i, (Array.ofFn (n := n) fun i => T i.val)[j]! ≠
      (Array.ofFn (n := n) fun i => T i.val)[i]! := fun i hi j hj e => by
    rw [hget i hi, hget j (by omega)] at e
    have := congrArg U e
    rw [hUT j (by omega), hUT i hi] at this
    omega
  have heq : pinvCand n (Array.ofFn (n := n) fun i => T i.val) =
      (List.range' 0 n).foldl (fun p i => p.set! (Array.ofFn (n := n) fun i => T i.val)[i]! i)
        (Array.replicate n 0) := by
    unfold pinvCand
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  let f : Fin n → Fin n := fun x => ⟨T x.val, hT x.val x.isLt⟩
  have hinj : Function.Injective f := fun a b e => by
    have e' : T a.val = T b.val := congrArg Fin.val e
    have := congrArg U e'
    rw [hUT a.val a.isLt, hUT b.val b.isLt] at this
    exact Fin.ext this
  obtain ⟨x, hx⟩ := (Finite.surjective_of_injective hinj) ⟨y, hy⟩
  have hTx : T x.val = y := congrArg Fin.val hx
  have hxy : U y = x.val := by rw [← hTx, hUT x.val x.isLt]
  rw [heq, ← hTx, ← hget x.val x.isLt, (set_loop hD hd).2 x.val x.isLt, hget x.val x.isLt, hTx, hxy]

end CFSG.KS.CB

end
