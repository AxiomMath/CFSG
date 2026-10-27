module

public import Certificates.Data.Kernel.BfsTreeK
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.Co1M

open CFSG.KC.BfsT CFSG.Sporadic.Co1.Module.Pairs CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2
  CFSG.KC.Co1F2

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by
  cases a <;> rfl

private theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by
  cases a <;> rfl

private theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem getL_eq (x : Nat) : ∀ (L : List Nat) (k : Nat), getL x L k = L.getD k x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => getL_eq x L k

private theorem getL_lt {L : List Nat} {k : Nat} (hk : k < L.length) : getL 0 L k = L[k] := by
  rw [getL_eq, List.getD_eq_getElem _ _ hk]

private theorem lenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_eq L)

private theorem preK_iff (w : Nat) : ∀ (L : List Nat) (c : Nat), c ≤ L.length →
    (preK L c w = true ↔ ∃ k < c, getL 0 L k = w)
  | [], c, hc => by
    have : c = 0 := by simpa using hc
    subst this
    exact ⟨(fun h => nomatch h), fun ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | y :: L, 0, _ => ⟨(fun h => nomatch h), fun ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | y :: L, c + 1, hc => by
    change CFSG.KLie.CT.orB (Nat.beq y w) (preK L c w) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, Nat.beq_eq, preK_iff w L c (by simp at hc; omega)]
    constructor
    · rintro (h | ⟨k, hk, e⟩)
      · exact ⟨0, Nat.succ_pos _, h⟩
      · exact ⟨k + 1, by omega, e⟩
    · rintro ⟨k, hk, e⟩
      cases k with
      | zero => exact Or.inl e
      | succ k => exact Or.inr ⟨k, by omega, e⟩

private theorem runK_cons (f : Nat → Nat → Nat) (L P B : List Nat) (n x : Nat) (xs : List Nat)
    (h c : Nat) :
    runK f L P B n (x :: xs) h c =
      (decide (h < c) && stepK f L P B n x h 0 c fun c =>
        stepK f L P B n x h 1 c fun c => runK f L P B n xs (h + 1) c) := by
  change strictB h (fun h => strictB c fun c =>
    CFSG.KLie.CT.andB (Nat.blt h c) (stepK f L P B n x h 0 c fun c =>
      stepK f L P B n x h 1 c fun c => runK f L P B n xs (Nat.succ h) c)) = _
  have e : Nat.blt h c = decide (h < c) := by
    rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]
  rw [strictB_eq, strictB_eq, andB_eq, e]

private theorem stepK_cases {f : Nat → Nat → Nat} {L P B : List Nat} {n x h l c : Nat}
    {k : Nat → Bool} (hr : stepK f L P B n x h l c k = true) :
    (preK L c (f l x) = true ∧ k c = true) ∨
      (preK L c (f l x) = false ∧ c < n ∧ getL 0 L c = f l x ∧ getL 0 P c = h ∧
        getL 0 B c = l ∧ k (c + 1) = true) := by
  unfold stepK at hr
  rw [strictB_eq, bIf_eq] at hr
  cases hp : preK L (c) (f l x)
  · rw [hp] at hr
    simp only [Bool.false_eq_true, ↓reduceIte, andB_eq, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq, Nat.succ_eq_add_one] at hr
    exact Or.inr ⟨rfl, hr.1.1, hr.1.2, hr.2.1.1, hr.2.1.2, hr.2.2⟩
  · rw [hp] at hr
    simp only [↓reduceIte] at hr
    exact Or.inl ⟨rfl, hr⟩

private abbrev BSt := Array Nat × Array Nat × Array Nat

private def kInner (f : Nat → Nat → Nat) (h : Nat) (l : Nat) (s : BSt) : Id (ForInStep BSt) :=
  if (!s.1.contains (f l s.1[h]!)) = true then
    pure (.yield (s.1.push (f l s.1[h]!), s.2.1.push h, s.2.2.push l))
  else pure (.yield (s.1, s.2.1, s.2.2))

private def kOuter (f : Nat → Nat → Nat) (h : Nat) (s : BSt) : Id (ForInStep BSt) :=
  if h < s.1.size then do
    let s' ← forIn [0:2] (s.1, s.2.1, s.2.2) (kInner f h)
    pure (.yield (s'.1, s'.2.1, s'.2.2))
  else pure (.done (s.1, s.2.1, s.2.2))

private theorem bfsTree_eq (f : Nat → Nat → Nat) (w0 cap : Nat) :
    bfsTree f w0 cap =
      (let s := (forIn [0:cap] (#[w0], #[0], #[0]) (kOuter f) : Id BSt)
      (s.1, s.2.1, s.2.2)) := rfl

private def AR (a : Array Nat) (c : Nat) (g : Nat → Nat) : Prop :=
  a.size = c ∧ ∀ k < c, a[k]! = g k

private theorem AR_push {a : Array Nat} {c : Nat} {g : Nat → Nat} {v : Nat} (h : AR a c g)
    (hv : g c = v) : AR (a.push v) (c + 1) g := by
  refine ⟨by rw [Array.size_push, h.1], fun k hk => ?_⟩
  rw [getElem!_pos _ k (by rw [Array.size_push, h.1]; exact hk), Array.getElem_push]
  split
  · rename_i hk'
    rw [← getElem!_pos a k hk']
    exact h.2 k (by rw [← h.1]; exact hk')
  · have : k = c := by have := h.1; omega
    rw [this, hv]

private theorem AR_toArray {a : Array Nat} {L : List Nat} (h : AR a L.length (getL 0 L)) :
    a = L.toArray := by
  refine Array.ext (by rw [h.1, List.size_toArray]) fun k h1 h2 => ?_
  have e := h.2 k (by rw [← h.1]; exact h1)
  rw [getElem!_pos a k h1, getL_lt (by simpa using h2)] at e
  rw [e, List.getElem_toArray]

private theorem contains_eq {a : Array Nat} {L : List Nat} {c w : Nat} (h : AR a c (getL 0 L))
    (hc : c ≤ L.length) : a.contains w = preK L c w := by
  apply Bool.eq_iff_iff.2
  rw [Array.contains_iff_mem, Array.mem_iff_getElem, preK_iff w L c hc]
  constructor
  · rintro ⟨k, hk, e⟩
    refine ⟨k, by rw [← h.1]; exact hk, ?_⟩
    rw [← h.2 k (by rw [← h.1]; exact hk), getElem!_pos a k hk, e]
  · rintro ⟨k, hk, e⟩
    have hk' : k < a.size := by rw [h.1]; exact hk
    refine ⟨k, hk', ?_⟩
    rw [← getElem!_pos a k hk', h.2 k hk, e]

private def BInv (L P B : List Nat) (n c : Nat) (s : BSt) : Prop :=
  1 ≤ c ∧ c ≤ n ∧ AR s.1 c (getL 0 L) ∧ AR s.2.1 c (getL 0 P) ∧ AR s.2.2 c (getL 0 B)

private theorem inner_one {f : Nat → Nat → Nat} {L P B : List Nat} {n h l c : Nat} {s : BSt}
    {k : Nat → Bool} (hn : L.length = n) (hI : BInv L P B n c s) (hh : h < c)
    (hr : stepK f L P B n (getL 0 L h) h l c k = true) :
    ∃ c', c ≤ c' ∧ ∃ s', kInner f h l s = pure (.yield s') ∧ BInv L P B n c' s' ∧
      k c' = true := by
  obtain ⟨hc1, hcn, hpts, hpar, hlab⟩ := hI
  have hx : s.1[h]! = getL 0 L h := hpts.2 h hh
  have hct : s.1.contains (f l (getL 0 L h)) = preK L c (f l (getL 0 L h)) :=
    contains_eq hpts (by omega)
  rcases stepK_cases hr with ⟨hp, hk⟩ | ⟨hp, hcn', hLc, hPc, hBc, hk⟩
  · refine ⟨c, Nat.le_refl c, s, ?_, ⟨hc1, hcn, hpts, hpar, hlab⟩, hk⟩
    unfold kInner
    rw [hx, hct, hp]
    rfl
  · refine ⟨c + 1, by omega, (s.1.push (f l (getL 0 L h)), s.2.1.push h, s.2.2.push l), ?_,
      ⟨by omega, hcn', AR_push hpts hLc, AR_push hpar hPc, AR_push hlab hBc⟩, hk⟩
    unfold kInner
    rw [hx, hct, hp]
    rfl

private theorem outer_sim {f : Nat → Nat → Nat} {cap : Nat} {L P B : List Nat} {n : Nat}
    (hn : L.length = n) (hcap : n ≤ cap) :
    ∀ k h c (s : BSt), h + k = cap → BInv L P B n c s →
      runK f L P B n (L.drop h) h c = true →
      BInv L P B n n (forIn (m := Id) (List.range' h k) s (kOuter f)) := by
  have hend : ∀ h c, n ≤ h → runK f L P B n (L.drop h) h c = true → c = n := by
    intro h c hh hr
    rw [List.drop_eq_nil_of_le (by omega)] at hr
    exact Nat.eq_of_beq_eq_true hr
  intro k
  induction k with
  | zero =>
    intro h c s hk hI hr
    have := hend h c (by omega) hr
    subst this
    exact hI
  | succ k ih =>
    intro h c s hk hI hr
    rw [List.range'_succ, List.forIn_cons]
    by_cases hc : h < c
    · have hsz : h < s.1.size := by rw [hI.2.2.1.1]; exact hc
      have hLh : h < L.length := by have := hI.2.1; omega
      rw [List.drop_eq_getElem_cons hLh, ← getL_lt hLh, runK_cons] at hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨-, hr⟩ := hr
      obtain ⟨c1, hc1, s1, hs1, hI1, hr1⟩ := inner_one hn hI hc hr
      obtain ⟨c2, hc2, s2, hs2, hI2, hr2⟩ := inner_one hn hI1 (by omega) hr1
      have hb : kOuter f h s = pure (.yield s2) := by
        unfold kOuter
        rw [ite_eq_left hsz, Std.Legacy.Range.forIn_eq_forIn_range']
        simp only [Std.Legacy.Range.size]
        change (do
          let s' ← forIn (m := Id) [0, 1] (s.1, s.2.1, s.2.2) (kInner f h)
          pure (ForInStep.yield (s'.1, s'.2.1, s'.2.2))) = _
        have e : ((s.1, s.2.1, s.2.2) : BSt) = s := rfl
        rw [e]
        simp only [List.forIn_cons, List.forIn_nil, hs1, hs2, pure_bind]
      rw [hb]
      exact ih (h + 1) c2 s2 (by omega) hI2 hr2
    · have hsz : ¬h < s.1.size := by rw [hI.2.2.1.1]; exact hc
      have hb : kOuter f h s = pure (.done s) := by
        unfold kOuter
        rw [ite_eq_right hsz]
      rw [hb]
      have hnh : n ≤ h := by
        by_contra hlt
        have hLh : h < L.length := by omega
        rw [List.drop_eq_getElem_cons hLh, runK_cons] at hr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
        exact hc hr.1
      have := hend h c hnh hr
      subst this
      exact hI

theorem bfsTree_sound {f : Nat → Nat → Nat} {w0 cap : Nat} {L P B : List Nat}
    (_h : bfsK f w0 cap L P B = true) :
    bfsTree f w0 cap = (L.toArray, P.toArray, B.toArray) := by
  unfold bfsK at _h
  rw [strictB_eq, lenL_eq] at _h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, lenL_eq] at _h
  obtain ⟨⟨⟨hn0, hcap⟩, hPn, hBn⟩, ⟨hL0, hP0, hB0⟩, hrun⟩ := _h
  have hI0 : BInv L P B L.length 1 (#[w0], #[0], #[0]) := by
    refine ⟨Nat.le_refl 1, hn0, ⟨rfl, fun k hk => ?_⟩, ⟨rfl, fun k hk => ?_⟩,
      ⟨rfl, fun k hk => ?_⟩⟩
    · have e : k = 0 := by omega
      subst e
      simp [hL0]
    · have e : k = 0 := by omega
      subst e
      simp [hP0]
    · have e : k = 0 := by omega
      subst e
      simp [hB0]
  have hF := outer_sim (f := f) (P := P) (B := B) rfl hcap cap 0 1 _ (Nat.zero_add cap) hI0
    (by rw [List.drop_zero]; exact hrun)
  generalize hsF : forIn (m := Id) (List.range' 0 cap) (#[w0], #[0], #[0]) (kOuter f) = sF at hF
  obtain ⟨-, -, hpts, hpar, hlab⟩ := hF
  rw [bfsTree_eq]
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hl : List.range' [0:cap].start [0:cap].size [0:cap].step = List.range' 0 cap := by
    simp [Std.Legacy.Range.size]
  have hpar' : AR sF.2.1 P.length (getL 0 P) := by rw [hPn]; exact hpar
  have hlab' : AR sF.2.2 B.length (getL 0 B) := by rw [hBn]; exact hlab
  rw [hl, hsF, AR_toArray hpts, AR_toArray hpar', AR_toArray hlab']

end CFSG.KC.Co1M

end
