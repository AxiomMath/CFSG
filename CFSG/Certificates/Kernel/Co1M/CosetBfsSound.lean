module

public import Certificates.Data.Kernel.CosetBfsK
public import CFSG.Monster.GMS.S365CosetInputs
public import CFSG.Certificates.Kernel.Co1BMulSound
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.Co1M

open CFSG.KC.BfsT CFSG.KC.Co1F2 CFSG.Sporadic.Co1.S365Native CFSG.KC.Loop CFSG.KLie.CT
  CFSG.KC.M1F2 CFSG.Sporadic.SmallF2.Native

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by
  cases a <;> rfl

private theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by
  cases a <;> rfl

private theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.one_shiftLeft]

private theorem getL_eq_bfs (x : Nat) : ∀ (L : List Nat) (k : Nat), getL x L k = L.getD k x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => getL_eq_bfs x L k

private theorem getL_lt {L : List Nat} {k : Nat} (hk : k < L.length) : getL 0 L k = L[k] := by
  rw [getL_eq_bfs, List.getD_eq_getElem _ _ hk]

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

private theorem preK_succ {L : List Nat} {c w : Nat} (hc : c < L.length) :
    preK L (c + 1) w = true ↔ preK L c w = true ∨ getL 0 L c = w := by
  rw [preK_iff w L (c + 1) hc, preK_iff w L c (by omega)]
  constructor
  · rintro ⟨k, hk, e⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · exact Or.inl ⟨k, h, e⟩
    · exact Or.inr (h ▸ e)
  · rintro (⟨k, hk, e⟩ | e)
    · exact ⟨k, by omega, e⟩
    · exact ⟨c, Nat.lt_succ_self c, e⟩

private theorem canon_eq (x y M v : Nat) :
    canon4 x y (vecMulN 24 (unpackR 24 M) v) = canonK x y (vmF 24 M v) := by
  rw [CFSG.KC.F2W.vecMulN_unpackR]
  unfold canon4 canonK minK
  simp only [nIf_eq, Nat.ble_eq, Nat.min_def]
  rfl

private theorem runC_cons (Ms : List Nat) (x0 y0 cap : Nat) (L P B : List Nat) (n v : Nat)
    (xs : List Nat) (h c : Nat) :
    runC Ms x0 y0 cap L P B n (v :: xs) h c =
      if h < cap ∧ h < c then
        lettersC x0 y0 L P B n v h Ms 0 c fun c => runC Ms x0 y0 cap L P B n xs (h + 1) c
      else Nat.beq c n := by
  change strictB h (fun h => strictB c fun c =>
    Bool.rec (motive := fun _ => Bool) (Nat.beq c n)
      (lettersC x0 y0 L P B n v h Ms 0 c fun c => runC Ms x0 y0 cap L P B n xs (Nat.succ h) c)
      (CFSG.KLie.CT.andB (Nat.blt h cap) (Nat.blt h c))) = _
  rw [strictB_eq, strictB_eq, bIf_eq, andB_eq]
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.succ_eq_add_one]

private theorem runC_end {Ms : List Nat} {x0 y0 cap : Nat} {L P B : List Nat} {n : Nat}
    {xs : List Nat} {h c : Nat} (hr : runC Ms x0 y0 cap L P B n xs h c = true)
    (hh : cap ≤ h ∨ c ≤ h) : c = n := by
  cases xs with
  | nil => exact Nat.eq_of_beq_eq_true hr
  | cons v xs =>
    rw [runC_cons, ite_eq_right (by omega)] at hr
    exact Nat.eq_of_beq_eq_true hr

private theorem lettersC_cons {x0 y0 : Nat} {L P B : List Nat} {n v h M : Nat} {Ms : List Nat}
    {l c : Nat} {k : Nat → Bool} (hr : lettersC x0 y0 L P B n v h (M :: Ms) l c k = true) :
    canonK x0 y0 (vmF 24 M v) < 2 ^ 24 ∧
      ((preK L c (canonK x0 y0 (vmF 24 M v)) = true ∧
          lettersC x0 y0 L P B n v h Ms (l + 1) c k = true) ∨
        (preK L c (canonK x0 y0 (vmF 24 M v)) = false ∧ c < n ∧
          getL 0 L c = canonK x0 y0 (vmF 24 M v) ∧ getL 0 P c = h ∧ getL 0 B c = l ∧
          lettersC x0 y0 L P B n v h Ms (l + 1) (c + 1) k = true)) := by
  change strictB l (fun l => strictB c fun c =>
    strictB (canonK x0 y0 (vmF 24 M v)) fun w =>
      CFSG.KLie.CT.andB (Nat.blt w (pw2 24))
        (Bool.rec (motive := fun _ => Bool)
          (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.blt c n) (Nat.beq (getL 0 L c) w))
            (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (getL 0 P c) h) (Nat.beq (getL 0 B c) l))
              (lettersC x0 y0 L P B n v h Ms (Nat.succ l) (Nat.succ c) k)))
          (lettersC x0 y0 L P B n v h Ms (Nat.succ l) c k) (preK L c w))) = true at hr
  rw [strictB_eq, strictB_eq, strictB_eq, bIf_eq, andB_eq, pw2_eq] at hr
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.succ_eq_add_one] at hr
  obtain ⟨hw, hr⟩ := hr
  refine ⟨hw, ?_⟩
  cases hp : preK L c (canonK x0 y0 (vmF 24 M v))
  · rw [hp] at hr
    simp only [Bool.false_eq_true, ↓reduceIte, andB_eq, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at hr
    exact Or.inr ⟨rfl, hr.1.1, hr.1.2, hr.2.1.1, hr.2.1.2, hr.2.2⟩
  · rw [hp] at hr
    simp only [↓reduceIte] at hr
    exact Or.inl ⟨rfl, hr⟩

private abbrev KSt := Array UInt8 × Array Nat × Array Nat × Array Nat

private def kInner (Mts : Array (Array Nat)) (x y v h : Nat) (l : Nat) (s : KSt) :
    Id (ForInStep KSt) :=
  if (s.1[canon4 x y (vecMulN 24 Mts[l]! v)]! == 0) = true then
    pure (.yield (s.1.set! (canon4 x y (vecMulN 24 Mts[l]! v)) 1,
      s.2.1.push (canon4 x y (vecMulN 24 Mts[l]! v)), s.2.2.1.push h, s.2.2.2.push l))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private def kOuter (Mts : Array (Array Nat)) (x y : Nat) (h : Nat) (s : KSt) :
    Id (ForInStep KSt) :=
  if h < s.2.1.size then do
    let s' ← forIn [0:Mts.size] (s.1, s.2.1, s.2.2.1, s.2.2.2) (kInner Mts x y s.2.1[h]! h)
    pure (.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2))
  else pure (.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

private theorem cosetBFS_eq (Mts : Array (Array Nat)) (x y c0 cap : Nat) :
    cosetBFS Mts x y c0 cap =
      (let s := (forIn [0:cap] ((Array.replicate (1 <<< 24) 0).set! c0 1, #[c0], #[0], #[0])
        (kOuter Mts x y) : Id KSt)
      (s.2.1, s.2.2.1, s.2.2.2)) := rfl

private theorem set_getU {a : Array UInt8} {i j : Nat} {v : UInt8} (hi : i < a.size) :
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

private theorem AR_toArray {a : Array Nat} {L : List Nat} (h : AR a L.length (getL 0 L)) :
    a = L.toArray := by
  refine Array.ext (by rw [h.1, List.size_toArray]) fun k h1 h2 => ?_
  have e := h.2 k (by rw [← h.1]; exact h1)
  rw [getElem!_pos a k h1, getL_lt (by simpa using h2)] at e
  rw [e, List.getElem_toArray]

private def KInv (Ms : List Nat) (x y : Nat) (L P B : List Nat) (n c : Nat) (s : KSt) : Prop :=
  1 ≤ c ∧ c ≤ n ∧ AR s.2.1 c (getL 0 L) ∧ AR s.2.2.1 c (getL 0 P) ∧ AR s.2.2.2 c (getL 0 B) ∧
    s.1.size = 2 ^ 24 ∧ (∀ w < 2 ^ 24, (s.1[w]! = 0 ↔ preK L c w = false)) ∧
    (∀ k < c, getL 0 L k < 2 ^ 24) ∧ (∀ j < c, ∀ i < j, getL 0 L i ≠ getL 0 L j) ∧
    (∀ k < c, k ≠ 0 → getL 0 P k < k ∧ getL 0 B k < Ms.length ∧
      getL 0 L k = canonK x y (vmF 24 (getL 0 Ms (getL 0 B k)) (getL 0 L (getL 0 P k))))

private theorem Mts_get {Ms : List Nat} {l : Nat} (hl : l < Ms.length) :
    (Ms.map (unpackR 24)).toArray[l]! = unpackR 24 (getL 0 Ms l) := by
  rw [getElem!_pos _ l (by simpa using hl), List.getElem_toArray, List.getElem_map, getL_lt hl]

private theorem inner_sim {Ms : List Nat} {x y : Nat} {L P B : List Nat} {n h : Nat}
    (hn : L.length = n) :
    ∀ j l c (s : KSt) (k : Nat → Bool), l + j = Ms.length → KInv Ms x y L P B n c s → h < c →
      lettersC x y L P B n (getL 0 L h) h (Ms.drop l) l c k = true →
      ∃ c', c ≤ c' ∧ KInv Ms x y L P B n c'
        (forIn (m := Id) (List.range' l j) s
          (kInner (Ms.map (unpackR 24)).toArray x y (getL 0 L h) h)) ∧ k c' = true := by
  intro j
  induction j with
  | zero =>
    intro l c s k hl hI _ hk
    rw [Nat.add_zero] at hl
    rw [hl, List.drop_length] at hk
    exact ⟨c, Nat.le_refl c, hI, hk⟩
  | succ j ih =>
    intro l c s k hl hI hh hk
    have hlm : l < Ms.length := by omega
    rw [List.drop_eq_getElem_cons hlm, ← getL_lt hlm] at hk
    obtain ⟨hw, hcase⟩ := lettersC_cons hk
    have hw' : canon4 x y (vecMulN 24 (Ms.map (unpackR 24)).toArray[l]! (getL 0 L h)) =
        canonK x y (vmF 24 (getL 0 Ms l) (getL 0 L h)) := by
      rw [Mts_get hlm, canon_eq]
    generalize hwd : canonK x y (vmF 24 (getL 0 Ms l) (getL 0 L h)) = w at hw' hw hcase
    obtain ⟨hc1, hcn, hpts, hpar, hlab, hvs, hvis, hlt, hdis, htree⟩ := hI
    rw [List.range'_succ, List.forIn_cons]
    rcases hcase with ⟨hp, hk'⟩ | ⟨hp, hcn', hLc, hPc, hBc, hk'⟩
    · have hb : kInner (Ms.map (unpackR 24)).toArray x y (getL 0 L h) h l s =
          pure (.yield s) := by
        unfold kInner
        rw [hw']
        have hne : (s.1[w]! == 0) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          rw [(hvis w hw).1 e] at hp
          exact Bool.false_ne_true hp
        rw [hne]
        rfl
      rw [hb]
      exact ih (l + 1) c s k (by omega)
        ⟨hc1, hcn, hpts, hpar, hlab, hvs, hvis, hlt, hdis, htree⟩ hh hk'
    · have hb : kInner (Ms.map (unpackR 24)).toArray x y (getL 0 L h) h l s =
          pure (.yield (s.1.set! w 1, s.2.1.push w, s.2.2.1.push h, s.2.2.2.push l)) := by
        unfold kInner
        rw [hw']
        have he : (s.1[w]! == 0) = true := by
          rw [beq_iff_eq]
          exact (hvis w hw).2 hp
        rw [he]
        rfl
      rw [hb]
      have hLn : c < L.length := by omega
      have hI' : KInv Ms x y L P B n (c + 1)
          (s.1.set! w 1, s.2.1.push w, s.2.2.1.push h, s.2.2.2.push l) := by
        refine ⟨by omega, hcn', AR_push hpts hLc, AR_push hpar hPc, AR_push hlab hBc,
          by simp [hvs], fun w' hw'' => ?_, fun k' hk'' => ?_, fun j' hj' i' hi' => ?_,
          fun k' hk'' hk0 => ?_⟩
        · dsimp only
          rw [set_getU (by rw [hvs]; exact hw)]
          by_cases hww : w' = w
          · rw [ite_eq_left hww]
            have : preK L (c + 1) w' = true := (preK_succ hLn).2 (Or.inr (hLc.trans hww.symm))
            rw [this]
            exact ⟨fun e => absurd e (by decide), fun e => nomatch e⟩
          · rw [ite_eq_right hww, hvis w' hw'']
            have e : preK L (c + 1) w' = preK L c w' := by
              apply Bool.eq_iff_iff.2
              rw [preK_succ hLn]
              exact ⟨fun h' => h'.resolve_right fun e => hww (hLc ▸ e).symm, Or.inl⟩
            rw [e]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hk'' with h' | h'
          · exact hlt k' h'
          · rw [h', hLc]
            exact hw
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h' | h'
          · exact hdis j' h' i' hi'
          · rw [h'] at hi' ⊢
            intro e
            have : preK L c w = true :=
              (preK_iff w L c (by omega)).2 ⟨i', hi', e.trans hLc⟩
            rw [this] at hp
            exact Bool.noConfusion hp
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hk'' with h' | h'
          · exact htree k' h' hk0
          · subst h'
            rw [hPc, hBc, hLc, ← hwd]
            exact ⟨hh, hlm, rfl⟩
      obtain ⟨c', hc', hI'', hk''⟩ := ih (l + 1) (c + 1) _ k (by omega) hI' (by omega) hk'
      exact ⟨c', by omega, hI'', hk''⟩

private theorem outer_sim {Ms : List Nat} {x y cap : Nat} {L P B : List Nat} {n : Nat}
    (hn : L.length = n) :
    ∀ k h c (s : KSt), h + k = cap → h ≤ c → KInv Ms x y L P B n c s →
      runC Ms x y cap L P B n (L.drop h) h c = true →
      KInv Ms x y L P B n n
        (forIn (m := Id) (List.range' h k) s (kOuter (Ms.map (unpackR 24)).toArray x y)) := by
  intro k
  induction k with
  | zero =>
    intro h c s hk _ hI hr
    have := runC_end hr (Or.inl (by omega))
    subst this
    exact hI
  | succ k ih =>
    intro h c s hk hhc hI hr
    rw [List.range'_succ, List.forIn_cons]
    by_cases hc : h < c
    · have hsz : h < s.2.1.size := by rw [hI.2.2.1.1]; exact hc
      have hx : s.2.1[h]! = getL 0 L h := hI.2.2.1.2 h hc
      have hLh : h < L.length := by have := hI.2.1; omega
      rw [List.drop_eq_getElem_cons hLh, ← getL_lt hLh, runC_cons,
        ite_eq_left ⟨by omega, hc⟩] at hr
      obtain ⟨c', hcc, hI', hr'⟩ := inner_sim hn Ms.length 0 c s _ (by omega) hI hc
        (by rw [List.drop_zero]; exact hr)
      have hb : kOuter (Ms.map (unpackR 24)).toArray x y h s =
          pure (.yield (forIn (m := Id) (List.range' 0 Ms.length) s
            (kInner (Ms.map (unpackR 24)).toArray x y (getL 0 L h) h))) := by
        unfold kOuter
        rw [ite_eq_left hsz, hx, Std.Legacy.Range.forIn_eq_forIn_range']
        simp [Std.Legacy.Range.size]
        rfl
      rw [hb]
      exact ih (h + 1) c' _ (by omega) (by omega) hI' hr'
    · have hsz : ¬h < s.2.1.size := by rw [hI.2.2.1.1]; exact hc
      have hb : kOuter (Ms.map (unpackR 24)).toArray x y h s = pure (.done s) := by
        unfold kOuter
        rw [ite_eq_right hsz]
      rw [hb]
      have := runC_end hr (Or.inr (by omega))
      subst this
      exact hI

theorem cosetBFS_sound {Ms : List Nat} {x y c0 cap : Nat} {L P B : List Nat}
    (_h : cbfsK Ms x y c0 cap L P B = true) :
    cosetBFS (Ms.map (unpackR 24)).toArray x y c0 cap = (L.toArray, P.toArray, B.toArray) ∧
      L.Nodup ∧
      CFSG.Sporadic.Co1.Module.Pairs.treeCheckK (Ms.map (unpackR 24)).toArray x y L.toArray
        P.toArray B.toArray = true ∧
      (L.toArray.all fun v => decide (v < 2 ^ 24)) = true := by
  unfold cbfsK at _h
  rw [strictB_eq, lenL_eq] at _h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, pw2_eq, lenL_eq] at _h
  obtain ⟨⟨⟨hn0, hc0⟩, hPn, hBn⟩, ⟨hL0, hP0, hB0⟩, hrun⟩ := _h
  have hL0' : 0 < L.length := hn0
  have hI0 : KInv Ms x y L P B L.length 1
      ((Array.replicate (1 <<< 24) 0).set! c0 1, #[c0], #[0], #[0]) := by
    refine ⟨Nat.le_refl 1, hn0, ⟨rfl, fun k hk => ?_⟩, ⟨rfl, fun k hk => ?_⟩, ⟨rfl, fun k hk => ?_⟩,
      by simp [Nat.one_shiftLeft], fun w hw => ?_, fun k hk => ?_, fun j hj i hi => ?_,
      fun k hk hk0 => ?_⟩
    · have e : k = 0 := by omega
      subst e
      simp [hL0]
    · have e : k = 0 := by omega
      subst e
      simp [hP0]
    · have e : k = 0 := by omega
      subst e
      simp [hB0]
    · dsimp only
      rw [set_getU (by simpa [Nat.one_shiftLeft] using hc0)]
      have hp : preK L 1 w = true ↔ c0 = w := by
        rw [preK_iff w L 1 hn0, ← hL0]
        exact ⟨fun ⟨k, hk, e⟩ => by rwa [show k = 0 by omega] at e, fun e => ⟨0, Nat.one_pos, e⟩⟩
      by_cases hw0 : w = c0
      · rw [ite_eq_left hw0, (hp.2 hw0.symm)]
        exact ⟨fun e => absurd e (by decide), fun e => nomatch e⟩
      · rw [ite_eq_right hw0, getElem!_pos _ w (by simpa [Nat.one_shiftLeft] using hw),
          Array.getElem_replicate]
        have : preK L 1 w = false := by
          cases e : preK L 1 w
          · rfl
          · exact absurd (hp.1 e).symm hw0
        rw [this]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
    · have e : k = 0 := by omega
      subst e
      rw [hL0]
      exact hc0
    · omega
    · omega
  have hF := outer_sim (Ms := Ms) (x := x) (y := y) (cap := cap) (P := P) (B := B) rfl cap 0 1 _
    (Nat.zero_add cap) (Nat.zero_le 1) hI0 (by rw [List.drop_zero]; exact hrun)
  generalize hsF : forIn (m := Id) (List.range' 0 cap)
    ((Array.replicate (1 <<< 24) 0).set! c0 1, #[c0], #[0], #[0])
    (kOuter (Ms.map (unpackR 24)).toArray x y) = sF at hF
  obtain ⟨-, -, hpts, hpar, hlab, -, -, hlt, hdis, htree⟩ := hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cosetBFS_eq]
    dsimp only
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have hl : List.range' [0:cap].start [0:cap].size [0:cap].step = List.range' 0 cap := by
      simp [Std.Legacy.Range.size]
    have hpar' : AR sF.2.2.1 P.length (getL 0 P) := by rw [hPn]; exact hpar
    have hlab' : AR sF.2.2.2 B.length (getL 0 B) := by rw [hBn]; exact hlab
    rw [hl, hsF, AR_toArray hpts, AR_toArray hpar', AR_toArray hlab']
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [← getL_lt hi, ← getL_lt hj]
    exact hdis j hj i hij
  · unfold CFSG.Sporadic.Co1.Module.Pairs.treeCheckK
    simp only [List.size_toArray, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, beq_iff_eq]
    refine ⟨hL0', fun k hk => ?_⟩
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      obtain ⟨h1, h2, h3⟩ := htree k hk hk0
      have hkP : k < P.length := by omega
      have hkB : k < B.length := by omega
      have eP : P.toArray[k]! = getL 0 P k := by
        rw [getElem!_pos _ k (by simpa using hkP), List.getElem_toArray, getL_lt hkP]
      have eB : B.toArray[k]! = getL 0 B k := by
        rw [getElem!_pos _ k (by simpa using hkB), List.getElem_toArray, getL_lt hkB]
      have eL : ∀ i < L.length, L.toArray[i]! = getL 0 L i := fun i hi => by
        rw [getElem!_pos _ i (by simpa using hi), List.getElem_toArray, getL_lt hi]
      simp only [List.length_map]
      rw [eP, eB, eL k hk, eL _ (by omega), Mts_get h2, canon_eq]
      exact ⟨⟨h1, h2⟩, h3⟩
  · rw [List.all_toArray, List.all_eq_true]
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
    rw [decide_eq_true_eq, ← getL_lt hi]
    exact hlt i hi

end CFSG.KC.Co1M

end
