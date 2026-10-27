module

public import Certificates.Data.Kernel.SporSch.TitsStab
public import CFSG.Certificates.Kernel.SporSch.TitsInvSound
public import CFSG.Sporadic.Schreier.TitsStabCheckInputs
import CFSG.Certificates.Kernel.Spor.RawOrbHead
meta import Lean.Meta.Tactic.NormCast

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Tits
open CFSG.KS.Mathieu (icode)

theorem pgW_eq (w p i : Nat) : pgW w p i = pg w (mask w) p i := by
  apply Nat.eq_of_testBit_eq
  intro k
  have e : pgW w p i =
      pg w (mask w) ((p >>> (64 * w * (i / 64))) &&& mask (64 * w)) (i % 64) := rfl
  rw [e, testBit_pg, testBit_pg, Nat.testBit_and, Nat.testBit_shiftRight, testBit_mask]
  by_cases hk : k < w
  · have hm : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
    have h1 : w * (i % 64) + k < 64 * w := by nlinarith
    have h2 : 64 * w * (i / 64) + (w * (i % 64) + k) = w * i + k := by
      conv_rhs => rw [← Nat.div_add_mod i 64]
      ring
    simp [hk, h1, h2]
  · simp [hk]

theorem permW_eq (n w p q : Nat) : permW n w p q = permOK n w (mask w) (n * w) p q := by
  unfold permW permOK
  simp only [pgW_eq]
  rfl

theorem unpackW_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  simp only [unpack]
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem unpackW_get0 {n w P i : Nat} (hP0 : Nat.beq (Nat.shiftRight P (n * w)) 0 = true) :
    (unpack n w P)[i]! = pg w (mask w) P i := by
  have hP : P < 2 ^ (n * w) := Nat.lt_of_div_eq_zero (Nat.two_pow_pos _)
    (by rw [← Nat.shiftRight_eq_div_pow]; exact Nat.eq_of_beq_eq_true hP0)
  by_cases h : i < n
  · exact unpackW_get h
  · rw [getElem!_neg _ i (by unfold unpack; rw [Array.size_ofFn]; exact h)]
    have hw : n * w ≤ w * i := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left w (by omega)
    have e : Nat.shiftRight P (Nat.mul w i) = 0 := by
      have e1 : Nat.shiftRight P (Nat.mul w i) = P >>> (w * i) := rfl
      rw [e1, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) hw))
    unfold pg
    rw [e]
    exact (Nat.zero_and _).symm

theorem eq2W_sound {n w r p q : Nat} (h : eq2W n w r p q = true) :
    compA n (unpack n w p) (unpack n w q) = unpack n w r := by
  obtain ⟨hb, ha⟩ := (bAnd_iff _ _).1 h
  refine Array.ext (by simp [compA, unpack]) fun i h1 _ => ?_
  have hi : i < n := by simpa [compA] using h1
  have hc : (compA n (unpack n w p) (unpack n w q))[i] =
      (unpack n w p)[(unpack n w q)[i]!]! := by simp [compA]
  have hr : (unpack n w r)[i] = (unpack n w r)[i]! := (getElem!_pos _ i _).symm
  rw [hc, hr, unpackW_get hi, unpackW_get hi, unpackW_get0 (by simpa using hb)]
  have e := Nat.eq_of_beq_eq_true (allN_spec ha i hi)
  rw [pgW_eq, pgW_eq, pgW_eq] at e
  exact e.symm

theorem wPtG_get {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) :
    ∀ wd : List Int, lettersK kS wd = true → ∀ i < n,
      (wordA n S (rawInvs n S) wd)[i]! = wPtG w PS PSI wd i ∧ wPtG w PS PSI wd i < n
  | [], _, i, hi => by
    rw [wordA, CFSG.Monster.B.Co2.idA_get hi]
    exact ⟨rfl, hi⟩
  | z :: wd, hl, i, hi => by
    rw [Raw.Orb.lettersK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨h1, h2⟩, hl⟩ := hl
    obtain ⟨ih1, ih2⟩ := wPtG_get hS hp wd hl i hi
    obtain ⟨l1, l2⟩ := letter_get hS hp h1 h2 ih2
    have e : wPtG w PS PSI (z :: wd) i = pgW w (letP PS PSI (icode z)) (wPtG w PS PSI wd i) := by
      change strictN (icode z) (fun c => strictN (wPtG w PS PSI wd i)
        (fun j => pgW w (letP PS PSI c) j)) = _
      rw [Raw.Orb.strictN_eq, Raw.Orb.strictN_eq]
    rw [wordA, CFSG.Monster.B.Co2.compA_get hi, ih1, e, pgW_eq, ← l1]
    exact ⟨rfl, l2⟩

theorem wPtG_sound {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {wd : List Int}
    (_hw : n + 1 < 2 ^ w) (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : lettersK kS wd = true) {i : Nat} (hi : i < n) :
    (wordA n S (rawInvs n S) wd)[i]! = wPtG w PS PSI wd i :=
  (wPtG_get hS hp wd hl i hi).1

theorem size_wordA (n : Nat) (S Si : Array (Array Nat)) :
    ∀ wd : List Int, (wordA n S Si wd).size = n
  | [] => by simp [wordA, idA]
  | _ :: _ => by simp [wordA, compA]

theorem wordW_sound {n w kS r : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    {wd : List Int} (hw : n + 1 < 2 ^ w) (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (h : wordW n w PS PSI kS wd r = true) :
    wordA n S (rawInvs n S) wd = unpack n w r := by
  obtain ⟨hl, ha⟩ := (bAnd_iff _ _).1 h
  refine Array.ext (by rw [size_wordA]; simp [unpack]) fun i h1 _ => ?_
  have hi : i < n := by rwa [size_wordA] at h1
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i (by simpa [unpack] using hi),
    wPtG_sound hw hS hp hl hi, unpackW_get hi]
  have e := Nat.eq_of_beq_eq_true (allN_spec ha i hi)
  rw [pgW_eq] at e
  exact e.symm

theorem strongK_of {n w : Nat} {PS PSI : Nat → Nat} : ∀ {W : List (List Int)} {j : Nat},
    (∀ i < W.length, wordW n w PS PSI (j + i) W[i]! (PS (j + i)) = true) →
      strongK n w PS PSI W j = true
  | [], _, _ => rfl
  | wd :: W, j, h => by
    change Bool.rec (motive := fun _ => Bool) false (strongK n w PS PSI W (Nat.succ j))
      (wordW n w PS PSI j wd (PS j)) = true
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at h0
    rw [h0, strongK_of fun i hi => ?_]
    have hi' := h (i + 1) (by simp only [List.length_cons]; omega)
    have e : j + (i + 1) = Nat.succ j + i := by omega
    rw [e, List.getElem!_cons_succ] at hi'
    exact hi'

theorem eqA_refl' (n : Nat) (t : Array Nat) : eqA n t t = true := by
  unfold eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem lettersK_mono {j j' : Nat} (hj : j ≤ j') : ∀ {wd : List Int}, lettersK j wd = true →
    lettersK j' wd = true
  | [], _ => rfl
  | z :: wd, h => by
    rw [Raw.Orb.lettersK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at h ⊢
    exact ⟨⟨h.1.1, by omega⟩, lettersK_mono hj h.2⟩

theorem strongK_get {n w : Nat} {PS PSI : Nat → Nat} : ∀ {W : List (List Int)} {j : Nat},
    strongK n w PS PSI W j = true → ∀ i < W.length, wordW n w PS PSI (j + i) W[i]! (PS (j + i)) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | wd :: W, j, h, i, hi => by
    have h' : bAnd(wordW n w PS PSI j wd (PS j), strongK n w PS PSI W (Nat.succ j)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    cases i with
    | zero =>
      simpa using h1
    | succ i =>
      have := strongK_get h2 i (by simp at hi; omega)
      rw [List.getElem!_cons_succ]
      have e : j + (i + 1) = Nat.succ j + i := by omega
      rw [e]
      exact this

theorem strongArrs_facts {n w : Nat} {PS PSI : Nat → Nat} (hw : n + 1 < 2 ^ w) :
    ∀ (W : List (List Int)) {k : Nat} {start : Array (Array Nat)}, start.size = k →
      (∀ j < k, start[j]! = unpack n w (PS j)) →
      allN (k + W.length) (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true →
      strongK n w PS PSI W k = true →
      (strongArrs n start W).size = k + W.length ∧
        ∀ j < k + W.length, (strongArrs n start W)[j]! = unpack n w (PS j)
  | [], k, start, hs, hg, _, _ => ⟨by rw [← hs]; rfl, fun j hj => hg j (by simpa using hj)⟩
  | wd :: W, k, start, hs, hg, hp, h => by
    have h' : bAnd(wordW n w PS PSI k wd (PS k), strongK n w PS PSI W (Nat.succ k)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    have hpk : allN k (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true :=
      allN_of_forall fun j hj => allN_spec hp j (by simp; omega)
    have e := wordW_sound hw ⟨hs, hg⟩ hpk h1
    have hs' : (start.push (wordArr n start wd)).size = k + 1 := by rw [Array.size_push, hs]
    have hg' : ∀ j < k + 1, (start.push (wordArr n start wd))[j]! = unpack n w (PS j) := by
      intro j hj
      rw [getElem!_pos _ j (by rw [hs']; exact hj), Array.getElem_push]
      split
      · rename_i hj'
        rw [← getElem!_pos _ j hj']
        exact hg j (by omega)
      · have hjk : j = k := by omega
        rw [hjk]
        exact e
    have hp' : allN (k + 1 + W.length) (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) =
        true := by
      have e2 : k + 1 + W.length = k + (wd :: W).length := by simp; omega
      rw [e2]
      exact hp
    obtain ⟨r1, r2⟩ := strongArrs_facts hw W hs' hg' hp' h2
    have e3 : k + (wd :: W).length = k + 1 + W.length := by simp; omega
    change (strongArrs n (start.push (wordArr n start wd)) W).size = _ ∧ ∀ j < _,
      (strongArrs n (start.push (wordArr n start wd)) W)[j]! = _
    rw [e3]
    exact ⟨r1, r2⟩

theorem strongK_sound {n w k : Nat} {PS PSI : Nat → Nat} {start : Array (Array Nat)}
    {W : List (List Int)} (hw : n + 1 < 2 ^ w)
    (hs : start.size = k ∧ ∀ j < k, start[j]! = unpack n w (PS j))
    (hp : allN (k + W.length) (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (h : strongK n w PS PSI W k = true) :
    strongArrs n start W = Array.ofFn (n := k + W.length) (fun j => unpack n w (PS j.val)) ∧
      strongOK n k start (strongArrs n start W) W = true := by
  obtain ⟨hsz, hget⟩ := strongArrs_facts hw W hs.1 hs.2 hp h
  have hS : (strongArrs n start W).size = k + W.length ∧
      ∀ j < k + W.length, (strongArrs n start W)[j]! = unpack n w (PS j) := ⟨hsz, hget⟩
  refine ⟨?_, ?_⟩
  · apply Array.ext (by rw [hsz, Array.size_ofFn])
    intro j h1 h2
    have hj : j < k + W.length := by rwa [hsz] at h1
    rw [← getElem!_pos _ j h1, hget j hj, Array.getElem_ofFn]
  · have hW := strongK_get h
    unfold strongOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨hsz, CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => ?_⟩,
      CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => ?_⟩,
      CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_⟩
    · rw [hsz] at hj
      have hpj := allN_spec hp j hj
      rw [hget j hj, (CFSG.KS.Prim.invEqK_sound hpj).1]
      exact (CFSG.KS.Prim.invEqK_sound hpj).2
    · rw [hget j (by omega), hs.2 j hj]
      exact eqA_refl' _ _
    · obtain ⟨hl, ha⟩ := (bAnd_iff _ _).1 (hW i hi)
      rw [Bool.and_eq_true]
      refine ⟨CFSG.KS.Prim.lettersK_sound hl, ?_⟩
      have hw' : wordW n w PS PSI (k + W.length) W[i]! (PS (k + i)) = true :=
        (bAnd_iff _ _).2 ⟨lettersK_mono (by omega) hl, ha⟩
      have e := wordW_sound hw hS hp hw'
      change eqA n (strongArrs n start W)[k + i]!
        (wordA n (strongArrs n start W) (rawInvs n (strongArrs n start W)) W[i]!) = true
      rw [e, hget _ (by omega)]
      exact eqA_refl' _ _

theorem set_getS {a : Array Nat} {i j : Nat} {v : Nat} (hi : i < a.size) :
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

theorem forIn_invS {β : Type} (R : Nat → β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    ∀ k a (init : β), a + k ≤ E → R a init → R (a + k) (forIn (List.range' a k) init f)
  | 0, _, _, _, h => h
  | k + 1, a, init, hE, h => by
    obtain ⟨b', hb, hR⟩ := hf a init (by omega) h
    rw [List.range'_succ, List.forIn_cons, hb]
    have e : a + (k + 1) = a + 1 + k := by omega
    rw [e]
    exact forIn_invS R E f hf k (a + 1) b' (by omega) hR

theorem forIn_rngS {β : Type} (k : Nat) (init : β) (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id) [0:k] init f = forIn (List.range' 0 k) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hl : List.range' [0:k].start [0:k].size [0:k].step = List.range' 0 k := by
    simp [Std.Legacy.Range.size]
  rw [hl]

abbrev OrbISt := Array Nat × Array Nat × Array Nat × Array Nat × Array Nat

abbrev OrbOSt := Array Nat × Array Nat × Array Nat × Array Nat × Array Nat × Nat

@[expose] def orbInit (reps : Array Nat) (c : Nat) (s : Array Nat × Array Nat) :
    Id (ForInStep (Array Nat × Array Nat)) :=
  pure (.yield (s.1.set! reps[c]! c, s.2.push reps[c]!))

@[expose] def orbInner (gens : Array (Array Nat)) (m x i : Nat) (s : OrbISt) :
    Id (ForInStep OrbISt) :=
  if (s.1[(gens[i]!)[x]!]! == m) = true then
    pure (.yield (s.1.set! (gens[i]!)[x]! s.1[x]!, s.2.1.set! (gens[i]!)[x]! (s.2.1[x]! + 1),
      s.2.2.1.set! (gens[i]!)[x]! x, s.2.2.2.1.set! (gens[i]!)[x]! i,
      s.2.2.2.2.push (gens[i]!)[x]!))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

@[expose] def orbOuter (gens : Array (Array Nat)) (m : Nat) (_ : Nat) (s : OrbOSt) :
    Id (ForInStep OrbOSt) :=
  if s.2.2.2.2.2 < s.2.2.2.2.1.size then do
    let s' ← forIn [0:gens.size] (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1)
      (orbInner gens m s.2.2.2.2.1[s.2.2.2.2.2]!)
    pure (.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2.1, s'.2.2.2.2, s.2.2.2.2.2 + 1))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

theorem orbitForest_eqS (n : Nat) (gens : Array (Array Nat)) (reps : Array Nat) :
    orbitForest n gens reps =
      (let s0 := (forIn [0:reps.size] (Array.replicate n reps.size, (#[] : Array Nat))
          (orbInit reps) : Id (Array Nat × Array Nat))
       let s := (forIn [0:n] (s0.1, Array.replicate n 0, Array.replicate n 0, Array.replicate n 0,
          s0.2, 0) (orbOuter gens reps.size) : Id OrbOSt)
       (s.1, s.2.1, s.2.2.1, s.2.2.2.1)) := rfl

@[expose] def FInv (n r : Nat) (gens : Array (Array Nat)) (lab dep par gl q : Array Nat) : Prop :=
  lab.size = n ∧ dep.size = n ∧ par.size = n ∧ gl.size = n ∧ lab[r]! = 0 ∧ dep[r]! = 0 ∧
  (∀ k < q.size, q[k]! < n ∧ lab[q[k]!]! = 0) ∧
  (∀ k < q.size, ∀ k' < q.size, q[k]! = q[k']! → k = k') ∧
  (∀ y < n, lab[y]! = 0 ∨ lab[y]! = 1) ∧
  (∀ y < n, lab[y]! = 0 → ∃ k < q.size, q[k]! = y) ∧
  (∀ y < n, lab[y]! = 0 → (y = r ∧ dep[y]! = 0) ∨ (0 < dep[y]! ∧ par[y]! < n ∧
    lab[par[y]!]! = 0 ∧ dep[par[y]!]! + 1 = dep[y]! ∧ gl[y]! < gens.size ∧
    (gens[gl[y]!]!)[par[y]!]! = y))

@[expose] def FGrow (n : Nat) (lab q lab' q' : Array Nat) : Prop :=
  (∀ y < n, lab[y]! = 0 → lab'[y]! = 0) ∧ q.size ≤ q'.size ∧ ∀ k < q.size, q'[k]! = q[k]!

theorem fGrow_refl (n : Nat) (lab q : Array Nat) : FGrow n lab q lab q :=
  ⟨fun _ _ h => h, le_rfl, fun _ _ => rfl⟩

theorem fGrow_trans {n : Nat} {l1 q1 l2 q2 l3 q3 : Array Nat} (h1 : FGrow n l1 q1 l2 q2)
    (h2 : FGrow n l2 q2 l3 q3) : FGrow n l1 q1 l3 q3 :=
  ⟨fun y hy h => h2.1 y hy (h1.1 y hy h), le_trans h1.2.1 h2.2.1,
    fun k hk => by rw [h2.2.2 k (by have := h1.2.1; omega), h1.2.2 k hk]⟩

section Forest

variable {n r : Nat} {gens : Array (Array Nat)}
  (hG : ∀ i < gens.size, ∀ y < n, (gens[i]!)[y]! < n)
include hG

theorem orbInner_step {x i : Nat} (hx : x < n) (hi : i < gens.size) {lab dep par gl q : Array Nat}
    (hI : FInv n r gens lab dep par gl q) (hlx : lab[x]! = 0) :
    ∃ lab' dep' par' gl' q', orbInner gens 1 x i (lab, dep, par, gl, q) =
        pure (.yield (lab', dep', par', gl', q')) ∧ FInv n r gens lab' dep' par' gl' q' ∧
      FGrow n lab q lab' q' ∧ lab'[(gens[i]!)[x]!]! = 0 := by
  obtain ⟨s1, s2, s3, s4, sr, sdr, sq, sd, s01, smem, sf⟩ := hI
  have hy := hG i hi x hx
  set y := (gens[i]!)[x]! with hyd
  rcases s01 y hy with hly | hly
  · refine ⟨lab, dep, par, gl, q, ?_, ⟨s1, s2, s3, s4, sr, sdr, sq, sd, s01, smem, sf⟩,
      fGrow_refl n lab q, hly⟩
    unfold orbInner
    rw [ite_eq_right (by rw [hly]; decide)]
  · have hxy : x ≠ y := fun e => by rw [e, hly] at hlx; exact absurd hlx (by decide)
    have hL : ∀ z, (lab.set! y lab[x]!)[z]! = if z = y then lab[x]! else lab[z]! := fun z =>
      set_getS (by rw [s1]; exact hy)
    have hD : ∀ z, (dep.set! y (dep[x]! + 1))[z]! = if z = y then dep[x]! + 1 else dep[z]! :=
      fun z => set_getS (by rw [s2]; exact hy)
    have hP : ∀ z, (par.set! y x)[z]! = if z = y then x else par[z]! := fun z =>
      set_getS (by rw [s3]; exact hy)
    have hGl : ∀ z, (gl.set! y i)[z]! = if z = y then i else gl[z]! := fun z =>
      set_getS (by rw [s4]; exact hy)
    have hL0 : ∀ z, lab[z]! = 0 → (lab.set! y lab[x]!)[z]! = 0 := fun z hz => by
      rw [hL]
      split
      · exact hlx
      · exact hz
    have hQ : ∀ k < q.size + 1, (q.push y)[k]! = if k < q.size then q[k]! else y := by
      intro k hk
      rw [getElem!_pos _ k (by rw [Array.size_push]; exact hk), Array.getElem_push]
      split
      · rename_i hk'
        rw [← getElem!_pos _ k hk']
      · rfl
    refine ⟨lab.set! y lab[x]!, dep.set! y (dep[x]! + 1), par.set! y x, gl.set! y i, q.push y,
      ?_, ⟨?_, ?_, ?_, ?_, hL0 r sr, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨fun z _ hz => hL0 z hz, ?_, ?_⟩, ?_⟩
    · unfold orbInner
      rw [ite_eq_left (by rw [hly]; decide)]
    · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, s1]
    · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, s2]
    · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, s3]
    · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, s4]
    · have hry : r ≠ y := fun e => by rw [e, hly] at sr; exact absurd sr (by decide)
      rw [hD, ite_eq_right hry]
      exact sdr
    · intro k hk
      rw [Array.size_push] at hk
      rw [hQ k hk]
      split
      · rename_i hk'
        exact ⟨(sq k hk').1, hL0 _ (sq k hk').2⟩
      · rw [hL, ite_eq_left rfl]
        exact ⟨hy, hlx⟩
    · intro k hk k' hk' e
      rw [Array.size_push] at hk hk'
      rw [hQ k hk, hQ k' hk'] at e
      split at e <;> split at e
      · rename_i h1 h2
        exact sd k h1 k' h2 e
      · rename_i h1 h2
        have := (sq k h1).2
        rw [e, hly] at this
        exact absurd this (by decide)
      · rename_i h1 h2
        have := (sq k' h2).2
        rw [← e, hly] at this
        exact absurd this (by decide)
      · omega
    · intro z hz
      rw [hL]
      split
      · exact Or.inl hlx
      · exact s01 z hz
    · intro z hz hlz
      rw [hL] at hlz
      by_cases hzy : z = y
      · refine ⟨q.size, by rw [Array.size_push]; omega, ?_⟩
        rw [hQ _ (by omega), ite_eq_right (Nat.lt_irrefl _), hzy]
      · rw [ite_eq_right hzy] at hlz
        obtain ⟨k, hk, e⟩ := smem z hz hlz
        refine ⟨k, by rw [Array.size_push]; omega, ?_⟩
        rw [hQ k (by omega), ite_eq_left hk, e]
    · intro z hz hlz
      rw [hL] at hlz
      rw [hD, hP, hGl]
      by_cases hzy : z = y
      · refine Or.inr ?_
        rw [ite_eq_left hzy, ite_eq_left hzy, ite_eq_left hzy, hL, ite_eq_right hxy, hD,
          ite_eq_right hxy, hzy]
        exact ⟨by omega, hx, hlx, rfl, hi, rfl⟩
      · rw [ite_eq_right hzy] at hlz
        rw [ite_eq_right hzy, ite_eq_right hzy, ite_eq_right hzy]
        rcases sf z hz hlz with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
        · exact Or.inl ⟨h1, h2⟩
        · have hpy : par[z]! ≠ y := fun e => by rw [e, hly] at h3; exact absurd h3 (by decide)
          refine Or.inr ⟨h1, h2, ?_, ?_, h5, h6⟩
          · rw [hL, ite_eq_right hpy]
            exact h3
          · rw [hD, ite_eq_right hpy]
            exact h4
    · rw [Array.size_push]
      omega
    · intro k hk
      rw [hQ k (by omega), ite_eq_left hk]
    · rw [hL, ite_eq_left rfl]
      exact hlx

theorem orbInner_loop {x : Nat} (hx : x < n) {lab dep par gl q : Array Nat}
    (hI : FInv n r gens lab dep par gl q) (hlx : lab[x]! = 0) :
    ∃ lab' dep' par' gl' q', forIn (m := Id) [0:gens.size] (lab, dep, par, gl, q)
        (orbInner gens 1 x) = (lab', dep', par', gl', q') ∧ FInv n r gens lab' dep' par' gl' q' ∧
      FGrow n lab q lab' q' ∧ ∀ i < gens.size, lab'[(gens[i]!)[x]!]! = 0 := by
  rw [forIn_rngS]
  have key := forIn_invS (fun i (t : OrbISt) => FInv n r gens t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 ∧
      FGrow n lab q t.1 t.2.2.2.2 ∧ ∀ i' < i, t.1[(gens[i']!)[x]!]! = 0) gens.size
    (orbInner gens 1 x) (fun i t hi ⟨hI', hg, hc⟩ => by
      obtain ⟨l, d, p, g, qq⟩ := t
      obtain ⟨l', d', p', g', q', e, hI'', hg', hy⟩ :=
        orbInner_step hG hx hi hI' (hg.1 x hx hlx)
      refine ⟨(l', d', p', g', q'), e, hI'', fGrow_trans hg hg', fun i' hi' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
      · exact hg'.1 _ (hG i' (by omega) x hx) (hc i' hi')
      · exact hy) gens.size 0 (lab, dep, par, gl, q) (by omega)
    ⟨hI, fGrow_refl n lab q, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [Nat.zero_add] at key
  obtain ⟨hI', hg, hc⟩ := key
  exact ⟨_, _, _, _, _, rfl, hI', hg, hc⟩

@[expose] def FOut (n r j : Nat) (gens : Array (Array Nat)) (b : OrbOSt) : Prop :=
  FInv n r gens b.1 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2.1 ∧ b.2.2.2.2.2 ≤ b.2.2.2.2.1.size ∧
    (∀ k < b.2.2.2.2.2, ∀ i < gens.size, b.1[(gens[i]!)[b.2.2.2.2.1[k]!]!]! = 0) ∧
    (j ≤ b.2.2.2.2.2 ∨ b.2.2.2.2.2 = b.2.2.2.2.1.size)

theorem orbOuter_step {j : Nat} {b : OrbOSt} (hb : FOut n r j gens b) :
    ∃ b', orbOuter gens 1 j b = pure (.yield b') ∧ FOut n r (j + 1) gens b' := by
  obtain ⟨lab, dep, par, gl, q, h⟩ := b
  obtain ⟨hI, hh, hc, hj⟩ := hb
  dsimp only at hI hh hc hj
  by_cases hlt : h < q.size
  · have hx := (hI.2.2.2.2.2.2.1 h hlt).1
    have hlx := (hI.2.2.2.2.2.2.1 h hlt).2
    obtain ⟨l', d', p', g', q', e, hI', hg, hcx⟩ := orbInner_loop hG hx hI hlx
    refine ⟨(l', d', p', g', q', h + 1), ?_, hI', ?_, fun k hk i hi => ?_, ?_⟩
    · unfold orbOuter
      rw [ite_eq_left hlt]
      dsimp only
      rw [e]
      rfl
    · dsimp only
      have := hg.2.1
      omega
    · dsimp only
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [hg.2.2 k (by omega)]
        exact hg.1 _ (hG i hi _ (hI.2.2.2.2.2.2.1 k (by omega)).1) (hc k hk i hi)
      · rw [hg.2.2 k hlt]
        exact hcx i hi
    · dsimp only
      omega
  · refine ⟨(lab, dep, par, gl, q, h), ?_, hI, hh, hc, Or.inr (by dsimp only; omega)⟩
    unfold orbOuter
    rw [ite_eq_right hlt]

end Forest

theorem forest1K_sound {n w kG r DEP PAR GL : Nat} {GS GSI : Nat → Nat}
    {gens : Array (Array Nat)} (_hw : n + 1 < 2 ^ w)
    (hg : gens.size = kG ∧ ∀ j < kG, gens[j]! = unpack n w (GS j))
    (hp : allN kG (fun j => permOK n w (mask w) (n * w) (GS j) (GSI j)) = true)
    (h : forest1K n w GS kG r DEP PAR GL = true) : forestOK n gens #[r] = true := by
  obtain ⟨hgs, hgv⟩ := hg
  have G : ∀ i < kG, ∀ y < n, (gens[i]!)[y]! = pg w (mask w) (GS i) y := fun i hi y hy => by
    rw [hgv i hi, unpackW_get hy]
  have hG : ∀ i < gens.size, ∀ y < n, (gens[i]!)[y]! < n := fun i hi y hy => by
    rw [hgs] at hi
    rw [G i hi y hy]
    exact ((Raw.Orb.permOK_facts (allN_spec hp i hi)).2.2 y hy).1
  unfold forest1K at h
  obtain ⟨hr, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, hF⟩ := (bAnd_iff _ _).1 h
  have hrn : r < n := Nat.blt_eq.mp hr
  have CF : ∀ x < n, (pgW w DEP x = 0 ∧ x = r) ∨ (0 < pgW w DEP x ∧ pgW w PAR x < n ∧
      pgW w DEP (pgW w PAR x) + 1 = pgW w DEP x ∧ pgW w GL x < kG ∧
      pgW w (GS (pgW w GL x)) (pgW w PAR x) = x) := by
    intro x hx
    have h1 := allN_spec hF x hx
    rw [strictB_eq, Raw.Orb.bIf_eq] at h1
    split at h1
    · rename_i hd
      exact Or.inl ⟨Nat.eq_of_beq_eq_true hd, Nat.eq_of_beq_eq_true h1⟩
    · rename_i hd
      rw [strictB_eq] at h1
      obtain ⟨e1, h1⟩ := (bAnd_iff _ _).1 h1
      obtain ⟨e2, h1⟩ := (bAnd_iff _ _).1 h1
      rw [strictB_eq] at h1
      obtain ⟨e3, e4⟩ := (bAnd_iff _ _).1 h1
      have hd' : pgW w DEP x ≠ 0 := fun e => hd (by rw [e]; rfl)
      exact Or.inr ⟨Nat.pos_of_ne_zero hd', Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2,
        Nat.blt_eq.mp e3, Nat.eq_of_beq_eq_true e4⟩
  have hrep : ∀ y < n, (Array.replicate n 0)[y]! = 0 := fun y hy => by
    rw [getElem!_pos _ y (by simpa using hy), Array.getElem_replicate]
  have hrep1 : ∀ y < n, (Array.replicate n 1)[y]! = 1 := fun y hy => by
    rw [getElem!_pos _ y (by simpa using hy), Array.getElem_replicate]
  have hs0 : (forIn (m := Id) [0:(#[r] : Array Nat).size] (Array.replicate n (#[r] : Array Nat).size,
      (#[] : Array Nat)) (orbInit #[r]) : Id (Array Nat × Array Nat)) =
      ((Array.replicate n 1).set! r 0, #[r]) := by
    rw [forIn_rngS]
    rfl
  have hsz1 : (Array.replicate n 1).size = n := Array.size_replicate
  have INIT : FOut n r 0 gens ((Array.replicate n 1).set! r 0, Array.replicate n 0,
      Array.replicate n 0, Array.replicate n 0, #[r], 0) := by
    refine ⟨⟨?_, by simp, by simp, by simp, ?_, hrep r hrn, fun k hk => ?_, fun k hk k' hk' _ => ?_,
      fun y hy => ?_, fun y hy hly => ?_, fun y hy hly => ?_⟩, by simp,
      fun k hk => absurd hk (Nat.not_lt_zero _), Or.inl le_rfl⟩
    · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz1]
    · rw [set_getS (by rw [hsz1]; exact hrn), ite_eq_left rfl]
    · have hk0 : k = 0 := by simpa using hk
      subst hk0
      refine ⟨hrn, ?_⟩
      rw [set_getS (by rw [hsz1]; exact hrn)]
      simp
    · simp at hk hk'
      omega
    · rw [set_getS (by rw [hsz1]; exact hrn)]
      split
      · exact Or.inl rfl
      · exact Or.inr (hrep1 y hy)
    · rw [set_getS (by rw [hsz1]; exact hrn)] at hly
      split at hly
      · rename_i hyr
        exact ⟨0, by simp, by simp [hyr]⟩
      · rw [hrep1 y hy] at hly
        exact absurd hly (by decide)
    · rw [set_getS (by rw [hsz1]; exact hrn)] at hly
      split at hly
      · rename_i hyr
        exact Or.inl ⟨hyr, hrep y hy⟩
      · rw [hrep1 y hy] at hly
        exact absurd hly (by decide)
  have OUT := forIn_invS (fun j (b : OrbOSt) => FOut n r j gens b) n (orbOuter gens 1)
    (fun j b _ hb => orbOuter_step hG hb) n 0 _ (by omega) INIT
  rw [Nat.zero_add] at OUT
  have hF : forestOK n gens #[r] = orbitLabelOK n gens 1
      (forIn (m := Id) (List.range' 0 n) ((Array.replicate n 1).set! r 0, Array.replicate n 0,
        Array.replicate n 0, Array.replicate n 0, #[r], 0) (orbOuter gens 1)).1 #[r]
      (forIn (m := Id) (List.range' 0 n) ((Array.replicate n 1).set! r 0, Array.replicate n 0,
        Array.replicate n 0, Array.replicate n 0, #[r], 0) (orbOuter gens 1)).2.1
      (forIn (m := Id) (List.range' 0 n) ((Array.replicate n 1).set! r 0, Array.replicate n 0,
        Array.replicate n 0, Array.replicate n 0, #[r], 0) (orbOuter gens 1)).2.2.1
      (forIn (m := Id) (List.range' 0 n) ((Array.replicate n 1).set! r 0, Array.replicate n 0,
        Array.replicate n 0, Array.replicate n 0, #[r], 0) (orbOuter gens 1)).2.2.2.1 := by
    unfold forestOK
    simp only [orbitForest_eqS, hs0, forIn_rngS]
    rfl
  rw [hF]
  generalize forIn (m := Id) (List.range' 0 n) ((Array.replicate n 1).set! r 0,
    Array.replicate n 0, Array.replicate n 0, Array.replicate n 0, #[r], 0) (orbOuter gens 1) = S
    at OUT ⊢
  obtain ⟨lab, dep, par, gl, q, hh⟩ := S
  obtain ⟨⟨s1, s2, s3, s4, sr, sdr, sq, sd, s01, smem, sf⟩, hhq, hc, hj⟩ := OUT
  dsimp only at s1 s2 s3 s4 sr sdr sq sd s01 smem sf hhq hc hj ⊢
  have hqn : q.size ≤ n := by
    have := Finset.card_le_card_of_injOn (s := Finset.range q.size) (t := Finset.range n)
      (fun k => q[k]!) (fun k hk => Finset.mem_range.2 (sq k (Finset.mem_range.1 hk)).1)
      (fun k hk k' hk' e => sd k (Finset.mem_range.1 hk) k' (Finset.mem_range.1 hk') e)
    simpa using this
  have hend : hh = q.size := by omega
  have ALL : ∀ d, ∀ x < n, pgW w DEP x = d → lab[x]! = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hx hd
      rcases CF x hx with ⟨-, hxr⟩ | ⟨h1, h2, h3, h4, h5⟩
      · rw [hxr]
        exact sr
      · have hlp := ih _ (by omega) _ h2 rfl
        obtain ⟨k, hk, hqk⟩ := smem _ h2 hlp
        have := hc k (by omega) (pgW w GL x) (by rw [hgs]; exact h4)
        rw [hqk, G _ h4 _ h2, ← pgW_eq, h5] at this
        exact this
  have L0 : ∀ x < n, lab[x]! = 0 := fun x hx => ALL _ x hx rfl
  unfold orbitLabelOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_,
    CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_⟩,
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc' => ?_⟩, CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_⟩
  · rw [L0 x hx]
    decide
  · rw [L0 _ (hG i hi x hx), L0 x hx]
    rfl
  · have hc0 : c = 0 := by simpa using hc'
    subst hc0
    have e : (#[r] : Array Nat)[0]! = r := rfl
    rw [e, sr, sdr]
    simp [hrn]
  · rcases sf x hx (L0 x hx) with ⟨hxr, hd⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · rw [hd, L0 x hx, hxr]
      simp
    · rw [Bool.or_eq_true]
      refine Or.inr ?_
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨⟨⟨h1, h2⟩, h4⟩, h5⟩, h6⟩

theorem iterA_eq {n : Nat} {a : Array Nat} {g : Nat → Nat} (ha : ∀ x < n, a[x]! = g x) :
    ∀ {k p : Nat}, itRng n g k p = true → iterA a k p = itN g k p
  | 0, _, _ => rfl
  | k + 1, p, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Nat.blt (itN g k p) n) (itRng n g k p) =
      true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    change a[iterA a k p]! = g (itN g k p)
    rw [iterA_eq ha h1]
    rw [Nat.blt_eq] at h2
    exact ha _ h2

theorem itRng_le {n : Nat} {g : Nat → Nat} {p j : Nat} :
    ∀ {k : Nat}, itRng n g k p = true → j ≤ k → itRng n g j p = true
  | 0, h, hjk => by
    rw [Nat.le_zero.1 hjk]
    exact h
  | k + 1, h, hjk => by
    rcases Nat.lt_or_eq_of_le hjk with hlt | heq
    · have h' : Bool.rec (motive := fun _ => Bool) false (Nat.blt (itN g k p) n)
          (itRng n g k p) = true := h
      exact itRng_le ((bAnd_iff _ _).1 h').1 (by omega)
    · rw [heq]
      exact h

theorem beqB_eq (a b : Bool) : beqB a b = (a == b) := by
  cases a <;> cases b <;> rfl

end CFSG.KS.SporSch

end
