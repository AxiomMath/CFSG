module

public import Certificates.Data.Kernel.StdOdd.Chain
public import CFSG.Certificates.Kernel.StdOdd.RootOrbitSound
public import Mathlib.Algebra.Group.Submonoid.Basic

public section

namespace CFSG.KS.StdOdd.Chain

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit Matrix

@[expose] noncomputable def cb (U : List ℕ) (i c : ℕ) : Bool := (nthN U c).testBit i

theorem forceL_eq (l : List ℕ) (k : List ℕ → ℕ) : forceL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    change forceN x (fun x => forceL l fun t => k (x :: t)) = _
    rw [forceN_eq, ih]

theorem forceLB_eq (l : List ℕ) (k : List ℕ → Bool) : forceLB l k = k l := by
  unfold forceLB
  rw [forceL_eq]
  cases k l <;> rfl

theorem forceB_eq (y : ℕ) (k : ℕ → Bool) : forceB y k = k y := by
  cases y <;> rfl

theorem notB_eq (b : Bool) : notB b = !b := by
  cases b <;> rfl

theorem beq_false_of_ne' {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem nthN_nil (i : ℕ) : nthN [] i = 0 := rfl

theorem nthN_ge : ∀ (l : List ℕ) (i : ℕ), lenN l ≤ i → nthN l i = 0
  | [], _, _ => rfl
  | _ :: l, 0, h => by rw [lenN_cons] at h; omega
  | _ :: l, i + 1, h => by
    rw [nthN_cons_succ]
    exact nthN_ge l i (by rw [lenN_cons] at h; omega)

theorem lenN_eq_length (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [lenN_cons, ih, List.length_cons]

@[expose] noncomputable def mapA (U : List ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih M => List.cons (rowX M U) (ih (Nat.shiftRight M (nat_lit 156))))

theorem mapRows_eq (M : ℕ) (U : List ℕ) : mapRows M U = mapA U 156 M := rfl

theorem mapA_succ (U : List ℕ) (n M : ℕ) :
    mapA U (n + 1) M = rowX M U :: mapA U n (M >>> 156) := rfl

theorem lenN_mapA (U : List ℕ) : ∀ n M, lenN (mapA U n M) = n
  | 0, _ => rfl
  | n + 1, M => by rw [mapA_succ, lenN_cons, lenN_mapA U n]

theorem nthN_mapA (U : List ℕ) : ∀ n M c, c < n → nthN (mapA U n M) c = rowX (M >>> (156 * c)) U
  | 0, _, c, h => absurd h (Nat.not_lt_zero c)
  | n + 1, M, 0, _ => by rw [mapA_succ, nthN_cons_zero, Nat.mul_zero, Nat.shiftRight_zero]
  | n + 1, M, c + 1, h => by
    rw [mapA_succ, nthN_cons_succ, nthN_mapA U n _ c (by omega), ← Nat.shiftRight_add]
    congr 2
    omega

theorem lenN_mapRows (M : ℕ) (U : List ℕ) : lenN (mapRows M U) = 156 := lenN_mapA U 156 M

theorem cb_mapRows {U : List ℕ} (hl : lenN U = 156) (M i : ℕ) (c : Fin 156) :
    bz (cb (mapRows M U) i c) = (matB M *ᵥ ptB U i) c := by
  rw [cb, mapRows_eq, nthN_mapA U 156 M c c.2]
  exact rowX_bit hl M c i

theorem planeApply_sound {U : List ℕ} (hl : lenN U = 156) (M i : ℕ) :
    ptB (mapRows M U) i = matB M *ᵥ ptB U i := by
  funext c
  rw [ptB_eq, ← cb_mapRows hl M i c]
  rfl

@[expose] def pairsOf : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | n + 1, pk =>
    if pk &&& 16383 = 0 then [] else
      ((pk &&& 16383) &&& 127, (pk &&& 16383) >>> 7) :: pairsOf n (pk >>> 14)

@[expose] noncomputable def f4b (U V : List ℕ) (i : ℕ) (p : ℕ × ℕ) : Bool × Bool :=
  ((cb U i (2 * p.1) && cb V i (2 * p.2)) ^^ (cb U i (2 * p.1 + 1) && cb V i (2 * p.2 + 1)),
    (cb U i (2 * p.1) && cb V i (2 * p.2 + 1)) ^^
      (cb U i (2 * p.1 + 1) && (cb V i (2 * p.2) ^^ cb V i (2 * p.2 + 1))))

@[expose] noncomputable def f4acc (s : Bool × Bool) (U V : List ℕ) (i : ℕ) (ps : List (ℕ × ℕ)) :
    Bool × Bool :=
  ps.foldl (fun acc p => (acc.1 ^^ (f4b U V i p).1, acc.2 ^^ (f4b U V i p).2)) s

@[expose] noncomputable def pairLoop (U V : List ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ a0 a1 => Nat.lor a0 a1)
    (fun _ ih pk a0 a1 => forceN (Nat.land pk (nat_lit 16383)) fun c =>
      Bool.rec (motive := fun _ => Nat)
      (forceN (Nat.land c (nat_lit 127)) fun a => forceN (Nat.shiftRight c (nat_lit 7)) fun b =>
      forceN (nthN U (Nat.mul 2 a)) fun x0 => forceN (nthN U (Nat.add (Nat.mul 2 a) 1)) fun x1 =>
      forceN (nthN V (Nat.mul 2 b)) fun y0 => forceN (nthN V (Nat.add (Nat.mul 2 b) 1)) fun y1 =>
      forceN (Nat.xor a0 (Nat.xor (Nat.land x0 y0) (Nat.land x1 y1))) fun a0 =>
      forceN (Nat.xor a1 (Nat.xor (Nat.land x0 y1) (Nat.land x1 (Nat.xor y0 y1)))) fun a1 =>
      ih (Nat.shiftRight pk (nat_lit 14)) a0 a1)
      (Nat.lor a0 a1) (Nat.beq c 0))

theorem pairAcc_eq (U V : List ℕ) (pk a0 a1 : ℕ) :
    pairAcc U V pk a0 a1 = pairLoop U V 6084 pk a0 a1 := rfl

theorem pairLoop_succ (U V : List ℕ) (n pk a0 a1 : ℕ) :
    pairLoop U V (n + 1) pk a0 a1 =
      if pk &&& 16383 = 0 then a0 ||| a1 else
        pairLoop U V n (pk >>> 14)
          (a0 ^^^ ((nthN U (2 * ((pk &&& 16383) &&& 127)) &&&
              nthN V (2 * ((pk &&& 16383) >>> 7))) ^^^
            (nthN U (2 * ((pk &&& 16383) &&& 127) + 1) &&&
              nthN V (2 * ((pk &&& 16383) >>> 7) + 1))))
          (a1 ^^^ ((nthN U (2 * ((pk &&& 16383) &&& 127)) &&&
              nthN V (2 * ((pk &&& 16383) >>> 7) + 1)) ^^^
            (nthN U (2 * ((pk &&& 16383) &&& 127) + 1) &&&
              (nthN V (2 * ((pk &&& 16383) >>> 7)) ^^^
                nthN V (2 * ((pk &&& 16383) >>> 7) + 1))))) := by
  have e : pairLoop U V (n + 1) pk a0 a1 = forceN (Nat.land pk (nat_lit 16383)) fun c =>
      Bool.rec (motive := fun _ => Nat)
      (forceN (Nat.land c (nat_lit 127)) fun a => forceN (Nat.shiftRight c (nat_lit 7)) fun b =>
      forceN (nthN U (Nat.mul 2 a)) fun x0 => forceN (nthN U (Nat.add (Nat.mul 2 a) 1)) fun x1 =>
      forceN (nthN V (Nat.mul 2 b)) fun y0 => forceN (nthN V (Nat.add (Nat.mul 2 b) 1)) fun y1 =>
      forceN (Nat.xor a0 (Nat.xor (Nat.land x0 y0) (Nat.land x1 y1))) fun a0 =>
      forceN (Nat.xor a1 (Nat.xor (Nat.land x0 y1) (Nat.land x1 (Nat.xor y0 y1)))) fun a1 =>
      pairLoop U V n (Nat.shiftRight pk (nat_lit 14)) a0 a1)
      (Nat.lor a0 a1) (Nat.beq c 0) := rfl
  rw [e, forceN_eq]
  by_cases hc : pk &&& 16383 = 0
  · rw [ite_eq_left hc]
    have : Nat.beq (pk &&& 16383) 0 = true := by rw [hc]; rfl
    change Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq (pk &&& 16383) 0) = _
    rw [this]
    rfl
  · rw [ite_eq_right hc]
    have : Nat.beq (pk &&& 16383) 0 = false := beq_false_of_ne' hc
    change Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq (pk &&& 16383) 0) = _
    rw [this]
    simp only [forceN_eq]
    rfl

theorem pairLoop_sound (U V : List ℕ) (i : ℕ) : ∀ n pk a0 a1,
    (pairLoop U V n pk a0 a1).testBit i =
      ((f4acc (a0.testBit i, a1.testBit i) U V i (pairsOf n pk)).1 ||
        (f4acc (a0.testBit i, a1.testBit i) U V i (pairsOf n pk)).2)
  | 0, pk, a0, a1 => by
    change (a0 ||| a1).testBit i = _
    rw [Nat.testBit_or]
    rfl
  | n + 1, pk, a0, a1 => by
    rw [pairLoop_succ]
    by_cases hc : pk &&& 16383 = 0
    · rw [ite_eq_left hc, Nat.testBit_or, pairsOf, ite_eq_left hc]
      rfl
    · rw [ite_eq_right hc, pairLoop_sound U V i n, pairsOf, ite_eq_right hc]
      simp only [f4acc, List.foldl_cons, f4b, cb, Nat.testBit_xor, Nat.testBit_and]

theorem pairNZ_sound (U V : List ℕ) (pk i : ℕ) :
    (pairNZ U V pk).testBit i =
      ((f4acc (false, false) U V i (pairsOf 6084 pk)).1 ||
        (f4acc (false, false) U V i (pairsOf 6084 pk)).2) := by
  rw [pairNZ, pairAcc_eq, pairLoop_sound, Nat.zero_testBit]

@[expose] noncomputable def anyB (U V : List ℕ) (i : ℕ) (BL : List ℕ) : Bool :=
  BL.any fun pk => (f4acc (false, false) U V i (pairsOf 6084 pk)).1 ||
    (f4acc (false, false) U V i (pairsOf 6084 pk)).2

theorem anyNZ_aux (U V : List ℕ) (i : ℕ) : ∀ (BL : List ℕ) (acc : ℕ),
    (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun pk _ ih acc => forceN (Nat.lor acc (pairNZ U V pk)) ih) BL acc).testBit i =
      (acc.testBit i || anyB U V i BL)
  | [], acc => by simp [anyB]
  | pk :: BL, acc => by
    change (forceN (acc ||| pairNZ U V pk) _).testBit i = _
    rw [forceN_eq]
    change (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun pk _ ih acc => forceN (Nat.lor acc (pairNZ U V pk)) ih) BL
        (acc ||| pairNZ U V pk)).testBit i = _
    rw [anyNZ_aux U V i BL, Nat.testBit_or, pairNZ_sound]
    simp only [anyB, List.any_cons, Bool.or_assoc]

theorem anyNZ_sound (U V : List ℕ) (BL : List ℕ) (i : ℕ) :
    (anyNZ U V BL).testBit i = anyB U V i BL := by
  rw [anyNZ, anyNZ_aux]
  simp

@[expose] noncomputable def eqB (U V : List ℕ) (i : ℕ) : Bool :=
  (List.range (lenN U)).all fun c => cb U i c == cb V i c

theorem neqMask_aux (i : ℕ) : ∀ (U V : List ℕ) (acc : ℕ), lenN U = lenN V →
    (List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
      (fun x _ ih V acc => List.rec (motive := fun _ => Nat) acc
        (fun y V' _ => forceN (Nat.lor acc (Nat.xor x y)) (ih V')) V) U V acc).testBit i =
      (acc.testBit i || !(List.range (lenN U)).all fun c => cb U i c == cb V i c)
  | [], V, acc, _ => by simp [lenN]
  | x :: U, [], acc, h => by rw [lenN_cons] at h; exact absurd h (by simp [lenN])
  | x :: U, y :: V, acc, h => by
    rw [lenN_cons, lenN_cons] at h
    change (forceN (acc ||| (x ^^^ y)) _).testBit i = _
    rw [forceN_eq]
    change (List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
      (fun x _ ih V acc => List.rec (motive := fun _ => Nat) acc
        (fun y V' _ => forceN (Nat.lor acc (Nat.xor x y)) (ih V')) V) U V
        (acc ||| (x ^^^ y))).testBit i = _
    rw [neqMask_aux i U V _ (by omega), Nat.testBit_or, Nat.testBit_xor, lenN_cons,
      List.range_succ_eq_map, List.all_cons, List.all_map]
    have e : (fun c => cb (x :: U) i c == cb (y :: V) i c) ∘ Nat.succ =
        fun c => cb U i c == cb V i c := rfl
    rw [e]
    simp only [cb, nthN_cons_zero]
    cases x.testBit i <;> cases y.testBit i <;> simp

theorem neqMask_sound {U V : List ℕ} (h : lenN U = lenN V) (i : ℕ) :
    (neqMask U V).testBit i = !eqB U V i := by
  rw [neqMask, neqMask_aux i U V 0 h]
  simp [eqB]

theorem eqB_iff {U V : List ℕ} (hU : lenN U = 156) (_hV : lenN V = 156) (i : ℕ) :
    eqB U V i = true ↔ ptB U i = ptB V i := by
  rw [eqB, List.all_eq_true, hU]
  constructor
  · intro h
    funext c
    rw [ptB_eq, ptB_eq]
    have := h c (List.mem_range.2 c.2)
    rw [beq_iff_eq] at this
    exact congrArg bz this
  · intro h c hc
    rw [beq_iff_eq]
    exact bz_inj (by have := congrFun h ⟨c, List.mem_range.1 hc⟩; rwa [ptB_eq, ptB_eq] at this)

@[expose] noncomputable def rhoB (U V : List ℕ) (i FP : ℕ) (BL : List ℕ) : ℕ :=
  if eqB U V i = true then 0 else
    if ((f4acc (false, false) U V i (pairsOf 6084 FP)).1 ||
      (f4acc (false, false) U V i (pairsOf 6084 FP)).2) = true then 4 else
      if anyB U V i BL = true then 3 else 5

theorem andNot_testBit (m x i : ℕ) : (andNot m x).testBit i = (m.testBit i && !x.testBit i) := by
  change (m ^^^ (m &&& x)).testBit i = _
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases m.testBit i <;> cases x.testBit i <;> rfl

theorem profMask_eq (M : ℕ) (U : List ℕ) (w t FP : ℕ) (BL : List ℕ) :
    profMask M U w t FP BL =
      if t = 0 then andNot (full w) (full w &&& neqMask U (mapRows M U)) else
      if t = 4 then full w &&& neqMask U (mapRows M U) &&& pairNZ U (mapRows M U) FP else
      if t = 3 then
        andNot (full w &&& neqMask U (mapRows M U))
          (full w &&& neqMask U (mapRows M U) &&& pairNZ U (mapRows M U) FP) &&&
          anyNZ U (mapRows M U) BL
      else
        andNot (andNot (full w &&& neqMask U (mapRows M U))
          (full w &&& neqMask U (mapRows M U) &&& pairNZ U (mapRows M U) FP))
          (andNot (full w &&& neqMask U (mapRows M U))
            (full w &&& neqMask U (mapRows M U) &&& pairNZ U (mapRows M U) FP) &&&
            anyNZ U (mapRows M U) BL) := by
  unfold profMask
  simp only [forceL_eq, forceN_eq]
  by_cases h0 : t = 0
  · subst h0
    rfl
  by_cases h4 : t = 4
  · subst h4
    rfl
  by_cases h3 : t = 3
  · subst h3
    rfl
  rw [ite_eq_right h0, ite_eq_right h4, ite_eq_right h3]
  change Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) _ _ (Nat.beq t 3)) _ (Nat.beq t 4)) _ (Nat.beq t 0) = _
  rw [beq_false_of_ne' h0, beq_false_of_ne' h4, beq_false_of_ne' h3]
  rfl

theorem profileMask_sound {U : List ℕ} (hl : lenN U = 156) (M w t FP : ℕ) (BL : List ℕ)
    (ht : t = 0 ∨ t = 3 ∨ t = 4 ∨ t = 5) (i : ℕ) :
    (profMask M U w t FP BL).testBit i = true ↔
      i < w ∧ rhoB U (mapRows M U) i FP BL = t := by
  have hlv : lenN U = lenN (mapRows M U) := by rw [hl, lenN_mapRows]
  rw [profMask_eq]
  have hne : (full w &&& neqMask U (mapRows M U)).testBit i =
      (decide (i < w) && !eqB U (mapRows M U) i) := by
    rw [Nat.testBit_and, testBit_full, neqMask_sound hlv]
  have hfz : (full w &&& neqMask U (mapRows M U) &&& pairNZ U (mapRows M U) FP).testBit i =
      (decide (i < w) && !eqB U (mapRows M U) i &&
        ((f4acc (false, false) U (mapRows M U) i (pairsOf 6084 FP)).1 ||
          (f4acc (false, false) U (mapRows M U) i (pairsOf 6084 FP)).2)) := by
    rw [Nat.testBit_and, hne, pairNZ_sound]
  unfold rhoB
  have h3 : ∀ x y : ℕ, (x &&& y).testBit i = (x.testBit i && y.testBit i) :=
    fun x y => Nat.testBit_and x y i
  rcases ht with rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [ite_true, ite_false, h3, andNot_testBit,
      neqMask_sound hlv, pairNZ_sound, anyNZ_sound, testBit_full] <;>
    generalize f4acc (false, false) U (mapRows M U) i (pairsOf 6084 FP) = q <;>
    generalize anyB U (mapRows M U) i BL = ab <;>
    generalize eqB U (mapRows M U) i = eb <;>
    obtain ⟨q1, q2⟩ := q <;>
    by_cases hi : i < w <;> cases q1 <;> cases q2 <;> cases ab <;> cases eb <;> simp [hi]

theorem orL_testBit (i : ℕ) : ∀ ms : List ℕ,
    (orL ms).testBit i = true ↔ ∃ l < lenN ms, (nthN ms l).testBit i = true
  | [] => by simp [orL, lenN]
  | m :: ms => by
    change (m ||| orL ms).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, orL_testBit i ms, lenN_cons]
    constructor
    · rintro (h | ⟨l, hl, h⟩)
      · exact ⟨0, by omega, h⟩
      · exact ⟨l + 1, by omega, h⟩
    · rintro ⟨l, hl, h⟩
      cases l with
      | zero => exact Or.inl h
      | succ l => exact Or.inr ⟨l, by omega, h⟩

theorem disjL_aux (i : ℕ) : ∀ (ms : List ℕ) (acc : ℕ),
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun m _ ih acc => andB (Nat.beq (Nat.land m acc) 0) (ih (Nat.lor acc m))) ms acc) = true →
    (∀ l < lenN ms, (nthN ms l).testBit i = true → acc.testBit i = false) ∧
    ∀ l < lenN ms, ∀ l' < lenN ms, (nthN ms l).testBit i = true → (nthN ms l').testBit i = true →
      l = l'
  | [], _, _ => by simp [lenN]
  | m :: ms, acc, h => by
    change andB (Nat.beq (m &&& acc) 0) _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    have h0 : m &&& acc = 0 := Nat.eq_of_beq_eq_true h.1
    have hb : m.testBit i = true → acc.testBit i = false := by
      intro hm
      have := congrArg (fun y => y.testBit i) h0
      simp only [Nat.testBit_and, hm, Bool.true_and, Nat.zero_testBit] at this
      exact this
    obtain ⟨ih1, ih2⟩ := disjL_aux i ms (acc ||| m) h.2
    have ih1' : ∀ l < lenN ms, (nthN ms l).testBit i = true → m.testBit i = false ∧
        acc.testBit i = false := by
      intro l hl hb'
      have := ih1 l hl hb'
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
      exact ⟨this.2, this.1⟩
    rw [lenN_cons]
    refine ⟨fun l hl hm => ?_, fun l hl l' hl' h1 h2 => ?_⟩
    · cases l with
      | zero => exact hb hm
      | succ l => exact (ih1' l (by omega) hm).2
    · cases l with
      | zero =>
        cases l' with
        | zero => rfl
        | succ l' =>
          have := (ih1' l' (by omega) h2).1
          rw [nthN_cons_zero] at h1
          rw [h1] at this
          cases this
      | succ l =>
        cases l' with
        | zero =>
          have := (ih1' l (by omega) h1).1
          rw [nthN_cons_zero] at h2
          rw [h2] at this
          cases this
        | succ l' =>
          rw [ih2 l (by omega) l' (by omega) h1 h2]

theorem disjL_sound {ms : List ℕ} (h : disjL ms = true) (i : ℕ) :
    ∀ l < lenN ms, ∀ l' < lenN ms, (nthN ms l).testBit i = true → (nthN ms l').testBit i = true →
      l = l' :=
  (disjL_aux i ms 0 h).2

theorem nthN_shiftRows : ∀ (Ms : List ℕ) (l : ℕ), nthN (shiftRows Ms) l = nthN Ms l >>> 156
  | [], l => by simp [shiftRows, nthN_nil]
  | M :: Ms, 0 => rfl
  | M :: Ms, l + 1 => by
    change nthN (shiftRows Ms) l = _
    rw [nthN_shiftRows Ms l]
    rfl

theorem lenN_shiftRows : ∀ Ms : List ℕ, lenN (shiftRows Ms) = lenN Ms
  | [] => rfl
  | M :: Ms => by
    change lenN (shiftRows Ms) + 1 = lenN Ms + 1
    rw [lenN_shiftRows Ms]

@[expose] noncomputable def shiftN (Ms : List ℕ) : ℕ → List ℕ
  | 0 => Ms
  | c + 1 => shiftRows (shiftN Ms c)

theorem nthN_shiftN (Ms : List ℕ) (l : ℕ) : ∀ c, nthN (shiftN Ms c) l = nthN Ms l >>> (156 * c)
  | 0 => by simp [shiftN]
  | c + 1 => by
    rw [shiftN, nthN_shiftRows, nthN_shiftN Ms l c, ← Nat.shiftRight_add]
    congr 1

theorem lenN_shiftN (Ms : List ℕ) : ∀ c, lenN (shiftN Ms c) = lenN Ms
  | 0 => rfl
  | c + 1 => by rw [shiftN, lenN_shiftRows, lenN_shiftN Ms c]

theorem letterSum_bit_zero (U : List ℕ) (i : ℕ) : ∀ (Ms ms : List ℕ),
    (∀ l < lenN ms, (nthN ms l).testBit i = true → False) →
    (letterSum Ms ms U).testBit i = false
  | [], _, _ => by
    change (0 : ℕ).testBit i = false
    rw [Nat.zero_testBit]
  | _ :: _, [], _ => by
    change (0 : ℕ).testBit i = false
    rw [Nat.zero_testBit]
  | M :: Ms, m :: ms, h => by
    change ((m &&& rowX M U) ^^^ letterSum Ms ms U).testBit i = false
    have hm : m.testBit i = false := by
      cases hm : m.testBit i
      · rfl
      · exact (h 0 (by rw [lenN_cons]; omega) hm).elim
    rw [Nat.testBit_xor, Nat.testBit_and, hm, Bool.false_and, Bool.false_xor]
    exact letterSum_bit_zero U i Ms ms fun l hl hb => h (l + 1) (by rw [lenN_cons]; omega) hb

theorem letterSum_bit (U : List ℕ) (i : ℕ) : ∀ (Ms ms : List ℕ), lenN ms ≤ lenN Ms →
    (∀ l < lenN ms, ∀ l' < lenN ms, (nthN ms l).testBit i = true →
      (nthN ms l').testBit i = true → l = l') →
    ∀ l < lenN ms, (nthN ms l).testBit i = true →
      (letterSum Ms ms U).testBit i = (rowX (nthN Ms l) U).testBit i
  | [], ms, hlen, _, l, hl, _ => by
    change lenN ms ≤ 0 at hlen
    omega
  | M :: Ms, [], _, _, l, hl, _ => by simp [lenN] at hl
  | M :: Ms, m :: ms, hlen, hd, l, hl, hb => by
    change ((m &&& rowX M U) ^^^ letterSum Ms ms U).testBit i = _
    rw [lenN_cons, lenN_cons] at hlen
    rw [lenN_cons] at hl
    have hd' : ∀ l < lenN ms, ∀ l' < lenN ms, (nthN ms l).testBit i = true →
        (nthN ms l').testBit i = true → l = l' := by
      intro a ha b hb1 h1 h2
      have := hd (a + 1) (by rw [lenN_cons]; omega) (b + 1) (by rw [lenN_cons]; omega) h1 h2
      omega
    rw [Nat.testBit_xor, Nat.testBit_and]
    cases l with
    | zero =>
      rw [nthN_cons_zero] at hb
      rw [hb, Bool.true_and, nthN_cons_zero]
      have hz : (letterSum Ms ms U).testBit i = false := by
        by_cases hex : ∃ l < lenN ms, (nthN ms l).testBit i = true
        · obtain ⟨l, hl', hb'⟩ := hex
          have := hd 0 (by rw [lenN_cons]; omega) (l + 1) (by rw [lenN_cons]; omega)
            (by rw [nthN_cons_zero]; exact hb) hb'
          omega
        · exact letterSum_bit_zero U i Ms ms (fun l hl h => hex ⟨l, hl, h⟩)
      rw [hz, Bool.xor_false]
    | succ l =>
      have hm : m.testBit i = false := by
        cases hm : m.testBit i
        · rfl
        · have := hd 0 (by rw [lenN_cons]; omega) (l + 1) (by rw [lenN_cons]; omega)
            (by rw [nthN_cons_zero]; exact hm) hb
          omega
      rw [hm, Bool.false_and, Bool.false_xor, nthN_cons_succ]
      exact letterSum_bit U i Ms ms (by omega) hd' l (by omega) hb

theorem shiftN_shiftRows (Ms : List ℕ) : ∀ c, shiftN (shiftRows Ms) c = shiftN Ms (c + 1)
  | 0 => rfl
  | c + 1 => by rw [shiftN, shiftN_shiftRows Ms c, shiftN, shiftN, shiftN]

theorem stepAux_nth (ms U : List ℕ) (o : ℕ) : ∀ (V Ms : List ℕ) (c : ℕ), c < lenN V →
    nthN (stepAux ms U o V Ms) c = andNot (nthN V c) o ^^^ letterSum (shiftN Ms c) ms U
  | [], _, c, h => by simp [lenN] at h
  | x :: V, Ms, 0, _ => rfl
  | x :: V, Ms, c + 1, h => by
    rw [lenN_cons] at h
    change nthN (stepAux ms U o V (shiftRows Ms)) c = _
    rw [stepAux_nth ms U o V (shiftRows Ms) c (by omega), nthN_cons_succ, shiftN_shiftRows]

theorem lenN_stepAux (ms U : List ℕ) (o : ℕ) : ∀ (V Ms : List ℕ),
    lenN (stepAux ms U o V Ms) = lenN V
  | [], _ => rfl
  | x :: V, Ms => by
    change lenN (stepAux ms U o V (shiftRows Ms)) + 1 = lenN (x :: V)
    rw [lenN_stepAux ms U o V, lenN_cons]

theorem lenN_stepL (Ms ms U : List ℕ) : lenN (stepL Ms ms U) = lenN U := lenN_stepAux _ _ _ _ _

theorem stepL_sound {Ms ms U : List ℕ} (hl : lenN U = 156) (hlen : lenN ms = lenN Ms)
    (hd : disjL ms = true) (i : ℕ) :
    ptB (stepL Ms ms U) i = ptB U i ∨
      ∃ l < lenN Ms, ptB (stepL Ms ms U) i = matB (nthN Ms l) *ᵥ ptB U i := by
  have hd' := disjL_sound hd i
  by_cases hex : ∃ l < lenN ms, (nthN ms l).testBit i = true
  · obtain ⟨l, hlt, hb⟩ := hex
    refine Or.inr ⟨l, by omega, ?_⟩
    funext c
    rw [ptB_eq, ← rowX_bit hl (nthN Ms l) c i, stepL, stepAux_nth ms U _ U Ms c (by rw [hl]; exact c.2),
      Nat.testBit_xor, andNot_testBit, (orL_testBit i ms).2 ⟨l, hlt, hb⟩, Bool.not_true,
      Bool.and_false,
      Bool.false_xor, letterSum_bit U i (shiftN Ms c) ms (by rw [lenN_shiftN]; omega) hd' l hlt hb,
      nthN_shiftN]
  · refine Or.inl ?_
    funext c
    have ho : (orL ms).testBit i = false := by
      cases h : (orL ms).testBit i
      · rfl
      · exact (hex ((orL_testBit i ms).1 h)).elim
    rw [ptB_eq, ptB_eq, stepL, stepAux_nth ms U _ U Ms c (by rw [hl]; exact c.2), Nat.testBit_xor,
      andNot_testBit, ho, Bool.not_false, Bool.and_true,
      letterSum_bit_zero U i _ ms (fun l hl h => hex ⟨l, hl, h⟩), Bool.xor_false]

@[expose] noncomputable def letterMon (Ms : List ℕ) : Submonoid (Matrix (Fin 156) (Fin 156) (ZMod 2)) :=
  Submonoid.closure {A | ∃ l < lenN Ms, A = matB (nthN Ms l)}

theorem forestPlane_sound {Ms : List ℕ} {k : List ℕ → Bool} : ∀ (S : List (List ℕ)) (U : List ℕ),
    lenN U = 156 → walkK Ms S U k = true →
    ∃ V, k V = true ∧ lenN V = 156 ∧ ∀ i, ∃ g ∈ letterMon Ms, ptB V i = g *ᵥ ptB U i
  | [], U, hl, h => ⟨U, h, hl, fun i => ⟨1, Submonoid.one_mem _, by rw [Matrix.one_mulVec]⟩⟩
  | ms :: S, U, hl, h => by
    change andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
      (forceLB (stepL Ms ms U) fun U => walkK Ms S U k) = true at h
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, forceLB_eq] at h
    obtain ⟨⟨hlen, hd⟩, hw⟩ := h
    have hl' : lenN (stepL Ms ms U) = 156 := by rw [lenN_stepL, hl]
    obtain ⟨V, hk, hV, hpt⟩ := forestPlane_sound S _ hl' hw
    refine ⟨V, hk, hV, fun i => ?_⟩
    obtain ⟨g, hg, e⟩ := hpt i
    rcases stepL_sound hl (Nat.eq_of_beq_eq_true hlen) hd i with h1 | ⟨l, hlt, h1⟩
    · exact ⟨g, hg, by rw [e, h1]⟩
    · refine ⟨g * matB (nthN Ms l), Submonoid.mul_mem _ hg
        (Submonoid.subset_closure ⟨l, hlt, rfl⟩), ?_⟩
      rw [e, h1, Matrix.mulVec_mulVec]

@[expose] noncomputable def vecB (v : ℕ) : Fin 156 → ZMod 2 := fun c => bz (v.testBit c)

@[expose] noncomputable def replA (w : ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih v => List.cons (Nat.mul (Nat.land v 1) (full w)) (ih (Nat.shiftRight v 1)))

theorem lenN_replA (w : ℕ) : ∀ n v, lenN (replA w n v) = n
  | 0, _ => rfl
  | n + 1, v => by
    change lenN (replA w n (v >>> 1)) + 1 = n + 1
    rw [lenN_replA w n]

theorem nthN_replA (w i : ℕ) (hi : i < w) : ∀ n v c, c < n →
    (nthN (replA w n v) c).testBit i = v.testBit c
  | 0, _, c, h => absurd h (Nat.not_lt_zero c)
  | n + 1, v, 0, _ => by
    change ((v &&& 1) * full w).testBit i = _
    rw [Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one v with h | h
    · rw [h, Nat.zero_mul, Nat.zero_testBit, Nat.testBit_zero, h]
      rfl
    · rw [h, Nat.one_mul, testBit_full, Nat.testBit_zero, h]
      simp [hi]
  | n + 1, v, c + 1, h => by
    change (nthN (replA w n (v >>> 1)) c).testBit i = _
    rw [nthN_replA w i hi n _ c (by omega), Nat.testBit_shiftRight, Nat.add_comm]

theorem lenN_repl (v w : ℕ) : lenN (repl v w) = 156 := lenN_replA w 156 v

theorem repl_sound (v w i : ℕ) (hi : i < w) : ptB (repl v w) i = vecB v := by
  funext c
  rw [ptB_eq, vecB]
  change bz ((nthN (replA w 156 v) c).testBit i) = _
  rw [nthN_replA w i hi 156 v c c.2]

theorem neqV_aux (F i : ℕ) : ∀ (U : List ℕ) (v acc : ℕ),
    (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => Nat.land F acc)
      (fun x _ ih v acc => forceN (Nat.lor acc (Nat.xor x (Nat.mul (Nat.land v 1) F)))
        (ih (Nat.shiftRight v 1))) U v acc).testBit i =
      (F.testBit i && (acc.testBit i ||
        (List.range (lenN U)).any fun c => (nthN U c).testBit i != (v.testBit c && F.testBit i)))
  | [], v, acc => by
    change (F &&& acc).testBit i = _
    rw [Nat.testBit_and]
    simp [lenN]
  | x :: U, v, acc => by
    change (forceN (acc ||| (x ^^^ (v &&& 1) * F)) _).testBit i = _
    rw [forceN_eq]
    change (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => Nat.land F acc)
      (fun x _ ih v acc => forceN (Nat.lor acc (Nat.xor x (Nat.mul (Nat.land v 1) F)))
        (ih (Nat.shiftRight v 1))) U (v >>> 1) (acc ||| (x ^^^ (v &&& 1) * F))).testBit i = _
    rw [neqV_aux F i U, lenN_cons, List.range_succ_eq_map, List.any_cons, List.any_map]
    have e : ((fun c => (nthN (x :: U) c).testBit i != (v.testBit c && F.testBit i)) ∘
        Nat.succ) = fun c => (nthN U c).testBit i != ((v >>> 1).testBit c && F.testBit i) := by
      funext c
      simp only [Function.comp, nthN_cons_succ, Nat.testBit_shiftRight, Nat.add_comm 1 c]
    rw [e, Nat.testBit_or, Nat.testBit_xor, nthN_cons_zero]
    have hv : ((v &&& 1) * F).testBit i = (v.testBit 0 && F.testBit i) := by
      rw [Nat.and_one_is_mod]
      rcases Nat.mod_two_eq_zero_or_one v with h | h
      · rw [h, Nat.zero_mul, Nat.zero_testBit, Nat.testBit_zero, h]
        rfl
      · rw [h, Nat.one_mul, Nat.testBit_zero, h]
        simp
    rw [hv]
    cases F.testBit i <;> cases acc.testBit i <;> cases x.testBit i <;> cases v.testBit 0 <;> simp

theorem neqV_sound {U : List ℕ} (hl : lenN U = 156) (v w i : ℕ) :
    (neqV U v w).testBit i = true ↔ i < w ∧ ptB U i ≠ vecB v := by
  unfold neqV
  rw [forceN_eq, neqV_aux, testBit_full, Nat.zero_testBit, Bool.false_or, hl]
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      bne_iff_ne, ne_eq] at h
    obtain ⟨hi, c, hc, hne⟩ := h
    refine ⟨hi, fun e => hne ?_⟩
    have := congrFun e ⟨c, hc⟩
    rw [ptB_eq, vecB] at this
    simpa [hi] using bz_inj this
  · rintro ⟨hi, hne⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      bne_iff_ne, ne_eq]
    refine ⟨hi, ?_⟩
    by_contra hall
    push Not at hall
    apply hne
    funext c
    rw [ptB_eq, vecB, hall c c.2]
    simp [hi]

theorem neqPt_aux (F i k : ℕ) : ∀ (U FP : List ℕ) (acc : ℕ), lenN U = lenN FP →
    (List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
      (fun x _ ih FP acc => List.rec (motive := fun _ => Nat) acc
        (fun y FP' _ => forceN (Nat.lor acc (Nat.xor x
          (Nat.mul (Nat.land (Nat.shiftRight y k) 1) F))) (ih FP')) FP) U FP acc).testBit i =
      (acc.testBit i || (List.range (lenN U)).any fun c =>
        (nthN U c).testBit i != ((nthN FP c).testBit k && F.testBit i))
  | [], _, acc, _ => by simp [lenN]
  | x :: U, [], acc, h => by simp [lenN] at h
  | x :: U, y :: FP, acc, h => by
    rw [lenN_cons, lenN_cons] at h
    change (forceN (acc ||| (x ^^^ ((y >>> k) &&& 1) * F)) _).testBit i = _
    rw [forceN_eq]
    change (List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
      (fun x _ ih FP acc => List.rec (motive := fun _ => Nat) acc
        (fun y FP' _ => forceN (Nat.lor acc (Nat.xor x
          (Nat.mul (Nat.land (Nat.shiftRight y k) 1) F))) (ih FP')) FP) U FP
          (acc ||| (x ^^^ ((y >>> k) &&& 1) * F))).testBit i = _
    rw [neqPt_aux F i k U FP _ (by omega), lenN_cons, List.range_succ_eq_map, List.any_cons,
      List.any_map]
    have e : ((fun c => (nthN (x :: U) c).testBit i !=
        ((nthN (y :: FP) c).testBit k && F.testBit i)) ∘ Nat.succ) =
        fun c => (nthN U c).testBit i != ((nthN FP c).testBit k && F.testBit i) := rfl
    rw [e, Nat.testBit_or, Nat.testBit_xor, nthN_cons_zero, nthN_cons_zero]
    have hv : (((y >>> k) &&& 1) * F).testBit i = (y.testBit k && F.testBit i) := by
      rw [Nat.and_one_is_mod]
      rcases Nat.mod_two_eq_zero_or_one (y >>> k) with h | h
      · have hb : y.testBit k = false := by
          have := Nat.testBit_shiftRight (x := y) (i := k) (j := 0)
          rw [Nat.add_zero, Nat.testBit_zero, h] at this
          rw [← this]
          rfl
        rw [h, Nat.zero_mul, Nat.zero_testBit, hb, Bool.false_and]
      · have hb : y.testBit k = true := by
          have := Nat.testBit_shiftRight (x := y) (i := k) (j := 0)
          rw [Nat.add_zero, Nat.testBit_zero, h] at this
          rw [← this]
          rfl
        rw [h, Nat.one_mul, hb, Bool.true_and]
    rw [hv]
    cases acc.testBit i <;> cases x.testBit i <;> cases y.testBit k <;> cases F.testBit i <;> simp

theorem memMask_aux (U FP : List ℕ) (F i : ℕ) (h : lenN U = lenN FP) : ∀ (s acc : ℕ),
    (Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun k ih acc => forceN (Nat.lor acc (andNot F (neqPt U FP k F))) ih) s acc).testBit i =
      (acc.testBit i || (List.range s).any fun k => F.testBit i &&
        !(List.range (lenN U)).any fun c =>
          (nthN U c).testBit i != ((nthN FP c).testBit k && F.testBit i))
  | 0, acc => by simp
  | s + 1, acc => by
    change (forceN (acc ||| andNot F (neqPt U FP s F)) _).testBit i = _
    rw [forceN_eq]
    change (Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun k ih acc => forceN (Nat.lor acc (andNot F (neqPt U FP k F))) ih) s
        (acc ||| andNot F (neqPt U FP s F))).testBit i = _
    rw [memMask_aux U FP F i h s, Nat.testBit_or, andNot_testBit, neqPt, neqPt_aux F i s U FP 0 h,
      Nat.zero_testBit, Bool.false_or, List.range_succ, List.any_append, List.any_cons,
      List.any_nil, Bool.or_false]
    cases acc.testBit i <;> simp [Bool.or_comm]

theorem memMask_sound {U FP : List ℕ} (hU : lenN U = 156) (hF : lenN FP = 156) (s w i : ℕ) :
    (memMask U FP s w).testBit i = true ↔ i < w ∧ ∃ k < s, ptB U i = ptB FP k := by
  unfold memMask
  rw [forceN_eq, memMask_aux U FP _ i (by rw [hU, hF]), Nat.zero_testBit, Bool.false_or,
    testBit_full, hU]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and, Bool.and_true, List.any_eq_true, List.mem_range,
      Bool.not_eq_true', List.any_eq_false, bne_iff_ne, ne_eq, not_not, true_and]
    constructor
    · rintro ⟨k, hk, hall⟩
      refine ⟨k, hk, funext fun c => ?_⟩
      rw [ptB_eq, ptB_eq, hall c c.2]
    · rintro ⟨k, hk, e⟩
      refine ⟨k, hk, fun c hc => ?_⟩
      have := congrFun e ⟨c, hc⟩
      rw [ptB_eq, ptB_eq] at this
      exact bz_inj this
  · simp [hi]

theorem land_sub_one (x : ℕ) (hx : x ≠ 0) :
    ∃ t, x.testBit t = true ∧ x &&& (x - 1) = x ^^^ 2 ^ t := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have hy : x / 2 ≠ 0 := by omega
      obtain ⟨t, ht, e⟩ := ih (x / 2) (by omega) hy
      refine ⟨t + 1, by rw [Nat.testBit_succ]; exact ht, Nat.eq_of_testBit_eq fun j => ?_⟩
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow]
      cases j with
      | zero =>
        rw [Nat.testBit_zero, h]
        simp
      | succ j =>
        rw [Nat.testBit_succ, Nat.testBit_succ]
        have e2 : (x - 1) / 2 = x / 2 - 1 := by omega
        rw [e2, ← Nat.testBit_and, e, Nat.testBit_xor, Nat.testBit_two_pow]
        simp
    · refine ⟨0, by rw [Nat.testBit_zero, h]; rfl, Nat.eq_of_testBit_eq fun j => ?_⟩
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow]
      cases j with
      | zero =>
        rw [Nat.testBit_zero, Nat.testBit_zero, h]
        have : (x - 1) % 2 = 0 := by omega
        rw [this]
        simp
      | succ j =>
        rw [Nat.testBit_succ, Nat.testBit_succ]
        have e2 : (x - 1) / 2 = x / 2 := by omega
        rw [e2]
        simp

theorem card_filter_xor {x t n : ℕ} (ht : x.testBit t = true) (hn : x < 2 ^ n) :
    ((Finset.range n).filter fun j => (x ^^^ 2 ^ t).testBit j = true).card + 1 =
      ((Finset.range n).filter fun j => x.testBit j = true).card := by
  have htn : t < n := by
    by_contra h
    have : x < 2 ^ t := Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow this] at ht
    cases ht
  have e : ((Finset.range n).filter fun j => (x ^^^ 2 ^ t).testBit j = true) =
      ((Finset.range n).filter fun j => x.testBit j = true).erase t := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, Nat.testBit_xor,
      Nat.testBit_two_pow]
    by_cases hj : t = j
    · subst hj
      simp [ht]
    · simp [hj, Ne.symm hj]
  rw [e, Finset.card_erase_of_mem (by simp [htn, ht])]
  have : 0 < ((Finset.range n).filter fun j => x.testBit j = true).card :=
    Finset.card_pos.2 ⟨t, by simp [htn, ht]⟩
  omega

theorem popK_sound : ∀ (c x n : ℕ), popK x c = true → x < 2 ^ n →
    ((Finset.range n).filter fun j => x.testBit j = true).card = c
  | 0, x, n, h, _ => by
    have : x = 0 := Nat.eq_of_beq_eq_true h
    subst this
    simp
  | c + 1, x, n, h, hn => by
    change andB (notB (Nat.beq x 0)) (forceB (x &&& (x - 1)) fun y => popK y c) = true at h
    rw [andB_eq, Bool.and_eq_true, forceB_eq, notB_eq] at h
    have hx : x ≠ 0 := by
      intro hx
      subst hx
      exact absurd h.1 (by decide)
    obtain ⟨t, ht, e⟩ := land_sub_one x hx
    rw [e] at h
    have htn : 2 ^ t < 2 ^ n := by
      by_contra hc
      have : x < 2 ^ t := Nat.lt_of_lt_of_le hn (by omega)
      rw [Nat.testBit_lt_two_pow this] at ht
      cases ht
    have := popK_sound c _ n h.2 (Nat.xor_lt_two_pow hn htn)
    rw [← card_filter_xor ht hn, this]

@[expose] noncomputable def selM : List ℕ → List ℕ → ℕ → Matrix (Fin 156) (Fin 156) (ZMod 2)
  | M :: Ms, m :: ms, i => if m.testBit i = true then matB M else selM Ms ms i
  | _, _, _ => 1

@[expose] noncomputable def walkElt (Ms : List ℕ) : List (List ℕ) → ℕ →
    Matrix (Fin 156) (Fin 156) (ZMod 2)
  | [], _ => 1
  | ms :: S, i => walkElt Ms S i * selM Ms ms i

theorem selM_of_bit (i : ℕ) : ∀ (Ms ms : List ℕ), lenN ms ≤ lenN Ms →
    (∀ l < lenN ms, ∀ l' < lenN ms, (nthN ms l).testBit i = true →
      (nthN ms l').testBit i = true → l = l') →
    ∀ l < lenN ms, (nthN ms l).testBit i = true → selM Ms ms i = matB (nthN Ms l)
  | [], ms, hlen, _, l, hl, _ => by
    change lenN ms ≤ 0 at hlen
    omega
  | M :: Ms, [], _, _, l, hl, _ => by simp [lenN] at hl
  | M :: Ms, m :: ms, hlen, hd, l, hl, hb => by
    rw [lenN_cons, lenN_cons] at hlen
    rw [lenN_cons] at hl
    cases l with
    | zero =>
      rw [nthN_cons_zero] at hb
      rw [selM, ite_eq_left hb, nthN_cons_zero]
    | succ l =>
      have hm : m.testBit i = false := by
        cases hm : m.testBit i
        · rfl
        · have := hd 0 (by rw [lenN_cons]; omega) (l + 1) (by rw [lenN_cons]; omega)
            (by rw [nthN_cons_zero]; exact hm) hb
          omega
      rw [selM, ite_eq_right (by rw [hm]; decide), nthN_cons_succ]
      refine selM_of_bit i Ms ms (by omega) (fun a ha c hc h1 h2 => ?_) l (by omega) hb
      have := hd (a + 1) (by rw [lenN_cons]; omega) (c + 1) (by rw [lenN_cons]; omega) h1 h2
      omega

theorem selM_none (i : ℕ) : ∀ (Ms ms : List ℕ),
    (∀ l < lenN ms, (nthN ms l).testBit i = true → False) → selM Ms ms i = 1
  | [], _, _ => by simp [selM]
  | _ :: _, [], _ => by simp [selM]
  | M :: Ms, m :: ms, h => by
    have hm : m.testBit i = false := by
      cases hm : m.testBit i
      · rfl
      · exact (h 0 (by rw [lenN_cons]; omega) hm).elim
    rw [selM, ite_eq_right (by rw [hm]; decide)]
    exact selM_none i Ms ms fun l hl hb => h (l + 1) (by rw [lenN_cons]; omega) hb

theorem stepL_sel {Ms ms U : List ℕ} (hl : lenN U = 156) (hlen : lenN ms = lenN Ms)
    (hd : disjL ms = true) (i : ℕ) : ptB (stepL Ms ms U) i = selM Ms ms i *ᵥ ptB U i := by
  have hd' := disjL_sound hd i
  by_cases hex : ∃ l < lenN ms, (nthN ms l).testBit i = true
  · obtain ⟨l, hlt, hb⟩ := hex
    rw [selM_of_bit i Ms ms (by omega) hd' l hlt hb]
    funext c
    rw [ptB_eq, ← rowX_bit hl (nthN Ms l) c i, stepL,
      stepAux_nth ms U _ U Ms c (by rw [hl]; exact c.2), Nat.testBit_xor, andNot_testBit,
      (orL_testBit i ms).2 ⟨l, hlt, hb⟩, Bool.not_true, Bool.and_false, Bool.false_xor,
      letterSum_bit U i (shiftN Ms c) ms (by rw [lenN_shiftN]; omega) hd' l hlt hb, nthN_shiftN]
  · rw [selM_none i Ms ms (fun l hl h => hex ⟨l, hl, h⟩), Matrix.one_mulVec]
    funext c
    have ho : (orL ms).testBit i = false := by
      cases h : (orL ms).testBit i
      · rfl
      · exact (hex ((orL_testBit i ms).1 h)).elim
    rw [ptB_eq, ptB_eq, stepL, stepAux_nth ms U _ U Ms c (by rw [hl]; exact c.2), Nat.testBit_xor,
      andNot_testBit, ho, Bool.not_false, Bool.and_true,
      letterSum_bit_zero U i _ ms (fun l hl h => hex ⟨l, hl, h⟩), Bool.xor_false]

theorem walkK_sound {Ms : List ℕ} {k : List ℕ → Bool} : ∀ (S : List (List ℕ)) (U : List ℕ),
    lenN U = 156 → walkK Ms S U k = true →
    ∃ V, k V = true ∧ lenN V = 156 ∧ ∀ i, ptB V i = walkElt Ms S i *ᵥ ptB U i
  | [], U, hl, h => ⟨U, h, hl, fun i => by rw [walkElt, Matrix.one_mulVec]⟩
  | ms :: S, U, hl, h => by
    change andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
      (forceLB (stepL Ms ms U) fun U => walkK Ms S U k) = true at h
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, forceLB_eq] at h
    obtain ⟨⟨hlen, hd⟩, hw⟩ := h
    have hl' : lenN (stepL Ms ms U) = 156 := by rw [lenN_stepL, hl]
    obtain ⟨V, hk, hV, hpt⟩ := walkK_sound S _ hl' hw
    refine ⟨V, hk, hV, fun i => ?_⟩
    rw [hpt i, stepL_sel hl (Nat.eq_of_beq_eq_true hlen) hd i, Matrix.mulVec_mulVec, walkElt]

theorem blk_iff (r i n j : ℕ) (hj : j < r) :
    (n * r ≤ i * r + j ∧ i * r + j - n * r < r) ↔ n = i := by
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.mul_le_mul_right r (show n + 1 ≤ i by omega)
      rw [Nat.succ_mul] at this
      omega
    · have := Nat.mul_le_mul_right r (show i + 1 ≤ n by omega)
      rw [Nat.succ_mul] at this
      omega
  · rintro rfl
    exact ⟨by omega, by omega⟩

theorem blk_false {a b : Prop} [Decidable a] [Decidable b] (h : ¬(a ∧ b)) (x : Bool) :
    (decide a && (x && decide b)) = false := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

theorem testBit_blk (x r n q : ℕ) :
    ((x &&& full r) <<< (n * r)).testBit q =
      (decide (n * r ≤ q) && (x.testBit (q - n * r) && decide (q - n * r < r))) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_and, testBit_full]

theorem spread_testBit (r k m i j : ℕ) (hj : j < r) (hi : i < k) :
    (spread m r k).testBit (i * r + j) = m.testBit j := by
  unfold spread
  rw [forceN_eq]
  have key : ∀ n, (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun i ih => Nat.lor ih (Nat.shiftLeft (m &&& full r) (Nat.mul i r))) n).testBit
        (i * r + j) = (decide (i < n) && m.testBit j) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      change (_ ||| (m &&& full r) <<< (n * r)).testBit (i * r + j) = _
      rw [Nat.testBit_or, ih, testBit_blk]
      by_cases hin : n = i
      · subst hin
        have h1 : n * r ≤ n * r + j := by omega
        simp [h1, hj]
      · rw [blk_false ((blk_iff r i n j hj).not.2 hin), Bool.or_false]
        congr 1
        simp only [decide_eq_decide]
        omega
  exact (key k).trans (by simp [hi])

theorem selM_spread (r k i j : ℕ) (hj : j < r) (hi : i < k) : ∀ Ms ms : List ℕ,
    selM Ms (ms.map fun m => spread m r k) (i * r + j) = selM Ms ms j
  | [], _ => by simp [selM]
  | _ :: _, [] => by simp [selM]
  | M :: Ms, m :: ms => by
    rw [List.map_cons, selM, selM, spread_testBit r k m i j hj hi, selM_spread r k i j hj hi Ms ms]

theorem walkElt_spread (Ms : List ℕ) (r k i j : ℕ) (hj : j < r) (hi : i < k) :
    ∀ S : List (List ℕ), walkElt Ms (spreadS S r k) (i * r + j) = walkElt Ms S j
  | [] => rfl
  | ms :: S => by
    have e : spreadS (ms :: S) r k = (ms.map fun m => spread m r k) :: spreadS S r k := by
      change List.cons _ _ = _
      congr 1
      induction ms with
      | nil => rfl
      | cons m ms ih => exact congrArg (List.cons (spread m r k)) ih
    rw [e, walkElt, walkElt, selM_spread r k i j hj hi, walkElt_spread Ms r k i j hj hi S]

theorem selM_mem (Ms : List ℕ) (i : ℕ) : ∀ ms : List ℕ, selM Ms ms i ∈ letterMon Ms := by
  suffices h : ∀ (Ns ms : List ℕ), (∀ l < lenN Ns, ∃ l' < lenN Ms, nthN Ns l = nthN Ms l') →
      selM Ns ms i ∈ letterMon Ms from fun ms => h Ms ms fun l hl => ⟨l, hl, rfl⟩
  intro Ns
  induction Ns with
  | nil => intro ms _; simp [selM]
  | cons M Ns ih =>
    intro ms hN
    cases ms with
    | nil => simp [selM]
    | cons m ms =>
      rw [selM]
      split_ifs
      · obtain ⟨l', hl', e⟩ := hN 0 (by rw [lenN_cons]; omega)
        rw [nthN_cons_zero] at e
        exact Submonoid.subset_closure ⟨l', hl', by rw [e]⟩
      · exact ih ms fun l hl => hN (l + 1) (by rw [lenN_cons]; omega)

theorem walkElt_mem (Ms : List ℕ) (i : ℕ) : ∀ S, walkElt Ms S i ∈ letterMon Ms
  | [] => Submonoid.one_mem _
  | ms :: S => Submonoid.mul_mem _ (walkElt_mem Ms i S) (selM_mem Ms i ms)

theorem forceNL_eq (y : ℕ) (k : ℕ → List ℕ) : forceNL y k = k y := by
  cases y <;> rfl

theorem lenN_chunkPl (U : List ℕ) (off w : ℕ) : lenN (chunkPl U off w) = lenN U := by
  unfold chunkPl
  rw [forceNL_eq]
  induction U with
  | nil => rfl
  | cons x U ih => exact congrArg Nat.succ ih

theorem nthN_chunkPl (U : List ℕ) (off w c : ℕ) :
    nthN (chunkPl U off w) c = (nthN U c >>> off) &&& full w := by
  unfold chunkPl
  rw [forceNL_eq]
  induction U generalizing c with
  | nil => simp [nthN_nil]
  | cons x U ih =>
    cases c with
    | zero => rfl
    | succ c => exact ih c

theorem ptB_chunkPl (U : List ℕ) (off w i : ℕ) (hi : i < w) :
    ptB (chunkPl U off w) i = ptB U (off + i) := by
  funext c
  rw [ptB_eq, ptB_eq, nthN_chunkPl, Nat.testBit_and, testBit_full, Nat.testBit_shiftRight,
    decide_eq_true hi, Bool.and_true, Nat.add_comm off i]

theorem lenN_catPl (Es : List (List ℕ)) (r : ℕ) : lenN (catPl Es r) = 156 := by
  have : ∀ n c, lenN (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun _ ih c => List.cons (catRow Es r c) (ih (Nat.succ c))) n c) = n := by
    intro n
    induction n with
    | zero => intro c; rfl
    | succ n ih => intro c; exact congrArg Nat.succ (ih _)
  exact this 156 0

theorem nthN_catPl (Es : List (List ℕ)) (r c : ℕ) (hc : c < 156) :
    nthN (catPl Es r) c = catRow Es r c := by
  have : ∀ n c0 c, c < n → nthN (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun _ ih c => List.cons (catRow Es r c) (ih (Nat.succ c))) n c0) c = catRow Es r (c0 + c) := by
    intro n
    induction n with
    | zero => intro c0 c h; omega
    | succ n ih =>
      intro c0 c h
      cases c with
      | zero => rfl
      | succ c =>
        change nthN (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
          (fun _ ih c => List.cons (catRow Es r c) (ih (Nat.succ c))) n (c0 + 1)) c = _
        rw [ih (c0 + 1) c (by omega)]
        congr 1
        omega
  exact (this 156 0 c hc).trans (by rw [Nat.zero_add])

@[expose] noncomputable def catA (r c : ℕ) (Es : List (List ℕ)) (i0 : ℕ) : ℕ :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun E _ ih i => Nat.lor (Nat.shiftLeft (Nat.land (nthN E c) (full r)) (Nat.mul i r))
      (ih (Nat.succ i))) Es i0

theorem catA_cons (r c : ℕ) (E : List ℕ) (Es : List (List ℕ)) (i0 : ℕ) :
    catA r c (E :: Es) i0 = ((nthN E c &&& full r) <<< (i0 * r)) ||| catA r c Es (i0 + 1) := rfl

theorem catA_testBit (r c j : ℕ) (hj : j < r) : ∀ (Es : List (List ℕ)) (i0 i : ℕ),
    (catA r c Es i0).testBit (i * r + j) =
      (decide (i0 ≤ i ∧ i < i0 + Es.length) && (nthN (Es.getD (i - i0) []) c).testBit j)
  | [], i0, i => by
    change (0 : ℕ).testBit _ = _
    rw [Nat.zero_testBit]
    simp
  | E :: Es, i0, i => by
    rw [catA_cons, Nat.testBit_or, testBit_blk, catA_testBit r c j hj Es (i0 + 1) i]
    by_cases hii : i0 = i
    · subst hii
      have h1 : i0 * r ≤ i0 * r + j := by omega
      simp [h1, hj]
    · rw [blk_false ((blk_iff r i i0 j hj).not.2 hii), Bool.false_or]
      by_cases hle : i0 + 1 ≤ i
      · have e : i - i0 = (i - (i0 + 1)) + 1 := by omega
        rw [e, List.getD_cons_succ, List.length_cons]
        congr 1
        simp only [decide_eq_decide]
        omega
      · have h5 : decide (i0 + 1 ≤ i ∧ i < i0 + 1 + Es.length) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        have h6 : decide (i0 ≤ i ∧ i < i0 + (E :: Es).length) = false := by
          simp only [decide_eq_false_iff_not, List.length_cons]
          omega
        rw [h5, h6, Bool.false_and, Bool.false_and]

theorem ptB_catPl (Es : List (List ℕ)) (r i j : ℕ) (hj : j < r) (hi : i < Es.length) :
    ptB (catPl Es r) (i * r + j) = ptB (Es.getD i []) j := by
  funext c
  rw [ptB_eq, ptB_eq, nthN_catPl Es r c c.2]
  change bz ((catA r c Es 0).testBit (i * r + j)) = _
  rw [catA_testBit r c j hj Es 0 i, Nat.sub_zero]
  simp [hi]

theorem profAll_sound (X : ℕ) {U : List ℕ} (hl : lenN U = 156) (w FP : ℕ) (BL : List ℕ)
    (i : ℕ) : ∀ (ks ts : List ℕ), lenN ks = lenN ts →
    (∀ t ∈ ts, t = 0 ∨ t = 3 ∨ t = 4 ∨ t = 5) →
    ((profAll X ks ts U w FP BL).testBit i = true ↔
      i < w ∧ ∀ l < lenN ks, rhoB U (mapRows (CFSG.KC.Misc.E6Std.powB X (nthN ks l)) U) i FP BL =
        nthN ts l)
  | [], ts, _, _ => by
    change (full w).testBit i = true ↔ _
    rw [testBit_full]
    simp [lenN]
  | k :: ks, [], h, _ => by simp [lenN] at h
  | k :: ks, t :: ts, h, ht => by
    rw [lenN_cons, lenN_cons] at h
    change (forceN (profMask (CFSG.KC.Misc.E6Std.powB X k) U w t FP BL) fun m =>
      Nat.land m (profAll X ks ts U w FP BL)).testBit i = true ↔ _
    rw [forceN_eq]
    change (profMask _ U w t FP BL &&& profAll X ks ts U w FP BL).testBit i = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, profileMask_sound hl _ w t FP BL
      (ht t List.mem_cons_self) i, profAll_sound X hl w FP BL i ks ts (by omega)
      (fun t' h' => ht t' (List.mem_cons_of_mem _ h')), lenN_cons]
    constructor
    · rintro ⟨⟨hi, h0⟩, -, hall⟩
      refine ⟨hi, fun l hl => ?_⟩
      cases l with
      | zero => exact h0
      | succ l => exact hall l (by omega)
    · rintro ⟨hi, hall⟩
      exact ⟨⟨hi, hall 0 (by omega)⟩, hi, fun l hl => hall (l + 1) (by omega)⟩

end CFSG.KS.StdOdd.Chain

end
