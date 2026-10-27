module

public import CFSG.Certificates.Kernel.StdOdd.ChainSound
public import Certificates.Data.Kernel.StdOdd.ChainRef

public section

namespace CFSG.KS.StdOdd.Chain

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit Matrix

theorem lenN_recL (f : ℕ → ℕ) : ∀ k c, lenN (Nat.rec (motive := fun _ => Nat → List Nat)
    (fun _ => List.nil) (fun _ ih c => List.cons (f c) (ih (Nat.succ c))) k c) = k
  | 0, _ => rfl
  | k + 1, c => congrArg Nat.succ (lenN_recL f k (c + 1))

theorem nthN_recL (f : ℕ → ℕ) : ∀ k c0 c, c < k → nthN (Nat.rec (motive := fun _ => Nat → List Nat)
    (fun _ => List.nil) (fun _ ih c => List.cons (f c) (ih (Nat.succ c))) k c0) c = f (c0 + c)
  | 0, _, c, h => absurd h (Nat.not_lt_zero c)
  | k + 1, c0, 0, _ => rfl
  | k + 1, c0, c + 1, h => by
    change nthN (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun _ ih c => List.cons (f c) (ih (Nat.succ c))) k (c0 + 1)) c = _
    rw [nthN_recL f k (c0 + 1) c (by omega)]
    congr 1
    omega

theorem lenN_splitPl (N bw w k : ℕ) : lenN (splitPl N bw w k) = k := by
  unfold splitPl
  rw [forceNL_eq]
  exact lenN_recL _ k 0

theorem lenN_vecsPl (vs : List ℕ) : lenN (vecsPl vs) = 156 := lenN_recL _ 156 0

theorem one_testBit (n : ℕ) : Nat.testBit 1 n = decide (0 = n) := Nat.testBit_two_pow (n := 0) (m := n)

theorem vecsRow_bit (c i : ℕ) : ∀ (vs : List ℕ) (r acc : ℕ),
    (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun v _ ih r acc =>
        forceN (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight v c) 1) r)) (ih (Nat.succ r)))
      vs r acc).testBit i =
      (acc.testBit i || (decide (r ≤ i) && decide (i < r + vs.length) && (nthN vs (i - r)).testBit c))
  | [], r, acc => by simp
  | v :: vs, r, acc => by
    change (forceN (acc ||| ((v >>> c) &&& 1) <<< r) (List.rec (motive := fun _ => Nat → Nat → Nat)
      (fun _ acc => acc) (fun v _ ih r acc =>
        forceN (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight v c) 1) r)) (ih (Nat.succ r)))
      vs (r + 1))).testBit i = _
    rw [forceN_eq, vecsRow_bit c i vs (r + 1), Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_and, Nat.testBit_shiftRight, one_testBit, List.length_cons, Bool.or_assoc]
    congr 1
    rcases Nat.lt_trichotomy i r with h | rfl | h
    · simp [show ¬ r ≤ i by omega, show ¬ r + 1 ≤ i by omega]
    · simp [nthN_cons_zero]
    · obtain ⟨d, rfl⟩ : ∃ d, i = r + 1 + d := ⟨i - (r + 1), by omega⟩
      have e : r + 1 + d - r = d + 1 := by omega
      simp only [e, nthN_cons_succ, show r + 1 + d - (r + 1) = d by omega,
        show r + (vs.length + 1) = r + 1 + vs.length by omega]
      simp [show r ≤ r + 1 + d by omega, show r + 1 ≤ r + 1 + d by omega]

theorem ptB_vecsPl (vs : List ℕ) {r : ℕ} (hr : r < vs.length) :
    ptB (vecsPl vs) r = vecB (nthN vs r) := by
  funext c
  rw [ptB_eq, vecB]
  congr 1
  change (nthN (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih c => List.cons (vecsRow vs c) (ih (Nat.succ c))) 156 0) c).testBit r = _
  rw [nthN_recL _ 156 0 c c.2, Nat.zero_add]
  change (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun v _ ih r acc =>
        forceN (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight v c) 1) r)) (ih (Nat.succ r)))
      vs 0 0).testBit r = _
  rw [vecsRow_bit]
  simp [hr]

theorem eqMaskV_sound {U : List ℕ} (hl : lenN U = 156) (v w i : ℕ) :
    (eqMaskV U v w).testBit i = true ↔ i < w ∧ ptB U i = vecB v := by
  rw [eqMaskV, andNot_testBit, testBit_full]
  have := neqV_sound hl v w i
  by_cases hi : i < w
  · by_cases he : ptB U i = vecB v
    · have : (neqV U v w).testBit i = false := by
        cases h : (neqV U v w).testBit i
        · rfl
        · exact absurd ((neqV_sound hl v w i).1 h).2 (not_not.2 he)
      simp [hi, he, this]
    · have : (neqV U v w).testBit i = true := (neqV_sound hl v w i).2 ⟨hi, he⟩
      simp [hi, he, this]
  · simp [hi]

theorem allIn_aux (U : List ℕ) (w i : ℕ) : ∀ (vs : List ℕ) (acc : ℕ),
    (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun v _ ih acc => forceN (Nat.land acc (neqV U v w)) ih) vs acc).testBit i =
      (acc.testBit i && vs.all fun v => (neqV U v w).testBit i)
  | [], acc => by simp
  | v :: vs, acc => by
    change (forceN (acc &&& neqV U v w) (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun v _ ih acc => forceN (Nat.land acc (neqV U v w)) ih) vs)).testBit i = _
    rw [forceN_eq, allIn_aux U w i vs, Nat.testBit_and, List.all_cons, Bool.and_assoc]

theorem allIn_sound {U vs : List ℕ} (hl : lenN U = 156) {w : ℕ} (h : allIn U vs w = true) :
    ∀ i < w, ∃ v ∈ vs, ptB U i = vecB v := by
  intro i hi
  have h0 := Nat.eq_of_beq_eq_true h
  have hb := congrArg (fun x => x.testBit i) h0
  rw [allIn_aux, Nat.zero_testBit, testBit_full, decide_eq_true hi, Bool.true_and,
    List.all_eq_false] at hb
  obtain ⟨v, hv, hn⟩ := hb
  refine ⟨v, hv, ?_⟩
  by_contra hne
  exact hn ((neqV_sound hl v w i).2 ⟨hi, hne⟩)

theorem refMask_aux (U : List ℕ) (w i : ℕ) : ∀ (vs st : List ℕ) (acc : ℕ),
    (List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
      (fun v _ ih st acc => List.rec (motive := fun _ => Nat) acc
        (fun s st' _ => Bool.rec (motive := fun _ => Nat) (ih st' acc)
          (forceN (Nat.lor acc (eqMaskV U v w)) (ih st')) (Nat.beq s 1)) st) vs st acc).testBit i =
      true →
      acc.testBit i = true ∨ ∃ r < lenN vs, nthN st r = 1 ∧ (eqMaskV U (nthN vs r) w).testBit i = true
  | [], st, acc, h => Or.inl h
  | v :: vs, [], acc, h => Or.inl h
  | v :: vs, s :: st, acc, h => by
    change (Bool.rec (motive := fun _ => Nat) (List.rec (motive := fun _ => List Nat → Nat → Nat)
      (fun _ acc => acc) (fun v _ ih st acc => List.rec (motive := fun _ => Nat) acc
        (fun s st' _ => Bool.rec (motive := fun _ => Nat) (ih st' acc)
          (forceN (Nat.lor acc (eqMaskV U v w)) (ih st')) (Nat.beq s 1)) st) vs st acc)
      (forceN (Nat.lor acc (eqMaskV U v w)) (List.rec (motive := fun _ => List Nat → Nat → Nat)
      (fun _ acc => acc) (fun v _ ih st acc => List.rec (motive := fun _ => Nat) acc
        (fun s st' _ => Bool.rec (motive := fun _ => Nat) (ih st' acc)
          (forceN (Nat.lor acc (eqMaskV U v w)) (ih st')) (Nat.beq s 1)) st) vs st))
      (Nat.beq s 1)).testBit i = true at h
    cases hs : Nat.beq s 1
    · rw [hs] at h
      rcases refMask_aux U w i vs st acc h with h | ⟨r, hr, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨r + 1, by rw [lenN_cons]; omega, h1, h2⟩
    · rw [hs, forceN_eq] at h
      rcases refMask_aux U w i vs st _ h with h | ⟨r, hr, h1, h2⟩
      · change (acc ||| eqMaskV U v w).testBit i = true at h
        rw [Nat.testBit_or, Bool.or_eq_true] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨0, by rw [lenN_cons]; omega, Nat.eq_of_beq_eq_true hs, h⟩
      · exact Or.inr ⟨r + 1, by rw [lenN_cons]; omega, h1, h2⟩

theorem refMask_sound {U : List ℕ} (hl : lenN U = 156) (vs st : List ℕ) (w i : ℕ)
    (h : (refMask U vs st w).testBit i = true) :
    ∃ r < lenN vs, nthN st r = 1 ∧ i < w ∧ ptB U i = vecB (nthN vs r) := by
  rcases refMask_aux U w i vs st 0 h with h0 | ⟨r, hr, h1, h2⟩
  · rw [Nat.zero_testBit] at h0
    cases h0
  · exact ⟨r, hr, h1, (eqMaskV_sound hl _ w i).1 h2⟩

theorem fixesOK_sound {M : ℕ} {vs : List ℕ} {i : ℕ} (h : fixesOK M vs i = true) :
    ∀ j < i, j < vs.length → matB M *ᵥ vecB (nthN vs j) = vecB (nthN vs j) := by
  intro j hj hjl
  unfold fixesOK at h
  rw [forceLB_eq] at h
  have h0 := Nat.eq_of_beq_eq_true h
  have hb := congrArg (fun x => x.testBit j) h0
  have hlen : lenN (mapRows M (vecsPl vs)) = lenN (vecsPl vs) := by
    rw [lenN_mapRows, lenN_vecsPl]
  change (neqMask (mapRows M (vecsPl vs)) (vecsPl vs) &&& full i).testBit j = Nat.testBit 0 j at hb
  rw [Nat.testBit_and, neqMask_sound hlen, testBit_full, decide_eq_true hj, Bool.and_true,
    Nat.zero_testBit, Bool.not_eq_false'] at hb
  have he := (eqB_iff (by rw [lenN_mapRows]) (lenN_vecsPl vs) j).1 hb
  rw [planeApply_sound (lenN_vecsPl vs), ptB_vecsPl vs hjl] at he
  exact he

theorem siftK_sound {βs : List ℕ} {k : List ℕ → Bool} : ∀ (Ls : List (List ℕ))
    (Ss : List (List (List ℕ))) (j : ℕ) (T : List ℕ), lenN T = 156 → siftK Ls Ss βs j T k = true →
    ∃ Tl : ℕ → List ℕ, Tl 0 = T ∧ (∀ l, lenN (Tl l) = 156) ∧ k (Tl Ls.length) = true ∧
      ∀ l < Ls.length, (∀ i, ptB (Tl (l + 1)) i =
        walkElt (Ls.getD l []) (Ss.getD l []) i *ᵥ ptB (Tl l) i) ∧
        ptB (Tl (l + 1)) (j + l) = vecB (nthN βs (j + l))
  | [], Ss, j, T, hl, h => ⟨fun _ => T, rfl, fun _ => hl, h, fun l hl' => absurd hl' (by simp)⟩
  | Ms :: Ls, [], j, T, hl, h => by
    change false = true at h
    exact absurd h (by decide)
  | Ms :: Ls, S :: Ss, j, T, hl, h => by
    change walkK Ms S T (fun T' =>
        andB (Nat.beq (Nat.land (neqV T' (nthN βs j) (Nat.succ j)) (Nat.shiftLeft 1 j)) 0)
          (siftK Ls Ss βs (Nat.succ j) T' k)) = true at h
    obtain ⟨V, hk, hV, hpt⟩ := walkK_sound S T hl h
    rw [andB_eq, Bool.and_eq_true] at hk
    obtain ⟨h1, h2⟩ := hk
    obtain ⟨Tl, h0, hlen, hend, hstep⟩ := siftK_sound Ls Ss (j + 1) V hV h2
    have hj : ptB V j = vecB (nthN βs j) := by
      by_contra hne
      have hb := (neqV_sound hV (nthN βs j) (j + 1) j).2 ⟨by omega, hne⟩
      have h0' := congrArg (fun x => x.testBit j) (Nat.eq_of_beq_eq_true h1)
      change ((neqV V (nthN βs j) (j + 1)) &&& (1 <<< j)).testBit j = (0 : ℕ).testBit j at h0'
      rw [Nat.testBit_and, hb, Nat.testBit_shiftLeft, Nat.zero_testBit] at h0'
      simp at h0'
    refine ⟨fun l => Nat.rec T (fun l _ => Tl l) l, rfl, fun l => ?_, ?_, fun l hl' => ?_⟩
    · cases l
      · exact hl
      · exact hlen _
    · change k (Tl Ls.length) = true
      exact hend
    · cases l with
      | zero =>
        refine ⟨fun i => ?_, ?_⟩
        · change ptB (Tl 0) i = _
          rw [h0, hpt i]
          rfl
        · change ptB (Tl 0) (j + 0) = _
          rw [h0, Nat.add_zero, hj]
      | succ l =>
        have hl2 : l < Ls.length := by simp at hl'; omega
        obtain ⟨hs1, hs2⟩ := hstep l hl2
        refine ⟨fun i => ?_, ?_⟩
        · change ptB (Tl (l + 1)) i = walkElt (Ls.getD l []) (Ss.getD l []) i *ᵥ ptB (Tl l) i
          exact hs1 i
        · change ptB (Tl (l + 1)) (j + (l + 1)) = _
          rw [show j + (l + 1) = j + 1 + l by omega]
          exact hs2

end CFSG.KS.StdOdd.Chain

end
