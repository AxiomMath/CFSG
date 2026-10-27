module

public import CFSG.Sporadic.HNOddCore.CCheckInputs
public import CFSG.Sporadic.HNSchreier.BFSList
public import CFSG.Sporadic.Schreier.ONPermArr
public import CFSG.Certificates.Kernel.Spor.CBfsKSound
public import CFSG.Certificates.Kernel.Spor.ChainKGen
public import Mathlib

public section

namespace CFSG.KS.BfsPar

open CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNSchreier CFSG.ONSchreier
open CFSG.ONSchreier.Native

theorem prep_pinvCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : PRep n t g) :
    PRep n (pinvCand n t) g⁻¹ ∧ pisInv n t (pinvCand n t) = true := by
  have hu : ∀ i < n, t[i]! = (Array.ofFn (n := n) fun i => ((g i : Fin n) : ℕ))[i]! := fun i hi => by
    rw [h.apply hi, getElem!_ofFn_nat _ hi]
  let T : ℕ → ℕ := fun x => if hx : x < n then ((g ⟨x, hx⟩ : Fin n) : ℕ) else x
  let U : ℕ → ℕ := fun x => if hx : x < n then ((g⁻¹ ⟨x, hx⟩ : Fin n) : ℕ) else x
  have hT : ∀ x < n, T x < n := fun x hx => by simp [T, hx]
  have hUT : ∀ x < n, U (T x) = x := fun x hx => by simp [T, U, hx]
  have hof : (Array.ofFn (n := n) fun i => ((g i : Fin n) : ℕ)) =
      Array.ofFn (n := n) fun i => T i.val := by
    congr 1
    funext i
    simp [T, i.isLt]
  have hget : ∀ y < n, (pinvCand n t)[y]! = U y := fun y hy => by
    rw [CFSG.KS.CH.pinvCand_eq_of_agree hu, hof]
    exact CFSG.KS.CB.pinvCand_get hT hUT hy
  have hinv : PRep n (pinvCand n t) g⁻¹ := fun x => by
    rw [hget x x.isLt]
    simp [U]
  refine ⟨hinv, allBelowN_iff.2 fun i hi => ?_⟩
  rw [h.apply hi, hinv.apply (g ⟨i, hi⟩).isLt]
  simp

@[expose] def parStep (a0 a1 : Array ℕ) (st : Array ℕ × Array Bool) (i : ℕ) :
    Array ℕ × Array Bool :=
  let st₁ := if !st.2[a0[i]!]! then (st.1.set! a0[i]! (2 * i), st.2.set! a0[i]! true) else st
  if !st₁.2[a1[i]!]! then (st₁.1.set! a1[i]! (2 * i + 1), st₁.2.set! a1[i]! true) else st₁

theorem bfsPar_eq (n : ℕ) (a0 a1 : Array ℕ) :
    bfsPar n a0 a1 = ((List.range n).foldl (parStep a0 a1)
      (Array.replicate n 0, (Array.replicate n false).set! 0 true)).1 := by
  unfold bfsPar
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range', Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize (Array.replicate n 0, (Array.replicate n false).set! 0 true) = s
  generalize List.range' 0 n = l
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.foldl_cons, ← ih (parStep a0 a1 s a)]
    unfold parStep
    split_ifs <;> simp_all

@[expose] def Good (α β : ℕ → ℕ) (p j : ℕ) : Prop :=
  p / 2 < j ∧ if p % 2 = 0 then α (p / 2) = j else β (p / 2) = j

@[expose] def Inv (n : ℕ) (α β : ℕ → ℕ) (m : ℕ) (st : Array ℕ × Array Bool) : Prop :=
  st.1.size = n ∧ st.2.size = n ∧ (∀ j < n, st.2[j]! = decide (j < m)) ∧
    ∀ j, 0 < j → j < m → Good α β st.1[j]! j

theorem get_set_ne {α : Type} [Inhabited α] (a : Array α) {i j : ℕ} (v : α) (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  rcases Nat.lt_or_ge j a.size with hj | hj
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj,
      Array.getElem_setIfInBounds_ne hj h]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j (by omega)]

theorem get_set_self {α : Type} [Inhabited α] (a : Array α) {i : ℕ} (v : α) (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ i (by simpa using h),
    Array.getElem_setIfInBounds_self]

theorem inv_add {n : ℕ} {α β : ℕ → ℕ} {m x v : ℕ} {st : Array ℕ × Array Bool}
    (hI : Inv n α β m st) (hx : x ≤ m) (hxn : x < n) (hv : x = m → Good α β v x) :
    Inv n α β (max m (x + 1))
      (if !st.2[x]! then (st.1.set! x v, st.2.set! x true) else st) := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  rcases Nat.lt_or_eq_of_le hx with hlt | rfl
  · have hs : st.2[x]! = true := by rw [h3 x hxn]; simp [hlt]
    rw [hs, max_eq_left (by omega)]
    exact ⟨h1, h2, h3, h4⟩
  · have hs : st.2[x]! = false := by rw [h3 x hxn]; simp
    rw [hs, max_eq_right (by omega)]
    simp only [Bool.not_false, if_true]
    refine ⟨by simp [h1], by simp [h2], fun j hj => ?_, fun j hj0 hj => ?_⟩
    · rcases Nat.lt_trichotomy j x with a | rfl | a
      · rw [get_set_ne _ _ (by omega), h3 j hj]
        simp [a, Nat.lt_succ_of_lt a]
      · rw [get_set_self _ _ (by omega)]
        simp
      · rw [get_set_ne _ _ (by omega), h3 j hj]
        simp only [decide_eq_decide]
        omega
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with a | rfl
      · rw [get_set_ne _ _ (by omega)]
        exact h4 j hj0 a
      · rw [get_set_self _ _ (by omega)]
        exact hv rfl

theorem inv_range {n : ℕ} {α β : ℕ → ℕ} {a0 a1 : Array ℕ}
    (ha0 : ∀ i < n, a0[i]! = α i) (ha1 : ∀ i < n, a1[i]! = β i)
    (hlt : ∀ i < n, α i < n ∧ β i < n) (hord : BfsOrder α β n) :
    ∀ q ≤ n, Inv n α β (ordState α β q).2 ((List.range q).foldl (parStep a0 a1)
      (Array.replicate n 0, (Array.replicate n false).set! 0 true)) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have := hord.2
      simp [ordState] at this
    · exact h
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨by simp, by simp, fun j hj => ?_, fun j hj0 hj => ?_⟩
    · have e : (ordState α β 0).2 = 1 := rfl
      rw [e, List.range_zero, List.foldl_nil]
      rcases Nat.eq_zero_or_pos j with rfl | h
      · rw [get_set_self _ _ (by simpa using hn)]
        simp
      · rw [get_set_ne _ _ (by omega), getElem!_pos _ j (by simpa using hj)]
        simp only [Array.getElem_replicate]
        simp only [false_eq_decide_iff]
        omega
    · simp [ordState] at hj
      omega
  | succ q ih =>
    intro hq
    have hI := ih (by omega)
    obtain ⟨-, hqm, hαm, hβm⟩ := ordState_flag_of_succ (ordState_flag_mono hord.1 (q + 1) hq)
    have hst : (ordState α β (q + 1)).2 =
        max (max (ordState α β q).2 (α q + 1)) (β q + 1) := by
      rw [ordState_succ]; rfl
    rw [hst, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hαn, hβn⟩ := hlt q (by omega)
    unfold parStep
    simp only
    rw [ha0 q (by omega), ha1 q (by omega)]
    have h1 := inv_add (v := 2 * q) hI hαm hαn fun e => by
      refine ⟨by omega, ?_⟩
      rw [if_pos (by omega)]
      congr 1
      omega
    exact inv_add (v := 2 * q + 1) h1 hβm hβn fun e => by
      refine ⟨by omega, ?_⟩
      rw [if_neg (by omega)]
      congr 1
      omega

theorem bfsPar_good {n : ℕ} {α β : ℕ → ℕ} {a0 a1 : Array ℕ}
    (ha0 : ∀ i < n, a0[i]! = α i) (ha1 : ∀ i < n, a1[i]! = β i)
    (hlt : ∀ i < n, α i < n ∧ β i < n) (hord : BfsOrder α β n) :
    ∀ j, 0 < j → j < n → Good α β (bfsPar n a0 a1)[j]! j := by
  have h := (inv_range ha0 ha1 hlt hord n le_rfl).2.2.2
  rw [hord.2] at h
  rw [bfsPar_eq]
  exact h

@[expose] def tabOf (cA cB : Array ℕ) (p : ℕ) : Array ℕ := if p % 2 == 0 then cA else cB

@[expose] def recStep (par cA cB : Array ℕ) (arr : Array ℕ) (j : ℕ) : Array ℕ :=
  arr.set! j (tabOf cA cB par[j]!)[arr[par[j]! / 2]!]!

theorem cRecArr_eq (n : ℕ) (par cA cB : Array ℕ) :
    cRecArr n par cA cB = (List.range' 1 (n - 1)).foldl (recStep par cA cB)
      (Array.replicate n 0) := by
  unfold cRecArr
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure]
  exact rfl

theorem cRec_spec {n : ℕ} {α β : ℕ → ℕ} {a0 a1 cA cB : Array ℕ}
    (ha0 : ∀ i < n, a0[i]! = α i) (ha1 : ∀ i < n, a1[i]! = β i)
    (hlt : ∀ i < n, α i < n ∧ β i < n) (hord : BfsOrder α β n) {f : ℕ → ℕ} (hf0 : f 0 = 0)
    (hfa : ∀ i < n, f (α i) = cA[f i]!) (hfb : ∀ i < n, f (β i) = cB[f i]!) :
    (cRecArr n (bfsPar n a0 a1) cA cB).size = n ∧
      (∀ j < n, (cRecArr n (bfsPar n a0 a1) cA cB)[j]! = f j) ∧
      cRecOK n a0 a1 (bfsPar n a0 a1) cA cB (cRecArr n (bfsPar n a0 a1) cA cB) = true := by
  have hG := bfsPar_good ha0 ha1 hlt hord
  set par := bfsPar n a0 a1
  have hrec : ∀ j, 0 < j → j < n →
      f j = (tabOf cA cB par[j]!)[f (par[j]! / 2)]! := fun j hj0 hj => by
    obtain ⟨hp, hs⟩ := hG j hj0 hj
    unfold tabOf
    split_ifs at hs with h2
    · rw [if_pos (by simpa using h2), ← hfa _ (by omega), hs]
    · rw [if_neg (by simpa using h2), ← hfb _ (by omega), hs]
  have key : ∀ k, k + 1 ≤ n →
      ((List.range' 1 k).foldl (recStep par cA cB) (Array.replicate n 0)).size = n ∧
      ∀ i < k + 1, ((List.range' 1 k).foldl (recStep par cA cB) (Array.replicate n 0))[i]! =
        f i := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨by simp, fun i hi => ?_⟩
      have : i = 0 := by omega
      subst this
      rw [getElem!_pos _ 0 (by simp; omega), hf0]
      simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hv⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set c := (List.range' 1 k).foldl (recStep par cA cB) (Array.replicate n 0)
      have e1 : 1 + 1 * k = k + 1 := by omega
      rw [e1]
      simp only [recStep]
      constructor
      · simp [hs]
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with a | rfl
      · rw [get_set_ne _ _ (by omega)]
        exact hv i a
      · rw [get_set_self _ _ (by omega), hv _ (hG (k + 1) (by omega) (by omega)).1,
          ← hrec (k + 1) (by omega) (by omega)]
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have := hord.2
      simp [ordState] at this
    · exact h
  obtain ⟨hs, hv⟩ := key (n - 1) (by omega)
  rw [← cRecArr_eq] at hs hv
  have hv' : ∀ j < n, (cRecArr n par cA cB)[j]! = f j := fun j hj => hv j (by omega)
  refine ⟨hs, hv', ?_⟩
  unfold cRecOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hs, by rw [hv' 0 hn, hf0]⟩, allBelowN_iff.2 fun j hj => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · have hj' : (j == 0) = false := beq_eq_false_iff_ne.2 (by omega)
    rw [hj', Bool.false_or]
    obtain ⟨hp, hsd⟩ := hG j hj0 hj
    unfold cRecStep
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hp, ?_⟩
    rw [hv' j hj, hv' _ (by omega), hrec j hj0 hj]
    unfold tabOf
    by_cases h2 : par[j]! % 2 = 0
    · rw [if_pos h2] at hsd
      have hb : (par[j]! % 2 == 0) = true := by simpa using h2
      simp [hb, ha0 _ (show par[j]! / 2 < n by omega), hsd]
    · rw [if_neg h2] at hsd
      have hb : (par[j]! % 2 == 0) = false := by simpa using h2
      simp [hb, ha1 _ (show par[j]! / 2 < n by omega), hsd]

end CFSG.KS.BfsPar
