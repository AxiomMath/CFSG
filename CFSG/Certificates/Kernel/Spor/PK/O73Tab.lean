module

public import CFSG.Certificates.Kernel.Spor.PK.O73Mat
public import CFSG.Certificates.Kernel.Spor.PK.MiscPerm
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.PK

open CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.LieType.Multipliers.O73 CFSG.YGroups.ModelNative
  CFSG.Monster.B.Co2.Native Matrix

private theorem allLt_iff' {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

private theorem getElem!_ofFn' {m : Nat} (f : Fin m → Nat) {i : Nat} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

private theorem idA_get' {n i : Nat} (hi : i < n) : (idA n)[i]! = i := by
  rw [idA, getElem!_ofFn' _ hi]

private theorem map_toArray_get {α β : Type} [Inhabited β] (f : α → β) (L : List α) {c : Nat}
    (hc : c < L.length) : (L.map f).toArray[c]! = f L[c] := by
  rw [getElem!_pos _ _ (by simpa using hc)]
  simp

theorem tabOf_size (A : Matrix Idx Idx (ZMod 3)) : (tabOf A).size = 2187 := by
  unfold tabOf
  exact Array.size_ofFn

theorem tabOf_get (A : Matrix Idx Idx (ZMod 3)) {x : Nat} (hx : x < 2187) :
    (tabOf A)[x]! = code (A *ᵥ dec x) := by
  unfold tabOf
  exact getElem!_ofFn' (fun x : Fin 2187 => code (A *ᵥ dec x.val)) hx

theorem tabOf_mul (A B : Matrix Idx Idx (ZMod 3)) :
    tabOf (A * B) = compA 2187 (tabOf A) (tabOf B) := by
  have h : ∀ x : Fin 2187,
      code ((A * B) *ᵥ dec x.val) = (tabOf A)[(tabOf B)[x.val]!]! := by
    intro x
    rw [tabOf_get B x.2, tabOf_get A (code_lt _), dec_code, Matrix.mulVec_mulVec]
  exact congrArg Array.ofFn (funext h)

theorem tabOf_one : tabOf 1 = idA 2187 := by
  have h : ∀ x : Fin 2187, code ((1 : Matrix Idx Idx (ZMod 3)) *ᵥ dec x.val) = x.val := by
    intro x
    rw [Matrix.one_mulVec, code_dec x.2]
  exact congrArg Array.ofFn (funext h)

theorem eqA_tabOf_iff (A B : Matrix Idx Idx (ZMod 3)) :
    eqA 2187 (tabOf A) (tabOf B) = true ↔ A = B := by
  unfold eqA
  rw [allLt_iff']
  constructor
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro v
    have hv := h (code v) (code_lt v)
    simp only [beq_iff_eq] at hv
    rw [tabOf_get A (code_lt v), tabOf_get B (code_lt v), dec_code] at hv
    have := congrArg dec hv
    rwa [dec_code, dec_code] at this
  · rintro rfl i _
    exact beq_self_eq_true _

private theorem set_loop' {N v : Nat} {D : Array Nat} :
    ∀ {m : Nat}, (∀ i < m, D[i]! < N) → (∀ i < m, ∀ j < i, D[j]! ≠ D[i]!) →
      ((List.range' 0 m).foldl (fun p i => p.set! D[i]! i) (Array.replicate N v)).size = N ∧
      ∀ i < m,
        ((List.range' 0 m).foldl (fun p i => p.set! D[i]! i) (Array.replicate N v))[D[i]!]! = i
  | 0, _, _ => ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | m + 1, hD, hd => by
    obtain ⟨hs, hv⟩ := set_loop' (N := N) (v := v) (D := D) (m := m) (fun i hi => hD i (by omega))
      (fun i hi j hj => hd i (by omega) j hj)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add]
    generalize (List.range' 0 m).foldl (fun p i => p.set! D[i]! i) (Array.replicate N v) = q
      at hs hv
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

private theorem invCand_get {n : Nat} {T : Nat → Nat} (hT : IsPermN n T) {y : Nat} (hy : y < n) :
    (invCand n (Array.ofFn (n := n) fun i => T i.val))[y]! = finv n T y := by
  have hget : ∀ i < n, (Array.ofFn (n := n) fun i => T i.val)[i]! = T i := fun i hi =>
    getElem!_ofFn' (fun i : Fin n => T i.val) hi
  have hD : ∀ i < n, (Array.ofFn (n := n) fun i => T i.val)[i]! < n := fun i hi => by
    rw [hget i hi]
    exact hT.1 i hi
  have hd : ∀ i < n, ∀ j < i, (Array.ofFn (n := n) fun i => T i.val)[j]! ≠
      (Array.ofFn (n := n) fun i => T i.val)[i]! := fun i hi j hj e => by
    rw [hget i hi, hget j (by omega)] at e
    have := hT.2 j (by omega) i hi e
    omega
  have heq : invCand n (Array.ofFn (n := n) fun i => T i.val) =
      (List.range' 0 n).foldl (fun p i => p.set! (Array.ofFn (n := n) fun i => T i.val)[i]! i)
        (Array.replicate n 0) := by
    unfold invCand
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  obtain ⟨hx, hTx⟩ := finv_spec hT hy
  rw [heq]
  conv_lhs => rw [← hTx]
  rw [← hget _ hx, (set_loop' hD hd).2 _ hx]

private theorem isInvA_ofFn {n : Nat} {T : Nat → Nat} (hT : IsPermN n T) :
    isInvA n (Array.ofFn (n := n) fun i => T i.val)
      (invCand n (Array.ofFn (n := n) fun i => T i.val)) = true := by
  unfold isInvA
  rw [allLt_iff']
  intro i hi
  have h1 : (Array.ofFn (n := n) fun i => T i.val)[i]! = T i :=
    getElem!_ofFn' (fun i : Fin n => T i.val) hi
  have h2 := hT.1 i hi
  rw [h1, invCand_get hT h2, finv_apply hT hi]
  simp [h2]

theorem permsOK_tabOf (Ms : List (Matrix Idx Idx (ZMod 3))) (h : ∀ M ∈ Ms, M * M = 1) :
    permsOK 2187 (Ms.map tabOf).toArray = true := by
  unfold permsOK
  rw [allLt_iff']
  intro c hc
  have hc' : c < Ms.length := by simpa using hc
  rw [map_toArray_get _ _ hc']
  have hM := h _ (List.getElem_mem hc')
  refine isInvA_ofFn (T := fun x => code (Ms[c] *ᵥ dec x)) ⟨fun x _ => code_lt _, ?_⟩
  have hTT : ∀ x < 2187, code (Ms[c] *ᵥ dec (code (Ms[c] *ᵥ dec x))) = x := by
    intro x hx
    rw [dec_code, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec, code_dec hx]
  intro x hx y hy hxy
  have h1 := hTT x hx
  have h2 := hTT y hy
  simp only at hxy
  rw [hxy] at h1
  exact h1.symm.trans h2

theorem evalW_tabOf (Ms : List (Matrix Idx Idx (ZMod 3))) (w : List Nat) :
    evalW 2187 (Ms.map tabOf).toArray w = tabOf (wordMat Ms w) := by
  induction w with
  | nil => exact tabOf_one.symm
  | cons c w ih =>
    have hl : letterOf 2187 (Ms.map tabOf).toArray c =
        tabOf (if c < Ms.length then Ms.getD c 1 else 1) := by
      unfold letterOf
      by_cases hc : c < Ms.length
      · have hc0 : Ms.getD c 1 = Ms[c] := by simp [List.getD_eq_getElem?_getD, hc]
        rw [if_pos (by simpa using hc), if_pos hc, map_toArray_get _ _ hc, hc0]
      · rw [if_neg (by simpa using hc), if_neg hc, tabOf_one]
    show compA 2187 (letterOf 2187 (Ms.map tabOf).toArray c)
      (evalW 2187 (Ms.map tabOf).toArray w) =
      tabOf ((if c < Ms.length then Ms.getD c 1 else 1) * wordMat Ms w)
    rw [tabOf_mul, ih, hl]

@[expose] def unpackA (n w P : Nat) : Array Nat := Array.ofFn (n := n) fun i => fd w P i

theorem permsOK_unpack {n w : Nat} {Ps : List Nat} (h : ∀ P ∈ Ps, permK n w P = true) :
    permsOK n (Ps.map (unpackA n w)).toArray = true := by
  unfold permsOK
  rw [allLt_iff']
  intro c hc
  have hc' : c < Ps.length := by simpa using hc
  rw [map_toArray_get _ _ hc']
  have hP := (permK_iff.1 (h _ (List.getElem_mem hc'))).2
  exact isInvA_ofFn (T := fd w Ps[c]) hP

private theorem wordPF_lt' {n w : Nat} (hw : n ≤ 2 ^ w) (Ps : List Nat)
    (hPs : ∀ c < Ps.length, ∀ x < n, fd w (Ps.getD c 0) x < n) (wd : List Nat) :
    ∀ x < n, wordPF w Ps wd x < n := by
  induction wd with
  | nil => intro x hx; exact hx
  | cons c wd ih =>
    intro x hx
    show (if c < Ps.length then fd w (Ps.getD c 0) (wordPF w Ps wd x) else wordPF w Ps wd x) < n
    by_cases hc : c < Ps.length
    · rw [if_pos hc]
      exact hPs c hc _ (ih x hx)
    · rw [if_neg hc]
      exact ih x hx

theorem evalW_unpack {n w : Nat} (hw : n ≤ 2 ^ w) {Ps : List Nat} (h : ∀ P ∈ Ps, permK n w P = true)
    (wd : List Nat) :
    evalW n (Ps.map (unpackA n w)).toArray wd = unpackA n w (CFSG.KC.Misc.O73.wordP n w Ps wd) := by
  have hPs : ∀ c < Ps.length, ∀ x < n, fd w (Ps.getD c 0) x < n := by
    intro c hc x hx
    have hc0 : Ps.getD c 0 = Ps[c] := by simp [List.getD_eq_getElem?_getD, hc]
    rw [hc0]
    exact ((permK_iff.1 (h _ (List.getElem_mem hc))).2).1 x hx
  have hlt := wordPF_lt' hw Ps hPs
  have key : ∀ wd : List Nat, evalW n (Ps.map (unpackA n w)).toArray wd =
      Array.ofFn (n := n) fun i => wordPF w Ps wd i.val := by
    intro wd
    induction wd with
    | nil => rfl
    | cons c wd ih =>
      show compA n (letterOf n (Ps.map (unpackA n w)).toArray c)
        (evalW n (Ps.map (unpackA n w)).toArray wd) = _
      rw [ih]
      unfold compA
      refine congrArg Array.ofFn (funext fun i => ?_)
      have hxn : wordPF w Ps wd i.val < n := hlt wd i.val i.2
      rw [getElem!_ofFn' (fun i : Fin n => wordPF w Ps wd i.val) i.2]
      show (letterOf n (Ps.map (unpackA n w)).toArray c)[wordPF w Ps wd i.val]! =
        (if c < Ps.length then fd w (Ps.getD c 0) (wordPF w Ps wd i.val)
          else wordPF w Ps wd i.val)
      generalize wordPF w Ps wd i.val = x at hxn ⊢
      unfold letterOf
      by_cases hc : c < Ps.length
      · have hc0 : Ps.getD c 0 = Ps[c] := by simp [List.getD_eq_getElem?_getD, hc]
        rw [if_pos (by simpa using hc), if_pos hc, map_toArray_get _ _ hc, unpackA,
          getElem!_ofFn' _ hxn, hc0]
      · rw [if_neg (by simpa using hc), if_neg hc, idA_get' hxn]
  rw [wordP_eq_of_maps hw Ps hPs wd, key wd, unpackA]
  refine congrArg Array.ofFn (funext fun i => ?_)
  exact (fd_enc (fun j hj => Nat.lt_of_lt_of_le (hlt wd j hj) hw) i.2).symm

theorem eqA_unpack_idP {n w P : Nat} (hw : n ≤ 2 ^ w) (hP : P < 2 ^ (w * n)) :
    eqA n (unpackA n w P) (idA n) = true ↔ P = idP n w := by
  rw [idP_eq hw]
  unfold eqA
  rw [allLt_iff']
  have hlt : enc w (fun x => x) n < 2 ^ (w * n) := enc_lt (fun i hi => Nat.lt_of_lt_of_le hi hw)
  have hfd : ∀ i < n, fd w (enc w (fun x => x) n) i = i :=
    fun i hi => fd_enc (fun j hj => Nat.lt_of_lt_of_le hj hw) hi
  constructor
  · intro h
    refine eq_of_fd_eq hP hlt fun i hi => ?_
    have := h i hi
    simp only [beq_iff_eq] at this
    rw [unpackA, getElem!_ofFn' _ hi, idA_get' hi] at this
    rw [hfd i hi]
    exact this
  · rintro rfl i hi
    simp only [beq_iff_eq]
    rw [unpackA, getElem!_ofFn' _ hi, idA_get' hi]
    exact hfd i hi

end CFSG.KS.PK

end
