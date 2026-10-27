module

public import Certificates.Data.Kernel.Co1BPair
public import CFSG.Certificates.Kernel.Co1BSpinSound

public section

namespace CFSG.KC.Co1BPair

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT CFSG.KC.F2W
  CFSG.EvenSporadicStandard.Co1Pair CFSG.Sporadic.Co1Schreier.Native CFSG.KC.Co1BSpin

@[expose] def rwIter (a : Array Nat) : Nat → Array (List Nat) × Nat → Array (List Nat) × Nat
  | 0, s => s
  | m + 1, s => rwIter a m (s.1.push (cpReadWord a s.2).1, (cpReadWord a s.2).2)

theorem fold_rw (a : Array Nat) : ∀ (l : List Nat) (q : Nat) (out : Array (List Nat)),
    List.foldl (fun b _ => ((cpReadWord a b.1).2, b.2.push (cpReadWord a b.1).1)) (q, out) l =
      ((rwIter a l.length (out, q)).2, (rwIter a l.length (out, q)).1)
  | [], _, _ => rfl
  | _ :: l, q, out => by
    rw [List.foldl_cons, fold_rw a l]
    rfl

theorem cpReadWords_eq (a : Array Nat) (m p : Nat) : cpReadWords a m p = rwIter a m (#[], p) := by
  unfold cpReadWords
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind]
  rw [fold_rw, List.length_range']
  rfl

theorem get!_toArray (l : List Nat) (i : Nat) : l.toArray[i]! = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem encW_cons (w : List Nat) (ws : List (List Nat)) : encW (w :: ws) = (w.length :: w) ++ encW ws := by
  simp [encW]

theorem cpReadWord_enc (pre rest w : List Nat) :
    cpReadWord (pre ++ ((w.length :: w) ++ rest)).toArray pre.length = (w, pre.length + 1 + w.length) := by
  unfold cpReadWord
  have h0 : (pre ++ ((w.length :: w) ++ rest)).toArray[pre.length]! = w.length := by
    rw [get!_toArray, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  rw [h0]
  refine Prod.ext ?_ rfl
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [get!_toArray, List.getD_append_right _ _ _ _ (by omega)]
  have : pre.length + 1 + i - pre.length = i + 1 := by omega
  rw [this, List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using h2),
    List.getD_eq_getElem _ _ (by simpa using h2)]

theorem rwIter_enc : ∀ (ws : List (List Nat)) (pre rest : List Nat) (out : Array (List Nat)),
    rwIter (pre ++ (encW ws ++ rest)).toArray ws.length (out, pre.length) =
      (out ++ ws.toArray, pre.length + (encW ws).length)
  | [], pre, rest, out => by simp [rwIter, encW]
  | w :: ws, pre, rest, out => by
    have e : pre ++ (encW (w :: ws) ++ rest) = (pre ++ (w.length :: w)) ++ (encW ws ++ rest) := by
      rw [encW_cons]
      simp
    rw [List.length_cons, rwIter]
    dsimp only
    have h1 : pre ++ (encW (w :: ws) ++ rest) = pre ++ ((w.length :: w) ++ (encW ws ++ rest)) := by
      rw [encW_cons]
      simp
    rw [h1, cpReadWord_enc, ← List.append_assoc]
    have hl : pre.length + 1 + w.length = (pre ++ (w.length :: w)).length := by simp; omega
    rw [hl, rwIter_enc ws (pre ++ (w.length :: w)) rest]
    rw [encW_cons]
    simp only [List.length_append, List.length_cons]
    refine Prod.ext ?_ ?_
    · simp
    · simp only
      omega

theorem readWords_enc (ws : List (List Nat)) (pre rest : List Nat) :
    cpReadWords (pre ++ (encW ws ++ rest)).toArray ws.length pre.length =
      (ws.toArray, pre.length + (encW ws).length) := by
  rw [cpReadWords_eq, rwIter_enc]
  simp

theorem lettersK_sound {lo hi : Nat} : ∀ {w : List Nat}, lettersK lo hi w = true →
    ∀ l ∈ w, lo ≤ l ∧ l < hi
  | [], _ => by simp
  | l :: w, h => by
    change CFSG.KLie.CT.andB (Nat.ble lo l) (CFSG.KLie.CT.andB (Nat.blt l hi) (lettersK lo hi w)) = true at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h3⟩ := andB_true h
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact ⟨Nat.le_of_ble_eq_true h1, Eq.mp Nat.blt_eq h2⟩
    · exact lettersK_sound h3 l' hl'

theorem wordsK_sound {M : Nat → Nat} {G : List Nat} {lo hi off : Nat} :
    ∀ {ws : List (List Nat)} {t : Nat}, wordsK M G lo hi off ws t = true →
      ∀ s (hs : s < ws.length), (∀ l ∈ ws[s], lo ≤ l ∧ l < hi) ∧
        unpackR 24 (M (off + (t + s))) = unpackR 24 (gwordFrom G ws[s] oneK)
  | [], _, _ => fun s hs => absurd hs (Nat.not_lt_zero _)
  | w :: ws, t, h => by
    change CFSG.KLie.CT.andB (lettersK lo hi w) (CFSG.KLie.CT.andB (eqK (M (Nat.add off t)) (gwordFrom G w oneK))
      (strictB (Nat.succ t) (wordsK M G lo hi off ws))) = true at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h3⟩ := andB_true h
    rw [strictB_eq'] at h3
    intro s hs
    cases s with
    | zero => exact ⟨lettersK_sound h1, beq_of_eqK h2⟩
    | succ s =>
      have := wordsK_sound h3 s (by simpa using hs)
      refine ⟨this.1, ?_⟩
      have e : off + (t + (s + 1)) = off + (Nat.succ t + s) := by omega
      rw [List.getElem_cons_succ, e]
      exact this.2

theorem levK_sound {M : Nat → Nat} {i : Nat} : ∀ {D : List Nat} {t : Nat}, levK M i D t = true →
    ∀ s (hs : s < D.length), chkK M i (t + s) D[s] = true
  | [], _, _ => fun s hs => absurd hs (Nat.not_lt_zero _)
  | p :: D, t, h => by
    change CFSG.KLie.CT.andB (chkK M i t p) (strictB (Nat.succ t) (levK M i D)) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    rw [strictB_eq'] at h2
    intro s hs
    cases s with
    | zero => exact h1
    | succ s =>
      have := levK_sound h2 s (by simpa using hs)
      have e : t + (s + 1) = Nat.succ t + s := by omega
      rw [List.getElem_cons_succ, e]
      exact this

theorem cpWord_eq {gens : Array (Array Nat)} {Gk : List Nat}
    (hG : ∀ l < Gk.length, gens[l]! = unpackR 24 (getL 0 Gk l)) {w : List Nat}
    (hw : ∀ l ∈ w, l < Gk.length) : cpWord gens w = unpackR 24 (gwordFrom Gk w oneK) := by
  rw [cpWord, one_eq]
  exact foldl_gword hG w hw oneK

theorem extract_mid (pre D rest : List Nat) :
    (pre ++ (D ++ rest)).toArray.extract pre.length (pre.length + D.length) = D.toArray := by
  apply Array.ext'
  simp [List.take_append_of_le_length]

end CFSG.KC.Co1BPair

end
