module

public import CFSG.Certificates.Kernel.Census.SoundProof
public import Certificates.Data.Kernel.Census.PackedF

public section

namespace CFSG.KC.Census.SP

open CFSG.KC.Enum CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

variable {n w : Nat}

theorem pslpIdx_eq : ∀ (k : Nat) (prog : List (Nat × Nat)), pslpIdxOK k prog = slpIdxOK k prog
  | _, [] => rfl
  | k, ij :: l => by
    have e1 : Nat.blt ij.1 k = decide (ij.1 < k) := by
      apply Bool.eq_iff_iff.mpr
      rw [Nat.blt_eq, decide_eq_true_eq]
    have e2 : Nat.blt ij.2 k = decide (ij.2 < k) := by
      apply Bool.eq_iff_iff.mpr
      rw [Nat.blt_eq, decide_eq_true_eq]
    rw [pslpIdxOK, slpIdxOK, e1, e2, pslpIdx_eq (k + 1) l]

theorem unpackP_zero_get (x : Nat) : (unpackP n w 0)[x]! = 0 := by
  rw [unpackP_get]
  split
  · exact at'_big (n := 0) (by simp [canon1]) (Nat.zero_le _)
  · rfl

theorem compA_left0 (X : Array Nat) :
    compA n (#[] : Array Nat) X = compA n (unpackP n w 0) X := by
  unfold compA
  congr 1
  funext i
  rw [unpackP_zero_get]
  rfl

theorem compA_right0 (Y : Array Nat) :
    compA n Y (#[] : Array Nat) = compA n Y (unpackP n w 0) := by
  unfold compA
  congr 1
  funext i
  rw [unpackP_zero_get]
  rfl

theorem get_map_or {regs : Array Nat} (i : Nat) :
    (regs.map (unpackP n w))[i]! = unpackP n w regs[i]! ∨
      ((regs.map (unpackP n w))[i]! = #[] ∧ regs[i]! = 0) := by
  by_cases hi : i < regs.size
  · exact Or.inl (map_get _ _ hi)
  · right
    rw [getElem!_neg (regs.map (unpackP n w)) i (by simpa using hi), getElem!_neg regs i hi]
    exact ⟨rfl, rfl⟩

theorem compA_map {regs : Array Nat} (i j : Nat) :
    compA n (regs.map (unpackP n w))[i]! (regs.map (unpackP n w))[j]! =
      compA n (unpackP n w regs[i]!) (unpackP n w regs[j]!) := by
  rcases get_map_or (n := n) (w := w) (regs := regs) i with h1 | ⟨h1, h1'⟩ <;>
    rcases get_map_or (n := n) (w := w) (regs := regs) j with h2 | ⟨h2, h2'⟩
  · rw [h1, h2]
  · rw [h1, h2, h2', compA_right0]
  · rw [h1, h2, h1', compA_left0]
  · rw [h1, h2, h1', h2', compA_left0, compA_right0]

theorem canon_get' {regs : Array Nat} (h : ∀ x ∈ regs.toList, canon1 n w x = true) (i : Nat) :
    canon1 n w regs[i]! = true := by
  by_cases hi : i < regs.size
  · exact canon_get h i hi
  · rw [getElem!_neg regs i hi]
    simp [canon1]

theorem regs_fold (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) :
    ∀ (prog : List (Nat × Nat)) (regs : Array Nat), (∀ x ∈ regs.toList, canon1 n w x = true) →
      (prog.foldl (fun regs ij => regs.push (pc n w regs[ij.1]! regs[ij.2]!)) regs).map
          (unpackP n w) = prog.foldl (slpStep n) (regs.map (unpackP n w)) ∧
        ∀ x ∈ (prog.foldl (fun regs ij => regs.push (pc n w regs[ij.1]! regs[ij.2]!))
          regs).toList, canon1 n w x = true
  | [], regs, h => ⟨rfl, h⟩
  | ij :: prog, regs, h => by
    have h' : ∀ x ∈ (regs.push (pc n w regs[ij.1]! regs[ij.2]!)).toList, canon1 n w x = true := by
      intro x hx
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h x hx
      · exact canon1_pc hn hw
    obtain ⟨e, c⟩ := regs_fold hn hw prog _ h'
    refine ⟨?_, c⟩
    rw [List.foldl_cons, List.foldl_cons, e]
    congr 1
    rw [slpStep, Array.map_push, unpackP_pc hn hw (canon_get' h _), compA_map]

theorem regs_unpack (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) {gs : Array Nat}
    (hg : ∀ x ∈ gs.toList, canon1 n w x = true) (prog : List (Nat × Nat)) :
    (pslpRegs n w gs prog).map (unpackP n w) = slpRegs n (gs.map (unpackP n w)) prog ∧
      ∀ x ∈ (pslpRegs n w gs prog).toList, canon1 n w x = true := by
  have h0 : ∀ x ∈ (gs ++ gs.map (pinv n w)).toList, canon1 n w x = true := by
    intro x hx
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hg x hx
    · exact (unpackP_pinv hw (hg y hy)).2
  obtain ⟨e, c⟩ := regs_fold hn hw prog _ h0
  refine ⟨?_, c⟩
  unfold pslpRegs slpRegs
  rw [e, Array.map_append, Array.map_map, Array.map_map]
  congr 2
  exact Array.map_congr_left fun y hy => (unpackP_pinv hw (hg y (by simpa using hy))).1

theorem pslpIdx_spec : ∀ (k : Nat) (prog : List (Nat × Nat)), pslpIdxOK k prog = true →
    ∀ s < prog.length, (prog.getD s (0, 0)).1 < k + s ∧ (prog.getD s (0, 0)).2 < k + s
  | _, [], _, s, hs => absurd hs (by simp)
  | k, ij :: l, h, s, hs => by
    simp only [pslpIdxOK, Bool.and_eq_true, Nat.blt_eq] at h
    cases s with
    | zero => simpa using ⟨h.1.1, h.1.2⟩
    | succ s =>
      have := pslpIdx_spec (k + 1) l h.2 s (by simpa using hs)
      simp only [List.getD_cons_succ]
      omega

theorem extract_get {R : Array Nat} {m i : Nat} (hm : m ≤ R.size) (hi : i < m) :
    (R.extract 0 m)[i]! = R[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos R i (by omega), Array.getElem_extract]
  simp only [Nat.zero_add]

end CFSG.KC.Census.SP

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 CFSG.RankThree.Native

theorem pslpOK_eq_proved {n w : Nat} {gs : Array Nat} {prog : List (Nat × Nat)}
    (_hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hg : gs.toList.all (canon1 n w) = true) :
    pslpOK n w gs prog = slpOK n (gs.map (unpackP n w)) prog := by
  have hg' := SP.canon_get (List.all_eq_true.1 hg)
  unfold pslpOK slpOK
  rw [SP.pslpIdx_eq, Array.size_map]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, allLt_iff]
  refine forall_congr' fun k => ?_
  rw [List.mem_range]
  refine imp_congr_right fun hk => ?_
  rw [SP.map_get _ _ hk, SP.validA_unpack hw (hg' k hk)]

theorem pinXL_slpRegs_proved {n w P : Nat} {gs : Array Nat} {prog : List (Nat × Nat)}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hg : gs.toList.all (canon1 n w) = true)
    (_hv : gs.toList.all (pvalid n w) = true) (hP : canon1 n w P = true) :
    pinXL (pslpRegs n w gs prog) P =
      inRegsL n (slpRegs n (gs.map (unpackP n w)) prog) (unpackP n w P) := by
  obtain ⟨e, c⟩ := SP.regs_unpack hn hw (List.all_eq_true.1 hg) prog
  rw [← e]
  unfold pinXL inRegsL
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true, Array.size_map]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have hk' : k < (pslpRegs n w gs prog).size := by simpa using hk
    refine ⟨k, List.mem_range.2 hk', ?_⟩
    rw [SP.map_get _ _ hk', SP.eqA_unpack hP (SP.canon_get c k hk'), getElem!_pos _ k hk']
    simpa using h
  · rintro ⟨k, hk, h⟩
    have hk' := List.mem_range.1 hk
    rw [SP.map_get _ _ hk', SP.eqA_unpack hP (SP.canon_get c k hk')] at h
    refine ⟨(pslpRegs n w gs prog)[k]!, ?_, h⟩
    rw [getElem!_pos _ k hk']
    exact Array.getElem_mem_toList hk'

theorem pslpRegs_eq_of_steps_proved {n w : Nat} {gs R : Array Nat} {prog : List (Nat × Nat)}
    (hsz : R.size = 2 * gs.size + prog.length) (hg : ∀ k < gs.size, R[k]! = gs[k]!)
    (hi : ∀ k < gs.size, R[gs.size + k]! = pinv n w gs[k]!)
    (hidx : pslpIdxOK (2 * gs.size) prog = true)
    (hs : ∀ t < prog.length, R[2 * gs.size + t]! =
      pc n w R[(prog.getD t (0, 0)).1]! R[(prog.getD t (0, 0)).2]!) :
    pslpRegs n w gs prog = R := by
  have key : ∀ t ≤ prog.length,
      (prog.take t).foldl (fun regs ij => regs.push (pc n w regs[ij.1]! regs[ij.2]!))
        (gs ++ gs.map (pinv n w)) = R.extract 0 (2 * gs.size + t) := by
    intro t
    induction t with
    | zero =>
      intro _
      apply Array.ext
      · simp [hsz]
        omega
      · intro k h1 h2
        simp only [List.take_zero, List.foldl_nil, Array.size_append, Array.size_map] at h1 ⊢
        rw [Array.getElem_extract]
        simp only [Nat.zero_add]
        have hk : k < R.size := by omega
        rcases Nat.lt_or_ge k gs.size with hk' | hk'
        · rw [Array.getElem_append_left (by simpa using hk')]
          have := hg k hk'
          rw [getElem!_pos R k hk, getElem!_pos gs k hk'] at this
          exact this.symm
        · rw [Array.getElem_append_right (by simpa using hk'), Array.getElem_map]
          have hk2 : k - gs.size < gs.size := by omega
          have := hi (k - gs.size) hk2
          rw [getElem!_pos gs _ hk2] at this
          simp only [show gs.size + (k - gs.size) = k by omega] at this
          rw [getElem!_pos R k hk] at this
          exact this.symm
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.foldl_append, ih', List.foldl_cons, List.foldl_nil]
      have hid := SP.pslpIdx_spec _ prog hidx t (by omega)
      have hgt : prog.getD t (0, 0) = prog[t] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [hgt] at hid
      have hm : 2 * gs.size + t ≤ R.size := by omega
      rw [SP.extract_get hm hid.1, SP.extract_get hm hid.2]
      apply Array.ext
      · simp
        omega
      · intro k h1 h2
        simp only [Array.size_push, Array.size_extract] at h1
        rw [Array.getElem_extract]
        simp only [Nat.zero_add]
        rcases Nat.lt_or_ge k (2 * gs.size + t) with hk | hk
        · rw [Array.getElem_push_lt (by simp; omega), Array.getElem_extract]
          simp only [Nat.zero_add]
        · have hk' : k = 2 * gs.size + t := by omega
          subst hk'
          have := hs t (by omega)
          rw [hgt, getElem!_pos R _ (by omega)] at this
          rw [Array.getElem_push]
          split
          · next hlt =>
            simp only [Array.size_extract] at hlt
            omega
          · exact this.symm
  have := key prog.length (Nat.le_refl _)
  rw [List.take_length] at this
  unfold pslpRegs
  rw [this, ← hsz, Array.extract_size]

end CFSG.KC.Census

end
