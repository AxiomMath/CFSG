module

public import Certificates.Data.Kernel.Misc.OmegaSixF
public import Certificates.Data.Foote82OmegaSixAut
public import CFSG.Certificates.Kernel.Misc.OmegaSixASound

public section

namespace CFSG.KC.OmegaSix

open Matrix CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux
  CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.OmegaSix CFSG.KD.YamakiRep
  CFSG.KD.YamakiRepF CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.ConjEnum CFSG.KC.YamakiRep
  CFSG.KC.YamakiRepF CFSG.KC.Loop CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

theorem pow5_eq (X : ℕ) :
    compA (arrF X) (compA (arrF X) (compA (arrF X) (compA (arrF X) (arrF X)))) =
      arrF (MULF (MULF (MULF X X) (MULF X X)) X) := by
  rw [arrF_mul, arrF_mul, arrF_mul, arrF_mul]
  have e : MULF X (MULF X (MULF X (MULF X X))) = MULF (MULF (MULF X X) (MULF X X)) X :=
    eqF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _) (by
      simp only [matF_mul, mul_assoc])
  rw [e]

theorem fiveAt_arrF {S : ℕ → ℕ} {nS X : ℕ} {E : Enum} (hX : X < 2 ^ 36)
    (hE : BInvE (fun t => arrF (recX S 5 t)) (recF S 5 0) (recF S 5 1) nS E)
    (hs : ∀ m < nS, recF S 5 2 m < nS) (h : fiveAt S nS X = true) :
    (arrF X == idA () ||
      !(compA (arrF X) (compA (arrF X) (compA (arrF X) (compA (arrF X) (arrF X)))) == idA ()) ||
      (E.lookup (arrF X)).isSome) = true := by
  rw [pow5_eq, ← arrF_one, beq_arrF hX CFSG.KC.YamakiS0.ONE_lt,
    beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) CFSG.KC.YamakiS0.ONE_lt]
  unfold fiveAt at h
  rw [strictY_eq] at h
  cases h1 : Nat.beq X ONE
  · rw [h1] at h
    change bIf(Nat.beq (MULF (MULF (MULF X X) (MULF X X)) X) ONE, memK S 5 nS X, true) = true at h
    cases h2 : Nat.beq (MULF (MULF (MULF X X) (MULF X X)) X) ONE
    · simp
    · rw [h2] at h
      change memK S 5 nS X = true at h
      rw [isSome_of_memK hE hs h]
      simp
  · simp

@[expose] def fiveBody (E E5 : Enum) (xb : Array ℕ) : Bool :=
  conjTreeOK E5 (genO ()) (genOInv ()) xb &&
    E.elems.all fun x => x == idA () || !(compA x (compA x (compA x (compA x x))) == idA ()) ||
      (E5.lookup x).isSome

theorem fiveCheck_eq : fiveCheck () =
    fiveBody (bfsEnum (genA6 ()) 25920) (conjEnum (genO ()) (genOInv ()) (marr bMat) 5184)
      (marr bMat) := rfl

theorem wordK_lt (X Y : ℕ) (w : List ℕ) : wordK X Y w < 2 ^ 36 := by
  cases w with
  | nil => exact CFSG.KC.YamakiS0.ONE_lt
  | cons i w => exact CFSG.KC.Sp62.MULF_lt _ _

theorem wordA_arrF2 (X Y : ℕ) : ∀ w : List ℕ, (∀ i ∈ w, i < 2) →
    wordA #[arrF X, arrF Y] w = arrF (wordK X Y w)
  | [], _ => by
    rw [wordA, ← arrF_one]
    rfl
  | i :: w, h => by
    have ih := wordA_arrF2 X Y w (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have hi : i < 2 := h i List.mem_cons_self
    have e : (#[arrF X, arrF Y] : Array (Array ℕ))[i]! = arrF (nIf(Nat.beq i 0, X, Y)) := by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
    rw [wordA, ih, e, arrF_mul]
    rfl

theorem relsK_eq (X Y : ℕ) : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ i ∈ w, i < 2) →
    (ws.all fun w => wordA #[arrF X, arrF Y] w == idA ()) = relsK ws X Y
  | [], _ => rfl
  | w :: ws, h => by
    rw [List.all_cons, relsK_eq X Y ws (fun v hv => h v (List.mem_cons_of_mem _ hv)),
      wordA_arrF2 X Y w (h w List.mem_cons_self), ← arrF_one,
      beq_arrF (wordK_lt X Y w) CFSG.KC.YamakiS0.ONE_lt]
    change _ = bIf(Nat.beq (wordK X Y w) ONE, relsK ws X Y, false)
    cases Nat.beq (wordK X Y w) ONE <;> rfl

theorem relators_lt : ∀ w ∈ relators, ∀ i ∈ w, i < 2 := by decide

theorem inPW_sound {P : ℕ → ℕ} {nP x : ℕ} (h : inPW P nP x = true) :
    ∃ m < nP, Nat.land (Nat.shiftRight (P m) 0) 68719476735 = x := by
  unfold inPW at h
  by_contra hn
  push Not at hn
  have hall : CFSG.KC.Misc.Clos.allR 0 nP (fun m =>
      bIf(Nat.beq (Nat.land (Nat.shiftRight (P m) 0) 68719476735) x, false, true)) = true := by
    rw [CFSG.KC.Misc.Clos.allR_iff]
    intro m _ hm
    have hne := hn m (by omega)
    cases hb : Nat.beq (Nat.land (Nat.shiftRight (P m) 0) 68719476735) x
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne
  rw [hall] at h
  exact absurd h (by decide)

theorem pwAt_sound {G P : ℕ → ℕ} {o n a y m : ℕ} (h : pwAt G o n a y P m = true) :
    Nat.land (Nat.shiftRight (P m) 36) 65535 < n ∧
      MULF (recX G o (Nat.land (Nat.shiftRight (P m) 36) 65535)) y =
        MULF y (recX G o (Nat.land (Nat.shiftRight (P m) 36) 65535)) ∧
      MULF (recX G o (Nat.land (Nat.shiftRight (P m) 36) 65535)) a =
        MULF (Nat.land (Nat.shiftRight (P m) 0) 68719476735)
          (recX G o (Nat.land (Nat.shiftRight (P m) 36) 65535)) := by
  unfold pwAt at h
  simp only [strictY_eq, bAnd_iffO, Nat.blt_eq, Nat.beq_eq] at h
  exact h

@[expose] def pairBody (E EO : Enum) (xa xb : Array ℕ) : Bool :=
  E.elems.all fun x => x == idA () || !(relators.all fun w => wordA #[x, xb] w == idA ()) ||
    (EO.elems.filter fun o => compA o xb == compA xb o).any fun o => compA o xa == compA x o

theorem pairCheck_eq : pairCheck () =
    pairBody (bfsEnum (genA6 ()) 25920) (bfsEnum (genO ()) 51840) (marr aMat) (marr bMat) := rfl

section Checks

variable {R G : ℕ → ℕ}

theorem fiveCheck_of {S : ℕ → ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hlt : ∀ j < 10, R j < 2 ^ 36) (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (hA' : aMat = matF (G 0)) (hB' : bMat = matF (G 1)) (hr' : rMat = matF (G 2))
    (hd : hdrO S (G 0) (G 1) (G 2) (R 1) = true) (hhS : headC3 S 5 5184 = true)
    (hcS : ∀ q < 11, chunkF3 S (cjO G S) 5 5184 512 q = true)
    (hf : ∀ q < 51, fiveChunk R 10 25920 S 5184 512 q = true) : fiveCheck () = true := by
  have T := omega_inv hA hB hh hc
  have O5 := orbitO3 (S := S) (L := 512) (m := 11) (fuel := 5184) hA' hB' hr' (by norm_num)
    (by norm_num) (by norm_num) (hlt 1 (by norm_num)) hd hhS hcS
  have mB : marr bMat = arrF (R 1) := by rw [hB]; rfl
  rw [fiveCheck_eq, mB, fiveBody, O5.2.1, Bool.true_and, Array.all_eq_true]
  intro i hi
  have hsz := T.1.1
  have hi' : i < 25920 := by omega
  rw [← getElem!_pos _ i hi, T.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks 512 51 _ hf i (by omega)
  change bIf(Nat.blt i 25920, strictY (recX R 10 i) (fiveAt S 5184), true) = true at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  exact fiveAt_arrF (T.2 i hi') O5.1 O5.2.2.2 hall

theorem pairCheck_of {P : ℕ → ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (hA' : aMat = matF (G 0)) (hB' : bMat = matF (G 1)) (hr' : rMat = matF (G 2))
    (hhO : headK G 3 51840 3 = true)
    (hcO : ∀ q < 203, chunkF3 G (rstG G 0) 3 51840 256 q = true)
    (hpw : pwOK G 3 51840 (R 0) (R 1) P 10 = true)
    (hp : ∀ q < 51, pairChunk R 10 25920 relators (R 1) P 10 512 q = true) :
    pairCheck () = true := by
  have T := omega_inv hA hB hh hc
  have TO := oEnum_inv (L := 256) (m := 203) hA' hB' hr' (by norm_num) hhO hcO
  have mA : marr aMat = arrF (R 0) := by rw [hA]; rfl
  have mB : marr bMat = arrF (R 1) := by rw [hB]; rfl
  rw [pairCheck_eq, pairBody, mA, mB, Array.all_eq_true]
  intro i hi
  have hsz := T.1.1
  have hi' : i < 25920 := by omega
  rw [← getElem!_pos _ i hi, T.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks 512 51 _ hp i (by omega)
  change bIf(Nat.blt i 25920, strictY (recX R 10 i) (pairAt relators (R 1) P 10), true) = true
    at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  have hX := T.2 i hi'
  beta_reduce
  rw [relsK_eq _ _ _ relators_lt, ← arrF_one, beq_arrF hX CFSG.KC.YamakiS0.ONE_lt]
  unfold pairAt at hall
  cases h1 : Nat.beq (recX R 10 i) ONE
  · rw [h1] at hall
    change bIf(relsK relators (recX R 10 i) (R 1), inPW P 10 (recX R 10 i), true) = true at hall
    cases h2 : relsK relators (recX R 10 i) (R 1)
    · simp
    · rw [h2] at hall
      change inPW P 10 (recX R 10 i) = true at hall
      obtain ⟨m, hm, hmx⟩ := inPW_sound hall
      have hw := (CFSG.KC.Misc.Clos.allR_iff _ _ _).mp hpw m (Nat.zero_le _) (by omega)
      obtain ⟨hj, hc1, hc2⟩ := pwAt_sound hw
      rw [hmx] at hc2
      set j := Nat.land (Nat.shiftRight (P m) 36) 65535 with hjdef
      have hjs : j < (bfsEnum (genO ()) 51840).elems.size := by rw [TO.1.1]; exact hj
      have ho : (bfsEnum (genO ()) 51840).elems[j] = arrF (recX G 3 j) := by
        rw [← getElem!_pos _ j hjs]
        exact TO.1.2.2.2.1 j hj
      have hTl := TO.2 j hj
      simp only [Bool.false_or, Bool.not_true]
      rw [Array.any_eq_true']
      refine ⟨arrF (recX G 3 j), ?_, ?_⟩
      · rw [Array.mem_filter]
        refine ⟨by rw [← ho]; exact Array.getElem_mem hjs, ?_⟩
        rw [arrF_mul, arrF_mul, beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _), hc1]
        exact Nat.beq_refl _
      · rw [arrF_mul, arrF_mul, beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _), hc2]
        exact Nat.beq_refl _
  · simp

end Checks

end CFSG.KC.OmegaSix

end
