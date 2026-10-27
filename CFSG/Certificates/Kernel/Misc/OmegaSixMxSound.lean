module

public import Certificates.Data.Kernel.Misc.OmegaSixMx
public import Certificates.Data.Foote82OmegaSixMax
public import CFSG.Certificates.Kernel.Misc.OmegaSixOSound

public section

namespace CFSG.KC.OmegaSix

open Matrix CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux
  CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.OmegaSix CFSG.KD.YamakiRep
  CFSG.KD.YamakiRepF CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiRep CFSG.KC.YamakiRepF
open CFSG.KD.Sp62 (MULF)

theorem rank1_false_of_twoNZ {t : Array ℕ} (h : twoNZ t = true) : rank1 t = false := by
  rw [Bool.eq_false_iff]
  intro h1
  simp only [twoNZ, subOneCode, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  simp only [rank1, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at h1
  obtain ⟨i, hi, hi0, j, hj, hj0, hij⟩ := h
  obtain ⟨c, -, -, hall⟩ := h1
  rcases hall i hi with e | e
  · exact hi0 e
  · rcases hall j hj with e' | e'
    · exact hj0 e'
    · exact hij (e'.trans e.symm)

theorem rank1_idA : rank1 (idA ()) = false := by
  rw [Bool.eq_false_iff]
  intro h1
  simp only [rank1, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h1
  obtain ⟨c, -, ⟨hc0, k, hk, hkc⟩, -⟩ := h1
  have e : (idA ())[k]! = k := by
    rw [idA, getElem!_pos _ k (by simp; omega)]
    simp
  rw [e, Nat.xor_self] at hkc
  exact hc0 hkc.symm

@[expose] def cosetF (EC : Enum) (R S1 S2 y : Array ℕ) : Bool :=
  compA y R == compA R y ||
    EC.elems.any fun c => compA (compA c y) R == compA S1 (compA c y) ||
      compA (compA c y) R == compA S2 (compA c y)

theorem cosetAt_arrF {RC : ℕ → ℕ} {nC r s₁ s₂ w X : ℕ} {EC : Enum}
    (hE : BInvE (fun t => arrF (recX RC 2 t)) (recF RC 2 0) (recF RC 2 1) nC EC)
    (h : cosetAt RC 2 nC r s₁ s₂ w X = true) :
    cosetF EC (arrF r) (arrF s₁) (arrF s₂) (arrF X) = true := by
  unfold cosetF
  rw [arrF_mul, arrF_mul, beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]
  unfold cosetAt at h
  cases h1 : Nat.beq (MULF X r) (MULF r X)
  · rw [h1] at h
    change bAnd(Nat.blt w nC, strictY (MULF (recX RC 2 w) X) fun cy => strictY (MULF cy r)
      fun u => bIf(Nat.beq u (MULF s₁ cy), true, Nat.beq u (MULF s₂ cy))) = true at h
    cases h2 : Nat.blt w nC
    · rw [h2] at h
      exact absurd h Bool.false_ne_true
    · rw [h2] at h
      change strictY (MULF (recX RC 2 w) X) (fun cy => strictY (MULF cy r)
        fun u => bIf(Nat.beq u (MULF s₁ cy), true, Nat.beq u (MULF s₂ cy))) = true at h
      rw [strictY_eq, strictY_eq] at h
      have hw := Nat.blt_eq.mp h2
      rw [Bool.false_or, Array.any_eq_true]
      refine ⟨w, by rw [hE.1]; exact hw, ?_⟩
      rw [← getElem!_pos EC.elems w (by rw [hE.1]; exact hw), hE.2.2.2.1 w hw]
      beta_reduce
      rw [arrF_mul, arrF_mul, arrF_mul, arrF_mul,
        beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _),
        beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]
      cases h3 : Nat.beq (MULF (MULF (recX RC 2 w) X) r) (MULF s₁ (MULF (recX RC 2 w) X))
      · rw [h3] at h
        change Nat.beq (MULF (MULF (recX RC 2 w) X) r) (MULF s₂ (MULF (recX RC 2 w) X)) =
          true at h
        rw [h]
        rfl
      · rfl
  · rfl

@[expose] def cosetBody (E EC : Enum) (R S1 S2 : Array ℕ) : Bool :=
  E.elems.all fun y => cosetF EC R S1 S2 y

theorem maxCosetCheck_eq : maxCosetCheck () =
    cosetBody (bfsEnum (genA6 ()) 25920) (bfsEnum (genCr ()) 720) (marr rMat)
      (marr (dc1Mat * rMat * dc1Mat)) (marr (dc2Mat * rMat * dc2Mat)) := rfl

@[expose] def maxReflBody (E ER : Enum) (x : Array ℕ) : Bool :=
  conjTreeOK ER (genA6 ()) (CFSG.CGT.Foote82.CaseIIClassAux.genA6Inv ()) x &&
    E.elems.all fun t => !(rank1 t) || (ER.lookup t).isSome

theorem maxReflCheck_eq : maxReflCheck () =
    maxReflBody (bfsEnum (genO ()) 51840)
      (conjEnum (genA6 ()) (CFSG.CGT.Foote82.CaseIIClassAux.genA6Inv ()) (marr rMat) 40) (marr rMat) := rfl

section Checks

variable {R C H S : ℕ → ℕ}

theorem cr_inv (h₁ : cr1Mat = matF (C 0)) (h₂ : cr2Mat = matF (C 1))
    (hh : headK C 2 720 2 = true) (hc : ∀ q < 3, chunkF C (rstG C 0) 2 720 256 q = true) :
    BInvE (fun t => arrF (recX C 2 t)) (recF C 2 0) (recF C 2 1) 720 (bfsEnum (genCr ()) 720) ∧
      enumOK (bfsEnum (genCr ()) 720) (genCr ()) = true := by
  have hg : ∀ j < 2, (genCr ())[j]! = arrF (C (0 + j)) := by
    intro j hj
    rcases j with _ | _ | j
    · rw [Nat.add_zero, arrF, ← h₁]
      rfl
    · rw [Nat.zero_add, arrF, ← h₂]
      rfl
    · omega
  have T := table_invF (gs := genCr ()) (R := C) (o := 2) (n := 720) (k := 2) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num) hg hh
    (rows_of_chunks (L := 256) (m := 3) (fun q hq => chunkK_of_chunkF (hc q hq)) (by norm_num))
  exact ⟨T.1, T.2.1⟩

theorem crEnumCheck_of (h₁ : cr1Mat = matF (C 0)) (h₂ : cr2Mat = matF (C 1))
    (hh : headK C 2 720 2 = true) (hc : ∀ q < 3, chunkF C (rstG C 0) 2 720 256 q = true) :
    crEnumCheck () = true := by
  have T := (cr_inv h₁ h₂ hh hc).2
  rw [enumOK, Bool.and_eq_true, Bool.and_eq_true] at T
  exact T.1.1

theorem maxGenCheck_of {gs : Array (Array ℕ)} {L m : ℕ} (hgs : gs.size = 3)
    (hg : ∀ j < 3, gs[j]! = arrF (S (0 + j))) (hm : 25920 ≤ L * m)
    (hh : headK S 3 25920 3 = true) (hc : ∀ q < m, chunkF3 S (rstG S 0) 3 25920 L q = true) :
    (enumOK (bfsEnum gs 25920) gs && (bfsEnum gs 25920).elems.size == 25920) = true := by
  have T := table_invF (gs := gs) (R := S) (o := 3) (n := 25920) (k := 3) (g := 0) hgs
    (by norm_num) (by norm_num) (by norm_num) hg hh
    (rows_of_chunks (L := L) (m := m) (fun q hq => chunkK_of_chunkF3 (hc q hq)) hm)
  rw [T.2.1, T.1.1]
  rfl

theorem maxMemCheck_of {x₀ x₁ x₂ x₃ p₀ p₁ p₂ p₃ : ℕ} (hA : aMat = matF (R 0))
    (hB : bMat = matF (R 1)) (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (h₀ : cr1Mat = matF x₀) (h₁ : cr2Mat = matF x₁) (h₂ : dc1Mat = matF x₂)
    (h₃ : dc2Mat = matF x₃)
    (hp₀ : posAt R 10 25920 p₀ x₀ = true) (hp₁ : posAt R 10 25920 p₁ x₁ = true)
    (hp₂ : posAt R 10 25920 p₂ x₂ = true) (hp₃ : posAt R 10 25920 p₃ x₃ = true) :
    maxMemCheck () = true := by
  have T := omega_inv hA hB hh hc
  have look : ∀ {M : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)} {x p : ℕ},
      M = matF x → posAt R 10 25920 p x = true →
        ((bfsEnum (genA6 ()) 25920).lookup (marr M)).isSome = true := by
    intro M x p hM hp
    unfold posAt at hp
    cases h1 : Nat.blt p 25920
    · rw [h1] at hp
      exact absurd hp Bool.false_ne_true
    · rw [h1] at hp
      change Nat.beq (recX R 10 p) x = true at hp
      have e : marr M = arrF (recX R 10 p) := by rw [Nat.beq_eq.mp hp, hM]; rfl
      rw [e, lookup_of_inv (T := fun t => arrF (recX R 10 t)) T.1 (Nat.blt_eq.mp h1)]
      rfl
  change ((bfsEnum (genA6 ()) 25920).lookup (marr cr1Mat)).isSome &&
    ((bfsEnum (genA6 ()) 25920).lookup (marr cr2Mat)).isSome &&
    ((bfsEnum (genA6 ()) 25920).lookup (marr dc1Mat)).isSome &&
    ((bfsEnum (genA6 ()) 25920).lookup (marr dc2Mat)).isSome = true
  rw [look h₀ hp₀, look h₁ hp₁, look h₂ hp₂, look h₃ hp₃]
  rfl

theorem maxCosetCheck_of {W : ℕ → ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hr : rMat = matF (R 2)) (h₁ : cr1Mat = matF (C 0)) (h₂ : cr2Mat = matF (C 1))
    (hd₁ : dc1Mat = matF (H 0)) (hd₂ : dc2Mat = matF (H 1))
    (hs₁ : H 2 = MULF (MULF (H 0) (R 2)) (H 0)) (hs₂ : H 3 = MULF (MULF (H 1) (R 2)) (H 1))
    (hh : headK R 10 25920 2 = true) (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (hhC : headK C 2 720 2 = true) (hcC : ∀ q < 3, chunkF C (rstG C 0) 2 720 256 q = true)
    (hcl : ∀ q < 102, cosetChunk R 10 25920 C 2 720 W (R 2) (H 2) (H 3) 256 q = true) :
    maxCosetCheck () = true := by
  have T := omega_inv hA hB hh hc
  have TC := (cr_inv h₁ h₂ hhC hcC).1
  have mr : marr rMat = arrF (R 2) := by rw [hr]; rfl
  have m₁ : marr (dc1Mat * rMat * dc1Mat) = arrF (H 2) := by
    rw [hd₁, hr, ← matF_mul, ← matF_mul, ← hs₁]
    rfl
  have m₂ : marr (dc2Mat * rMat * dc2Mat) = arrF (H 3) := by
    rw [hd₂, hr, ← matF_mul, ← matF_mul, ← hs₂]
    rfl
  rw [maxCosetCheck_eq, mr, m₁, m₂, cosetBody, Array.all_eq_true]
  intro i hi
  have hsz := T.1.1
  have hi' : i < 25920 := by omega
  rw [← getElem!_pos _ i hi, T.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks 256 102 _ hcl i (by omega)
  change bIf(Nat.blt i 25920, strictY (recX R 10 i) (cosetAt C 2 720 (R 2) (H 2) (H 3) (W i)),
    true) = true at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  exact cosetAt_arrF TC hall

theorem maxReflCheck_of {L m L' m' : ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hr : rMat = matF (R 2)) (hr2 : R 2 < 2 ^ 36) (hS4 : S 4 = R 2) (hm : 51840 ≤ L * m)
    (hh : headK R 3 51840 3 = true) (hc : ∀ q < m, chunkF3 R (rstG R 0) 3 51840 L q = true)
    (hd : hdrC S (R 0) (R 1) (S 4) = true) (hhS : headC S 5 36 = true)
    (hcS : ∀ q < 2, chunkF S (cjG S) 5 36 32 q = true) (hm' : 51840 ≤ L' * m')
    (hcl : ∀ q < m', reflChunk R 3 51840 S 36 L' q = true) :
    maxReflCheck () = true := by
  have T := oEnum_inv hA hB hr hm hh hc
  have O := orbitO (S := S) (fuel := 40) hA hB (by norm_num) (by norm_num) (by norm_num)
    (by rw [hS4]; exact hr2) hd hhS hcS
  have mr : marr rMat = arrF (S 4) := by rw [hS4, hr]; rfl
  rw [maxReflCheck_eq, mr, maxReflBody, O.2.1, Bool.true_and, Array.all_eq_true]
  intro i hi
  have hsz := T.1.1
  have hi' : i < 51840 := by omega
  rw [← getElem!_pos _ i hi, T.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks L' m' _ hcl i (by omega)
  change bIf(Nat.blt i 51840, strictY (recX R 3 i) (reflAt S 36), true) = true at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  have e := reflAt_arrF (T.2 i hi') O.1 O.2.2.2 hall
  cases hl : ((conjEnum (genA6 ()) (CFSG.CGT.Foote82.CaseIIClassAux.genA6Inv ()) (arrF (S 4)) 40).lookup
      (arrF (recX R 3 i))).isSome
  · rw [hl, Bool.false_or] at e
    beta_reduce
    rw [Bool.or_false, Bool.not_eq_true']
    cases hi1 : (arrF (recX R 3 i) == idA ())
    · rw [hi1, Bool.false_or] at e
      exact rank1_false_of_twoNZ e
    · rw [beq_iff_eq.mp hi1]
      exact rank1_idA
  · rw [Bool.or_true]

end Checks

end CFSG.KC.OmegaSix

end
