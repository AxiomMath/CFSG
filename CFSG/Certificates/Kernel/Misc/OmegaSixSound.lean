module

public import Certificates.Data.Kernel.Misc.OmegaSixK
public import Certificates.Data.Foote82OmegaSixClass
public import CFSG.CGT.Foote82.T66.GLSixCodes
public import CFSG.Certificates.Kernel.Misc.YamakiRepSound
public import CFSG.Certificates.Kernel.Misc.YamakiRepFSound
public import CFSG.Certificates.Kernel.Misc.YamakiGenPosSound

public section

namespace CFSG.KC.OmegaSix

open Matrix CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux
  CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.OmegaSix CFSG.KD.YamakiRep
  CFSG.KD.YamakiRepF CFSG.KD.YamakiGenPos CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiRep
  CFSG.KC.YamakiRepF CFSG.KC.YamakiGenPos CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

theorem bit6_bijective : Function.Bijective bit6 := by decide

@[expose] noncomputable def bit6E : (Fin 2 ⊕ Fin 2 ⊕ Fin 2) ≃ Fin 6 :=
  Equiv.ofBijective bit6 bit6_bijective

@[expose] def matF (N : ℕ) : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits (pkMat 6 N)

@[expose] def arrF (N : ℕ) : Array ℕ := marr (matF N)

theorem ofBits_eq (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : ofBits M = M.submatrix bit6E bit6E :=
  rfl

theorem matF_mul (A B : ℕ) : matF (MULF A B) = matF A * matF B := by
  rw [matF, matF, matF, ofBits_eq, ofBits_eq, ofBits_eq, CFSG.KC.Sp62.pkMat_MULF,
    Matrix.submatrix_mul_equiv]

theorem arrF_mul (A B : ℕ) : compA (arrF A) (arrF B) = arrF (MULF A B) := by
  rw [arrF, arrF, arrF, matF_mul, marr_mul]

theorem arrF_one : arrF ONE = idA () := by
  rw [arrF, matF, CFSG.KC.YamakiS0.pkMat_ONE, ofBits_eq, Matrix.submatrix_one_equiv, marr_one]

theorem arrF_inj {A B : ℕ} (hA : A < 2 ^ 36) (hB : B < 2 ^ 36) (h : arrF A = arrF B) : A = B := by
  have hm := marr_injective h
  apply CFSG.KC.Sp62.pkMat_inj hA hB
  ext i j
  have := congrFun (congrFun hm (bit6E.symm i)) (bit6E.symm j)
  rw [matF, matF, ofBits_eq, ofBits_eq] at this
  simpa using this

theorem beq_arrF {A B : ℕ} (hA : A < 2 ^ 36) (hB : B < 2 ^ 36) :
    (arrF A == arrF B) = Nat.beq A B := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]
  exact ⟨arrF_inj hA hB, fun h => by rw [h]⟩

section Table

variable {R : ℕ → ℕ} {o n k : ℕ}

theorem table_invF {gs : Array (Array ℕ)} {g : ℕ} (hk : gs.size = k) (hk0 : 0 < k)
    (hk64 : k ≤ 64) (hn : 0 < n) (hg : ∀ j < k, gs[j]! = arrF (R (g + j)))
    (hh : headK R o n k = true) (hr : ∀ t < n, rowK R (rstG R g) o n k t = true) :
    BInvE (fun t => arrF (recX R o t)) (recF R o 0) (recF R o 1) n (bfsEnum gs n) ∧
      enumOK (bfsEnum gs n) gs = true ∧ ∀ t < n, recX R o t < 2 ^ 36 := by
  unfold headK at hh
  simp only [Bool.and_eq_true, Nat.beq_eq] at hh
  obtain ⟨⟨h0, hC0⟩, hCn⟩ := hh
  have hBi := build_of_rows hr
  have hSi := step_of_rows hk0 hk64 hr
  have hX := sort_of_rows hr
  have hlt := recX_lt h0 hBi
  have hk' : 0 < gs.size := by rw [hk]; exact hk0
  have hd : ∀ t < n, ∀ t' < n, arrF (recX R o t) = arrF (recX R o t') → t = t' :=
    fun t ht t' ht' e => hX t ht t' ht' (arrF_inj (hlt t ht) (hlt t' ht') e)
  have hT0 : arrF (recX R o 0) = idA () := by rw [h0, arrF_one]
  have hS' : ∀ i < n * gs.size, StepE gs (fun t => arrF (recX R o t))
      (recF R o 0) (recF R o 1) (recC R o k) (recPOS R o k) n i := by
    intro i hi
    rw [hk] at hi
    unfold StepE
    rw [hk]
    obtain ⟨a, b, c, d, e, f⟩ := stepAt_facts (hSi i hi)
    refine ⟨a, b, c, ?_, e, f⟩
    beta_reduce
    rw [d, rstG, Nat.add_eq, ← arrF_mul, hg _ (Nat.mod_lt _ hk0)]
  have hB' : ∀ i < n - 1, recF R o 0 i ≤ i ∧ recF R o 1 i < gs.size ∧
      arrF (recX R o (i + 1)) = compA (arrF (recX R o (recF R o 0 i))) gs[recF R o 1 i]! := by
    intro i hi
    obtain ⟨a, b, c⟩ := hBi i hi
    refine ⟨a, by rw [hk]; exact b, ?_⟩
    rw [c, rstG, Nat.add_eq, ← arrF_mul, hg _ b]
  have hCn' : recC R o k (n * gs.size) = n := by rw [hk]; exact hCn
  have r1 := bfsEnum_replay (fuel := n) (T := fun t => arrF (recX R o t)) (PA := recF R o 0)
    (PB := recF R o 1) (C := recC R o k) (POS := recPOS R o k) (n := n) hk' hn le_rfl hT0 hd hC0
    hCn' hS'
  have r2 := enumOK_of_replay (fuel := n) (T := fun t => arrF (recX R o t))
    (PA := recF R o 0) (PB := recF R o 1) (C := recC R o k) (POS := recPOS R o k) (n := n)
    hk' hn le_rfl hT0 hd hC0 hCn' hS' hB'
  exact ⟨r1, r2, hlt⟩

theorem clos_of_chunks {y e₁ e₂ L m : ℕ} (h : ∀ q < m, closChunk R o n y e₁ e₂ L q = true)
    (hm : n ≤ L * m) : ∀ t < n, closAt y e₁ e₂ (recX R o t) = true := by
  intro t ht
  have hL : 0 < L := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hm; omega
  have hq : t / L < m := (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm]; omega)
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 (h _ hq) t (Nat.mul_div_le t L) (by
    have := Nat.lt_div_mul_add (a := t) hL
    rw [Nat.mul_comm] at this
    exact this)
  have hb : Nat.blt t n = true := Nat.blt_eq.mpr ht
  rw [hb, strictY_eq] at e
  exact e

end Table

theorem powA_arrF (X : ℕ) : ∀ m, powA (arrF X) m = arrF (powF X m)
  | 0 => by rw [powA, ← arrF_one]; rfl
  | m + 1 => by rw [powA, powA_arrF X m, arrF_mul]; rfl

theorem powF_lt (X m : ℕ) : powF X (m + 1) < 2 ^ 36 := CFSG.KC.Sp62.MULF_lt _ _

theorem plK_succ (x y k u : ℕ) :
    plK x y (k + 1) u = bIf(invK y u, true, strictY (MULF u x) (plK x y k)) := rfl

theorem plK_iff (x y : ℕ) : ∀ k j : ℕ,
    plK x y k (powF x j) = true ↔ ∃ m < k, invK y (powF x (j + m)) = true
  | 0, j => by
    constructor
    · intro h
      exact absurd h Bool.false_ne_true
    · rintro ⟨m, hm, -⟩
      omega
  | k + 1, j => by
    rw [plK_succ, strictY_eq]
    have e : MULF (powF x j) x = powF x (j + 1) := rfl
    rw [e]
    cases h : invK y (powF x j)
    · change plK x y k (powF x (j + 1)) = true ↔ _
      rw [plK_iff x y k (j + 1)]
      constructor
      · rintro ⟨m, hm, hp⟩
        have e2 : j + 1 + m = j + (m + 1) := by omega
        rw [e2] at hp
        exact ⟨m + 1, by omega, hp⟩
      · rintro ⟨m, hm, hp⟩
        cases m with
        | zero =>
          rw [Nat.add_zero, h] at hp
          exact absurd hp Bool.false_ne_true
        | succ m =>
          have e2 : j + (m + 1) = j + 1 + m := by omega
          rw [e2] at hp
          exact ⟨m, by omega, hp⟩
    · change true = true ↔ _
      refine ⟨fun _ => ⟨0, by omega, ?_⟩, fun _ => rfl⟩
      rw [Nat.add_zero]
      exact h

theorem invA_eq {Y P : ℕ} (hY : Y < 2 ^ 36) (hP : P < 2 ^ 36) :
    (compA (arrF P) (arrF P) == idA () && !(arrF P == idA ()) && !(arrF P == arrF Y)) =
      invK Y P := by
  rw [arrF_mul, ← arrF_one, beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) CFSG.KC.YamakiS0.ONE_lt,
    beq_arrF hP CFSG.KC.YamakiS0.ONE_lt, beq_arrF hP hY]
  unfold invK
  cases Nat.beq (MULF P P) ONE <;> cases Nat.beq P ONE <;> cases Nat.beq P Y <;> rfl

theorem powInvol_arrF {X Y : ℕ} (hY : Y < 2 ^ 36) :
    powInvol (idA ()) (arrF Y) (arrF X) = powInvolK Y X := by
  have key : ∀ m, (compA (powA (arrF X) (m + 1)) (powA (arrF X) (m + 1)) == idA () &&
      !(powA (arrF X) (m + 1) == idA ()) && !(powA (arrF X) (m + 1) == arrF Y)) =
      invK Y (powF X (1 + m)) := by
    intro m
    rw [Nat.add_comm 1 m, powA_arrF]
    exact invA_eq hY (powF_lt X m)
  apply Bool.eq_iff_iff.2
  have e : MULF ONE X = powF X 1 := rfl
  rw [powInvolK, strictY_eq, e, plK_iff]
  simp only [powInvol, List.any_eq_true, List.mem_range]
  simp only [key]

theorem stepA_arrF (E X : ℕ) : stepA (arrF E) (arrF X) = arrF (stepK E X) := by
  simp only [stepA, powA_arrF, arrF_mul, stepK]

theorem good1_arrF {Y E₁ E₂ X : ℕ} (hY : Y < 2 ^ 36) :
    good1 (idA ()) (arrF Y) [arrF E₁, arrF E₂] (arrF X) = good1K Y E₁ E₂ X := by
  simp only [good1, List.any_cons, List.any_nil, stepA_arrF, powInvol_arrF hY, good1K,
    strictY_eq, Bool.or_false]
  generalize powInvolK Y X = a
  generalize powInvolK Y (stepK E₁ X) = b
  generalize powInvolK Y (stepK E₂ X) = c
  cases a <;> cases b <;> cases c <;> rfl

theorem good2_arrF {Y E₁ E₂ X : ℕ} (hY : Y < 2 ^ 36) :
    good2 (idA ()) (arrF Y) [arrF E₁, arrF E₂] (arrF X) = good2K Y E₁ E₂ X := by
  simp only [good2, List.any_cons, List.any_nil, stepA_arrF, good1_arrF hY, good2K,
    strictY_eq, Bool.or_false]
  generalize good1K Y E₁ E₂ X = a
  generalize good1K Y E₁ E₂ (stepK E₁ X) = b
  generalize good1K Y E₁ E₂ (stepK E₂ X) = c
  cases a <;> cases b <;> cases c <;> rfl

theorem closAt_arrF {Y E₁ E₂ X : ℕ} (hY : Y < 2 ^ 36) (hX : X < 2 ^ 36) :
    (!(commB (arrF X) (arrF Y)) || arrF X == idA () || arrF X == arrF Y ||
      good2 (idA ()) (arrF Y) [arrF E₁, arrF E₂] (arrF X)) = closAt Y E₁ E₂ X := by
  rw [good2_arrF hY, commB, arrF_mul, arrF_mul,
    beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _), ← arrF_one,
    beq_arrF hX CFSG.KC.YamakiS0.ONE_lt, beq_arrF hX hY, closAt]
  cases Nat.beq (MULF X Y) (MULF Y X) <;> cases Nat.beq X ONE <;> cases Nat.beq X Y <;>
    cases good2K Y E₁ E₂ X <;> rfl

theorem centInv_arrF {E : Enum} {Y e : ℕ} (hY : Y < 2 ^ 36) (he : e < 2 ^ 36)
    (hl : (E.lookup (arrF e)).isSome = true) (hc : centInvK Y e = true) :
    isCentInv E (arrF Y) (arrF e) = true := by
  unfold centInvK at hc
  revert hc
  rw [isCentInv, hl, commB, arrF_mul, arrF_mul, arrF_mul, ← arrF_one,
    beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _),
    beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) CFSG.KC.YamakiS0.ONE_lt]
  cases Nat.beq (MULF e Y) (MULF Y e) <;> cases Nat.beq (MULF e e) ONE <;> decide

@[expose] def closBody (E : Enum) (y e₁ e₂ : Array ℕ) : Bool :=
  [e₁, e₂].all (isCentInv E y) && E.elems.all fun z =>
    !(commB z y) || z == idA () || z == y || good2 (idA ()) y [e₁, e₂] z

theorem closureCheck_eq : closureCheck () =
    closBody (bfsEnum (genA6 ()) 25920) (marr rAMat) (marr e1Mat) (marr e2Mat) := rfl

theorem closBody_of {E : Enum} {X : ℕ → ℕ} {n Y E₁ E₂ : ℕ} (hsz : E.elems.size = n)
    (hel : ∀ t < n, E.elems[t]! = arrF (X t)) (hlt : ∀ t < n, X t < 2 ^ 36)
    (hY : Y < 2 ^ 36) (h₁ : E₁ < 2 ^ 36) (h₂ : E₂ < 2 ^ 36)
    (hl₁ : (E.lookup (arrF E₁)).isSome = true) (hl₂ : (E.lookup (arrF E₂)).isSome = true)
    (hc₁ : centInvK Y E₁ = true) (hc₂ : centInvK Y E₂ = true)
    (hall : ∀ t < n, closAt Y E₁ E₂ (X t) = true) :
    closBody E (arrF Y) (arrF E₁) (arrF E₂) = true := by
  rw [closBody, Bool.and_eq_true, List.all_cons, List.all_cons, List.all_nil,
    centInv_arrF hY h₁ hl₁ hc₁, centInv_arrF hY h₂ hl₂ hc₂, Array.all_eq_true]
  refine ⟨rfl, fun i hi => ?_⟩
  have hi' : i < n := by omega
  rw [← getElem!_pos E.elems i hi, hel i hi', closAt_arrF hY (hlt i hi')]
  exact hall i hi'

theorem closureCheck_of {R : ℕ → ℕ} {p₁ p₂ : ℕ} (hA : aMat = matF (R 0))
    (hB : bMat = matF (R 1)) (hrA : rAMat = matF (R 3)) (he₁ : e1Mat = matF (R 8))
    (he₂ : e2Mat = matF (R 9)) (hlt : ∀ j < 10, R j < 2 ^ 36)
    (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (hcl : ∀ q < 51, closChunk R 10 25920 (R 3) (R 8) (R 9) 512 q = true)
    (hc₁ : centInvK (R 3) (R 8) = true) (hc₂ : centInvK (R 3) (R 9) = true)
    (hp : genPosK R 10 25920 [8, 9] [p₁, p₂] = true) :
    closureCheck () = true := by
  have hg : ∀ j < 2, (genA6 ())[j]! = arrF (R (0 + j)) := by
    intro j hj
    rcases j with _ | _ | j
    · rw [Nat.add_zero, arrF, ← hA]
      rfl
    · rw [Nat.zero_add, arrF, ← hB]
      rfl
    · omega
  have T := table_invF (gs := genA6 ()) (R := R) (o := 10) (n := 25920) (k := 2) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num) hg hh
    (rows_of_chunks (L := 512) (m := 51) (fun q hq => chunkK_of_chunkF (hc q hq)) (by norm_num))
  have look : ∀ i ∈ [8, 9], (Enum.lookup (bfsEnum (genA6 ()) 25920) (arrF (R i))).isSome =
      true := by
    intro i hi
    obtain ⟨p, hp', hpe⟩ := genPosK_sound hp i hi
    have h := lookup_of_inv (T := fun t => arrF (recX R 10 t)) T.1 hp'
    beta_reduce at h
    rw [hpe] at h
    rw [h]
    rfl
  have mA : marr rAMat = arrF (R 3) := by rw [hrA]; rfl
  have m₁ : marr e1Mat = arrF (R 8) := by rw [he₁]; rfl
  have m₂ : marr e2Mat = arrF (R 9) := by rw [he₂]; rfl
  rw [closureCheck_eq, mA, m₁, m₂]
  exact closBody_of (X := recX R 10) (n := 25920) T.1.1 T.1.2.2.2.1 T.2.2 (hlt 3 (by norm_num))
    (hlt 8 (by norm_num)) (hlt 9 (by norm_num)) (look 8 (by simp)) (look 9 (by simp)) hc₁ hc₂
    (clos_of_chunks (L := 512) (m := 51) hcl (by norm_num))

end CFSG.KC.OmegaSix

end
