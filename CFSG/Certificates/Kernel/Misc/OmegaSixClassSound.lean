module

public import Certificates.Data.Kernel.Misc.OmegaSixC
public import CFSG.Certificates.Kernel.Misc.OmegaSixSound
public import CFSG.Certificates.Kernel.Misc.ConjEnumSound

public section

namespace CFSG.KC.OmegaSix

open Matrix CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux
  CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.OmegaSix CFSG.KD.YamakiRep
  CFSG.KD.YamakiRepF CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.ConjEnum CFSG.KC.YamakiRep
  CFSG.KC.YamakiRepF CFSG.KC.Loop
open CFSG.KD.Sp62 (MULF ONE)

theorem strictN_eqO (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem nIf_eqO (c : Bool) (t e : ℕ) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_iffO (a b : Bool) : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

section Orbit

variable {R : ℕ → ℕ} {n : ℕ}

theorem srt_of_rows {st : ℕ → ℕ → ℕ} {o k : ℕ} (h : ∀ t < n, rowK R st o n k t = true) :
    ∀ m < n, recF R o 2 m < n := by
  intro m hm
  have e := h m hm
  unfold rowK sortAt at e
  simp only [Bool.and_eq_true, Nat.blt_eq] at e
  exact e.2.1.1.1.1

theorem cjG_arrF {gs gsInv : Array (Array ℕ)} (hg : ∀ j < 2, gs[j]! = arrF (R j))
    (hgi : ∀ j < 2, gsInv[j]! = arrF (R (2 + j))) {s : ℕ} (hs : s < 2) (X : ℕ) :
    arrF (cjG R X s) = cj gs gsInv (arrF X) s := by
  rw [cjG, cj, hg s hs, hgi s hs, arrF_mul, arrF_mul, Nat.add_eq]

theorem orbit_inv {gs gsInv : Array (Array ℕ)} {x : Array ℕ} {fuel : ℕ} (hk : gs.size = 2)
    (hn : 0 < n) (hfuel : n ≤ fuel) (hg : ∀ j < 2, gs[j]! = arrF (R j))
    (hgi : ∀ j < 2, gsInv[j]! = arrF (R (2 + j))) (hx : x = arrF (R 4)) (h4 : R 4 < 2 ^ 36)
    (hh : headC R 5 n = true) (hr : ∀ t < n, rowK R (cjG R) 5 n 2 t = true) :
    BInvE (fun t => arrF (recX R 5 t)) (recF R 5 0) (recF R 5 1) n
        (conjEnum gs gsInv x fuel) ∧
      conjTreeOK (conjEnum gs gsInv x fuel) gs gsInv x = true ∧
      (∀ t < n, recX R 5 t < 2 ^ 36) ∧ ∀ m < n, recF R 5 2 m < n := by
  unfold headC at hh
  simp only [bAnd_iffO, Nat.beq_eq] at hh
  obtain ⟨h0, hC0, hCn⟩ := hh
  have hBi := build_of_rows hr
  have hSi := step_of_rows (by norm_num) (by norm_num) hr
  have hX := sort_of_rows hr
  have hlt : ∀ t < n, recX R 5 t < 2 ^ 36 := by
    intro t ht
    cases t with
    | zero => rw [h0]; exact h4
    | succ t =>
      rw [(hBi t (by omega)).2.2]
      exact CFSG.KC.Sp62.MULF_lt _ _
  have hk' : 0 < gs.size := by rw [hk]; norm_num
  have hd : ∀ t < n, ∀ t' < n, arrF (recX R 5 t) = arrF (recX R 5 t') → t = t' :=
    fun t ht t' ht' e => hX t ht t' ht' (arrF_inj (hlt t ht) (hlt t' ht') e)
  have hT0 : arrF (recX R 5 0) = x := by rw [h0, hx]
  have hS' : ∀ i < n * gs.size, StepC gs gsInv (fun t => arrF (recX R 5 t))
      (recF R 5 0) (recF R 5 1) (recC R 5 2) (recPOS R 5 2) n i := by
    intro i hi
    rw [hk] at hi
    unfold StepC
    rw [hk]
    obtain ⟨a, b, c, d, e, f⟩ := stepAt_facts (hSi i hi)
    refine ⟨a, b, c, ?_, e, f⟩
    beta_reduce
    rw [d, cjG_arrF hg hgi (Nat.mod_lt _ (by norm_num))]
  have hB' : ∀ i < n - 1, recF R 5 0 i ≤ i ∧ recF R 5 1 i < gs.size ∧
      arrF (recX R 5 (i + 1)) = cj gs gsInv (arrF (recX R 5 (recF R 5 0 i))) (recF R 5 1 i) := by
    intro i hi
    obtain ⟨a, b, c⟩ := hBi i hi
    refine ⟨a, by rw [hk]; exact b, ?_⟩
    rw [c, cjG_arrF hg hgi b]
  have hCn' : recC R 5 2 (n * gs.size) = n := by rw [hk]; exact hCn
  have r1 := conjEnum_replay (gs := gs) (gsInv := gsInv) (fuel := fuel)
    (T := fun t => arrF (recX R 5 t)) (PA := recF R 5 0) (PB := recF R 5 1) (C := recC R 5 2)
    (POS := recPOS R 5 2) (n := n) hk' hn hfuel hT0 hd hC0 hCn' hS'
  have r2 := conjTreeOK_of_replay (gs := gs) (gsInv := gsInv) (fuel := fuel)
    (T := fun t => arrF (recX R 5 t)) (PA := recF R 5 0) (PB := recF R 5 1) (C := recC R 5 2)
    (POS := recPOS R 5 2) (n := n) hk' hn hfuel hT0 hd hC0 hCn' hS' hB'
  exact ⟨r1, r2, hlt, srt_of_rows hr⟩

end Orbit

theorem bsK_sound (X S : ℕ → ℕ) (x : ℕ) : ∀ f lo hi, bsK X S x f lo hi = true →
    ∃ m, lo ≤ m ∧ m < hi ∧ X (S m) = x
  | 0, _, _, h => absurd h Bool.false_ne_true
  | f + 1, lo, hi, h => by
    change bIf(Nat.blt lo hi, strictY (Nat.shiftRight (Nat.add lo hi) 1) fun m =>
      strictY (X (S m)) fun v => bIf(Nat.beq v x, true,
        bIf(Nat.blt v x, bsK X S x f (Nat.succ m) hi, bsK X S x f lo m)), false) = true at h
    cases hb : Nat.blt lo hi
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb, strictY_eq, strictY_eq] at h
      change bIf(_, _, _) = true at h
      have hlh : lo < hi := Nat.blt_eq.mp hb
      have hsr : Nat.shiftRight (Nat.add lo hi) 1 = (lo + hi) / 2 := by
        change (lo + hi) >>> 1 = _
        rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      have hm1 : lo ≤ Nat.shiftRight (Nat.add lo hi) 1 := by
        rw [hsr]
        omega
      have hm2 : Nat.shiftRight (Nat.add lo hi) 1 < hi := by
        rw [hsr]
        omega
      generalize Nat.shiftRight (Nat.add lo hi) 1 = m at h hm1 hm2
      cases he : Nat.beq (X (S m)) x
      · rw [he] at h
        change bIf(_, _, _) = true at h
        cases hl : Nat.blt (X (S m)) x
        · rw [hl] at h
          obtain ⟨m', h1, h2, h3⟩ := bsK_sound X S x f lo m h
          exact ⟨m', h1, by omega, h3⟩
        · rw [hl] at h
          obtain ⟨m', h1, h2, h3⟩ := bsK_sound X S x f (Nat.succ m) hi h
          exact ⟨m', by omega, h2, h3⟩
      · exact ⟨m, hm1, hm2, Nat.beq_eq.mp he⟩

theorem memK_sound {R : ℕ → ℕ} {o n x : ℕ} (h : memK R o n x = true) :
    ∃ m < n, recX R o (recF R o 2 m) = x := by
  obtain ⟨m, -, h2, h3⟩ := bsK_sound _ _ _ _ _ _ h
  exact ⟨m, h2, h3⟩

theorem isSome_of_memK {R : ℕ → ℕ} {n x : ℕ} {E : Enum}
    (hE : BInvE (fun t => arrF (recX R 5 t)) (recF R 5 0) (recF R 5 1) n E)
    (hs : ∀ m < n, recF R 5 2 m < n) (h : memK R 5 n x = true) :
    (E.lookup (arrF x)).isSome = true := by
  obtain ⟨m, hm, he⟩ := memK_sound h
  have l := lookup_of_inv (T := fun t => arrF (recX R 5 t)) hE (hs m hm)
  beta_reduce at l
  rw [he] at l
  rw [l]
  rfl

theorem clsAt_arrF {RA RB : ℕ → ℕ} {nA nB X : ℕ} {EA EB : Enum} (hX : X < 2 ^ 36)
    (hEA : BInvE (fun t => arrF (recX RA 5 t)) (recF RA 5 0) (recF RA 5 1) nA EA)
    (hsA : ∀ m < nA, recF RA 5 2 m < nA)
    (hEB : BInvE (fun t => arrF (recX RB 5 t)) (recF RB 5 0) (recF RB 5 1) nB EB)
    (hsB : ∀ m < nB, recF RB 5 2 m < nB) (h : clsAt RA nA RB nB X = true) :
    (!(compA (arrF X) (arrF X) == idA ()) || arrF X == idA () || (EA.lookup (arrF X)).isSome ||
      (EB.lookup (arrF X)).isSome) = true := by
  rw [arrF_mul, ← arrF_one, beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) CFSG.KC.YamakiS0.ONE_lt,
    beq_arrF hX CFSG.KC.YamakiS0.ONE_lt]
  unfold clsAt at h
  cases h1 : Nat.beq (MULF X X) ONE
  · rfl
  · rw [h1] at h
    change bIf(_, _, _) = true at h
    cases h2 : Nat.beq X ONE
    · rw [h2] at h
      change bIf(_, _, _) = true at h
      cases h3 : memK RA 5 nA X
      · rw [h3] at h
        change memK RB 5 nB X = true at h
        rw [isSome_of_memK hEB hsB h]
        simp
      · rw [isSome_of_memK hEA hsA h3]
        simp
    · simp

theorem sumBelow_eq_sumO (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have hgen : ∀ h, sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
        omega
      simp only [e, nIf_eqO, Nat.blt_eq]
  rw [hgen hi, show 64 * hi = m + (64 * hi - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem centCount_eq {E : Enum} {R : ℕ → ℕ} {o n Y : ℕ} (hsz : E.elems.size = n)
    (hel : ∀ t < n, E.elems[t]! = arrF (recX R o t)) (hlt : ∀ t < n, recX R o t < 2 ^ 36)
    (hY : Y < 2 ^ 36) :
    Nat.count (fun i => commB E.elems[i]! (arrF Y) = true) E.elems.size = cntK R o n Y := by
  have hm : n ≤ 64 * Nat.add (Nat.shiftRight n 6) 1 := by
    change n ≤ 64 * (n >>> 6 + 1)
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 6 = 64 from rfl]
    omega
  rw [cntK, sumBelow_eq_sumO _ _ _ hm, hsz, Nat.count_eq_card_filter_range, Finset.card_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [strictN_eqO, commN, nIf_eqO, hel t ht', commB, arrF_mul, arrF_mul,
    beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]

@[expose] def omClsBody (E EA EB : Enum) (xa xb : Array ℕ) : Bool :=
  conjTreeOK EA (genA6 ()) (genA6Inv ()) xa && conjTreeOK EB (genA6 ()) (genA6Inv ()) xb &&
    E.elems.all fun x => !(compA x x == idA ()) || x == idA () || (EA.lookup x).isSome ||
      (EB.lookup x).isSome

theorem omClassCheck_eq : omClassCheck () =
    omClsBody (bfsEnum (genA6 ()) 25920) (conjEnum (genA6 ()) (genA6Inv ()) (marr rAMat) 100)
      (conjEnum (genA6 ()) (genA6Inv ()) (marr rBMat) 400) (marr rAMat) (marr rBMat) := rfl

@[expose] def centBody (E : Enum) (x y z : Array ℕ) : Bool :=
  Nat.count (fun i => commB E.elems[i]! x = true) E.elems.size == 720 &&
    Nat.count (fun i => commB E.elems[i]! y = true) E.elems.size == 576 &&
    Nat.count (fun i => commB E.elems[i]! z = true) E.elems.size == 96

theorem centCountCheck_eq : centCountCheck () =
    centBody (bfsEnum (genA6 ()) 25920) (marr rMat) (marr rAMat) (marr rBMat) := rfl

section Checks

variable {R RA RB : ℕ → ℕ}

theorem genA6_get (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1)) :
    ∀ j < 2, (genA6 ())[j]! = arrF (R (0 + j)) := by
  intro j hj
  rcases j with _ | _ | j
  · rw [Nat.add_zero, arrF, ← hA]
    rfl
  · rw [Nat.zero_add, arrF, ← hB]
    rfl
  · omega

theorem omega_inv (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true) :
    BInvE (fun t => arrF (recX R 10 t)) (recF R 10 0) (recF R 10 1) 25920
        (bfsEnum (genA6 ()) 25920) ∧ ∀ t < 25920, recX R 10 t < 2 ^ 36 := by
  have T := table_invF (gs := genA6 ()) (R := R) (o := 10) (n := 25920) (k := 2) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num) (genA6_get hA hB) hh
    (rows_of_chunks (L := 512) (m := 51) (fun q hq => chunkK_of_chunkF (hc q hq)) (by norm_num))
  exact ⟨T.1, T.2.2⟩

theorem orbitO {S : ℕ → ℕ} {n fuel L m : ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hn : 0 < n) (hfuel : n ≤ fuel) (hm : n ≤ L * m) (h4 : S 4 < 2 ^ 36)
    (hd : hdrC S (R 0) (R 1) (S 4) = true) (hh : headC S 5 n = true)
    (hc : ∀ q < m, chunkF S (cjG S) 5 n L q = true) :
    BInvE (fun t => arrF (recX S 5 t)) (recF S 5 0) (recF S 5 1) n
        (conjEnum (genA6 ()) (genA6Inv ()) (arrF (S 4)) fuel) ∧
      conjTreeOK (conjEnum (genA6 ()) (genA6Inv ()) (arrF (S 4)) fuel) (genA6 ()) (genA6Inv ())
        (arrF (S 4)) = true ∧
      (∀ t < n, recX S 5 t < 2 ^ 36) ∧ ∀ m < n, recF S 5 2 m < n := by
  unfold hdrC at hd
  simp only [bAnd_iffO, Nat.beq_eq] at hd
  obtain ⟨d0, d1, d2, d3, -⟩ := hd
  have hg : ∀ j < 2, (genA6 ())[j]! = arrF (S j) := by
    intro j hj
    have := genA6_get hA hB j hj
    rw [Nat.zero_add] at this
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [this, d0]
    · rw [this, d1]
  have hgi : ∀ j < 2, (genA6Inv ())[j]! = arrF (S (2 + j)) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · change marr aMat = arrF (S 2)
      rw [d2, hA]
      rfl
    · change marr (bMat * (bMat * (bMat * bMat))) = arrF (S 3)
      rw [d3, hB, arrF, matF_mul, matF_mul, matF_mul]
  exact orbit_inv (fuel := fuel) rfl hn hfuel hg hgi rfl h4 hh
    (rows_of_chunks (fun q hq => chunkK_of_chunkF (hc q hq)) hm)

theorem omClassCheck_of (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hrA : rAMat = matF (RA 4)) (hrB : rBMat = matF (RB 4)) (hlt : ∀ j < 10, R j < 2 ^ 36)
    (hA4 : RA 4 = R 3) (hB4 : RB 4 = R 4)
    (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (hdA : hdrC RA (R 0) (R 1) (RA 4) = true) (hhA : headC RA 5 45 = true)
    (hcA : ∀ q < 2, chunkF RA (cjG RA) 5 45 32 q = true)
    (hdB : hdrC RB (R 0) (R 1) (RB 4) = true) (hhB : headC RB 5 270 = true)
    (hcB : ∀ q < 9, chunkF RB (cjG RB) 5 270 32 q = true)
    (hcl : ∀ q < 51, clsChunk R 10 25920 RA 45 RB 270 512 q = true) :
    omClassCheck () = true := by
  have T := omega_inv hA hB hh hc
  have OA := orbitO (S := RA) (fuel := 100) hA hB (by norm_num) (by norm_num) (by norm_num)
    (by rw [hA4]; exact hlt 3 (by norm_num)) hdA hhA hcA
  have OB := orbitO (S := RB) (fuel := 400) hA hB (by norm_num) (by norm_num) (by norm_num)
    (by rw [hB4]; exact hlt 4 (by norm_num)) hdB hhB hcB
  have mA : marr rAMat = arrF (RA 4) := by rw [hrA]; rfl
  have mB : marr rBMat = arrF (RB 4) := by rw [hrB]; rfl
  rw [omClassCheck_eq, mA, mB, omClsBody, OA.2.1, OB.2.1, Bool.true_and, Bool.true_and,
    Array.all_eq_true]
  intro i hi
  have hsz := T.1.1
  have hi' : i < 25920 := by omega
  rw [← getElem!_pos _ i hi, T.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks 512 51 _ hcl i (by omega)
  change bIf(Nat.blt i 25920, strictY (recX R 10 i) (clsAt RA 45 RB 270), true) = true at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  exact clsAt_arrF (T.2 i hi') OA.1 OA.2.2.2 OB.1 OB.2.2.2 hall

theorem centCountCheck_of (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hr : rMat = matF (R 2)) (hrA : rAMat = matF (R 3)) (hrB : rBMat = matF (R 4))
    (hlt : ∀ j < 10, R j < 2 ^ 36) (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (h1 : Nat.beq (cntK R 10 25920 (R 2)) 720 = true)
    (h2 : Nat.beq (cntK R 10 25920 (R 3)) 576 = true)
    (h3 : Nat.beq (cntK R 10 25920 (R 4)) 96 = true) :
    centCountCheck () = true := by
  have T := omega_inv hA hB hh hc
  have m2 : marr rMat = arrF (R 2) := by rw [hr]; rfl
  have m3 : marr rAMat = arrF (R 3) := by rw [hrA]; rfl
  have m4 : marr rBMat = arrF (R 4) := by rw [hrB]; rfl
  rw [centCountCheck_eq, m2, m3, m4, centBody,
    centCount_eq T.1.1 T.1.2.2.2.1 T.2 (hlt 2 (by norm_num)),
    centCount_eq T.1.1 T.1.2.2.2.1 T.2 (hlt 3 (by norm_num)),
    centCount_eq T.1.1 T.1.2.2.2.1 T.2 (hlt 4 (by norm_num)), Nat.beq_eq.mp h1, Nat.beq_eq.mp h2,
    Nat.beq_eq.mp h3]
  rfl

end Checks

end CFSG.KC.OmegaSix

end
