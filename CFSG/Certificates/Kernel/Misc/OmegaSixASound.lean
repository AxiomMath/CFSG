module

public import Certificates.Data.Kernel.Misc.OmegaSixA
public import CFSG.Certificates.Kernel.Misc.OmegaSixOSound

public section

namespace CFSG.KC.OmegaSix

open Matrix CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux
  CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.OmegaSix CFSG.KD.YamakiRep
  CFSG.KD.YamakiRepF CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.ConjEnum CFSG.KC.YamakiRep
  CFSG.KC.YamakiRepF CFSG.KC.Loop CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

section Orbit

variable {G S : ℕ → ℕ} {n : ℕ}

theorem cjO_arrF {gs gsInv : Array (Array ℕ)} (hg : ∀ j < 3, gs[j]! = arrF (G j))
    (hgi : ∀ j < 3, gsInv[j]! = arrF (S j)) {s : ℕ} (hs : s < 3) (X : ℕ) :
    arrF (cjO G S X s) = cj gs gsInv (arrF X) s := by
  rw [cjO, cj, hg s hs, hgi s hs, arrF_mul, arrF_mul]

theorem orbit_inv3 {gs gsInv : Array (Array ℕ)} {x : Array ℕ} {fuel : ℕ} (hk : gs.size = 3)
    (hn : 0 < n) (hfuel : n ≤ fuel) (hg : ∀ j < 3, gs[j]! = arrF (G j))
    (hgi : ∀ j < 3, gsInv[j]! = arrF (S j)) (hx : x = arrF (S 4)) (h4 : S 4 < 2 ^ 36)
    (hh : headC3 S 5 n = true) (hr : ∀ t < n, rowK S (cjO G S) 5 n 3 t = true) :
    BInvE (fun t => arrF (recX S 5 t)) (recF S 5 0) (recF S 5 1) n
        (conjEnum gs gsInv x fuel) ∧
      conjTreeOK (conjEnum gs gsInv x fuel) gs gsInv x = true ∧
      (∀ t < n, recX S 5 t < 2 ^ 36) ∧ ∀ m < n, recF S 5 2 m < n := by
  unfold headC3 at hh
  simp only [bAnd_iffO, Nat.beq_eq] at hh
  obtain ⟨h0, hC0, hCn⟩ := hh
  have hBi := build_of_rows hr
  have hSi := step_of_rows (by norm_num) (by norm_num) hr
  have hX := sort_of_rows hr
  have hlt : ∀ t < n, recX S 5 t < 2 ^ 36 := by
    intro t ht
    cases t with
    | zero => rw [h0]; exact h4
    | succ t =>
      rw [(hBi t (by omega)).2.2]
      exact CFSG.KC.Sp62.MULF_lt _ _
  have hk' : 0 < gs.size := by rw [hk]; norm_num
  have hd : ∀ t < n, ∀ t' < n, arrF (recX S 5 t) = arrF (recX S 5 t') → t = t' :=
    fun t ht t' ht' e => hX t ht t' ht' (arrF_inj (hlt t ht) (hlt t' ht') e)
  have hT0 : arrF (recX S 5 0) = x := by rw [h0, hx]
  have hS' : ∀ i < n * gs.size, StepC gs gsInv (fun t => arrF (recX S 5 t))
      (recF S 5 0) (recF S 5 1) (recC S 5 3) (recPOS S 5 3) n i := by
    intro i hi
    rw [hk] at hi
    unfold StepC
    rw [hk]
    obtain ⟨a, b, c, d, e, f⟩ := stepAt_facts (hSi i hi)
    refine ⟨a, b, c, ?_, e, f⟩
    beta_reduce
    rw [d, cjO_arrF hg hgi (Nat.mod_lt _ (by norm_num))]
  have hB' : ∀ i < n - 1, recF S 5 0 i ≤ i ∧ recF S 5 1 i < gs.size ∧
      arrF (recX S 5 (i + 1)) = cj gs gsInv (arrF (recX S 5 (recF S 5 0 i))) (recF S 5 1 i) := by
    intro i hi
    obtain ⟨a, b, c⟩ := hBi i hi
    refine ⟨a, by rw [hk]; exact b, ?_⟩
    rw [c, cjO_arrF hg hgi b]
  have hCn' : recC S 5 3 (n * gs.size) = n := by rw [hk]; exact hCn
  have r1 := conjEnum_replay (gs := gs) (gsInv := gsInv) (fuel := fuel)
    (T := fun t => arrF (recX S 5 t)) (PA := recF S 5 0) (PB := recF S 5 1) (C := recC S 5 3)
    (POS := recPOS S 5 3) (n := n) hk' hn hfuel hT0 hd hC0 hCn' hS'
  have r2 := conjTreeOK_of_replay (gs := gs) (gsInv := gsInv) (fuel := fuel)
    (T := fun t => arrF (recX S 5 t)) (PA := recF S 5 0) (PB := recF S 5 1) (C := recC S 5 3)
    (POS := recPOS S 5 3) (n := n) hk' hn hfuel hT0 hd hC0 hCn' hS' hB'
  exact ⟨r1, r2, hlt, srt_of_rows hr⟩

theorem genO_get (hA : aMat = matF (G 0)) (hB : bMat = matF (G 1)) (hr : rMat = matF (G 2)) :
    ∀ j < 3, (genO ())[j]! = arrF (G j) := by
  intro j hj
  rcases j with _ | _ | _ | j
  · rw [arrF, ← hA]
    rfl
  · rw [arrF, ← hB]
    rfl
  · rw [arrF, ← hr]
    rfl
  · omega

theorem orbitO3 {L m fuel x : ℕ} (hA : aMat = matF (G 0)) (hB : bMat = matF (G 1))
    (hr : rMat = matF (G 2)) (hn : 0 < n) (hfuel : n ≤ fuel) (hm : n ≤ L * m)
    (h4 : x < 2 ^ 36) (hd : hdrO S (G 0) (G 1) (G 2) x = true) (hh : headC3 S 5 n = true)
    (hc : ∀ q < m, chunkF3 S (cjO G S) 5 n L q = true) :
    BInvE (fun t => arrF (recX S 5 t)) (recF S 5 0) (recF S 5 1) n
        (conjEnum (genO ()) (genOInv ()) (arrF x) fuel) ∧
      conjTreeOK (conjEnum (genO ()) (genOInv ()) (arrF x) fuel) (genO ()) (genOInv ())
        (arrF x) = true ∧
      (∀ t < n, recX S 5 t < 2 ^ 36) ∧ ∀ m < n, recF S 5 2 m < n := by
  unfold hdrO at hd
  simp only [bAnd_iffO, Nat.beq_eq] at hd
  obtain ⟨d0, d1, d2, d4⟩ := hd
  subst d4
  have hgi : ∀ j < 3, (genOInv ())[j]! = arrF (S j) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · change marr aMat = arrF (S 0)
      rw [d0, hA]
      rfl
    · change marr (bMat * (bMat * (bMat * bMat))) = arrF (S 1)
      rw [d1, hB, arrF, matF_mul, matF_mul, matF_mul]
    · change marr rMat = arrF (S 2)
      rw [d2, hr]
      rfl
  exact orbit_inv3 (fuel := fuel) rfl hn hfuel (genO_get hA hB hr) hgi rfl h4 hh
    (rows_of_chunks (fun q hq => chunkK_of_chunkF3 (hc q hq)) hm)

end Orbit

theorem marr_xor (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) {p q : ℕ}
    (hp : p < 64) (hq : q < 64) : (marr A)[p ^^^ q]! = (marr A)[p]! ^^^ (marr A)[q]! := by
  have hx : p ^^^ q < 64 := Nat.xor_lt_two_pow (n := 6) hp hq
  have l1 : (marr A)[p ^^^ q]! < 64 := by
    rw [marr_get A hx]
    exact vcode_lt _
  have l2 : (marr A)[p]! ^^^ (marr A)[q]! < 64 := by
    rw [marr_get A hp, marr_get A hq]
    exact Nat.xor_lt_two_pow (n := 6) (vcode_lt _) (vcode_lt _)
  have h1 : cvec (marr A)[p ^^^ q]! = cvec ((marr A)[p]! ^^^ (marr A)[q]!) := by
    rw [cvec_xor, ← mulVec_cvec A hx, ← mulVec_cvec A hp, ← mulVec_cvec A hq, cvec_xor,
      Matrix.mulVec_add]
  rw [← vcode_cvec _ l1, h1, vcode_cvec _ l2]

theorem subOne_xor (X : ℕ) {p q : ℕ} (hp : p < 64) (hq : q < 64) :
    subOneCode (arrF X) (p ^^^ q) = subOneCode (arrF X) p ^^^ subOneCode (arrF X) q := by
  rw [subOneCode, subOneCode, subOneCode, arrF, marr_xor _ hp hq]
  generalize (marr (matF X))[p]! = u
  generalize (marr (matF X))[q]! = v
  rw [Nat.xor_assoc, Nat.xor_assoc, ← Nat.xor_assoc v p q, Nat.xor_comm v p, Nat.xor_assoc p v q]

theorem subOne_lt (X : ℕ) {p : ℕ} (hp : p < 64) : subOneCode (arrF X) p < 64 := by
  rw [subOneCode, arrF, marr_get _ hp]
  exact Nat.xor_lt_two_pow (n := 6) (vcode_lt _) hp

theorem span64 (g : ℕ → ℕ) (P : ℕ → Prop) (h0 : P (g 0))
    (hlin : ∀ p < 64, ∀ q < 64, g (p ^^^ q) = g p ^^^ g q)
    (hcl : ∀ u v, P u → P v → P (u ^^^ v)) (hb : ∀ i < 6, P (g (2 ^ i))) :
    ∀ k < 64, P (g k) := by
  have hdec : ∀ k < 64, k = 0 ∨ ∃ i < 6, k ^^^ 2 ^ i < k := by decide
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases hdec k hk with rfl | ⟨i, hi, hlt⟩
    · exact h0
    · have hp : 2 ^ i < 64 :=
        calc 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hi
          _ = 64 := by norm_num
      have e : k = (k ^^^ 2 ^ i) ^^^ 2 ^ i := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [e, hlin _ (by omega) _ hp]
      exact hcl _ _ (ih _ hlt (by omega)) (hb i hi)

theorem rank1_of {X : ℕ} (h : rank1K X = true) : rank1 (arrF X) = true := by
  obtain ⟨c, hc, h1⟩ := anyK_sound _ 6 h
  rw [strictY_eq] at h1
  have h64 : ∀ c < 6, 2 ^ c < 64 := fun c hc => by
    calc 2 ^ c < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hc
      _ = 64 := by norm_num
  cases ha : Nat.beq (subK X c) 0
  · rw [ha] at h1
    change CFSG.KC.Misc.Clos.allR 0 6 _ = true at h1
    rw [CFSG.KC.Misc.Clos.allR_iff] at h1
    have ha' : subK X c ≠ 0 := fun e => by rw [e] at ha; exact absurd ha (by decide)
    have hall : ∀ d < 6, subK X d = 0 ∨ subK X d = subK X c := by
      intro d hd
      have e := h1 d (Nat.zero_le _) (by omega)
      rw [strictY_eq] at e
      cases hb : Nat.beq (subK X d) 0
      · rw [hb] at e
        exact Or.inr (Nat.beq_eq.mp e)
      · exact Or.inl (Nat.beq_eq.mp hb)
    have hP : ∀ k < 64, subOneCode (arrF X) k = 0 ∨ subOneCode (arrF X) k = subK X c := by
      refine span64 (subOneCode (arrF X)) (fun v => v = 0 ∨ v = subK X c) ?_
        (fun p hp q hq => subOne_xor X hp hq) ?_ ?_
      · have e := subOne_xor X (p := 0) (q := 0) (by norm_num) (by norm_num)
        rw [Nat.xor_self, Nat.xor_self] at e
        exact Or.inl e
      · rintro u v (rfl | rfl) (rfl | rfl) <;> simp
      · intro i hi
        rw [subOne_eq X i hi]
        exact hall i hi
    have hc64 : subK X c < 64 := by
      rw [← subOne_eq X c hc]
      exact subOne_lt X (h64 c hc)
    simp only [rank1, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.and_eq_true,
      bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq]
    refine ⟨subK X c, hc64, ⟨ha', 2 ^ c, h64 c hc, ?_⟩, fun k hk => hP k hk⟩
    rw [← subOne_eq X c hc]
    rfl
  · rw [ha] at h1
    exact absurd h1 Bool.false_ne_true

theorem matF_ONE : matF ONE = 1 := by
  rw [matF, CFSG.KC.YamakiS0.pkMat_ONE, ofBits_eq, Matrix.submatrix_one_equiv]

theorem eqF {A B : ℕ} (hA : A < 2 ^ 36) (hB : B < 2 ^ 36) (h : matF A = matF B) : A = B :=
  arrF_inj hA hB (by rw [arrF, arrF, h])

theorem beqF (A B : ℕ) : (arrF (MULF A B) == arrF ONE) = Nat.beq (MULF A B) ONE :=
  beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) CFSG.KC.YamakiS0.ONE_lt

theorem relA_eq (X Y : ℕ) :
    (a6Rels.all fun w => wordA #[arrF X, arrF Y] w == idA ()) = relK X Y := by
  have e0 : (#[arrF X, arrF Y] : Array (Array ℕ))[0]! = arrF X := rfl
  have e1 : (#[arrF X, arrF Y] : Array (Array ℕ))[1]! = arrF Y := rfl
  simp only [a6Rels, List.all_cons, List.all_nil, Bool.and_true, wordA, e0, e1, ← arrF_one,
    arrF_mul, beqF]
  have F1 : MULF Y (MULF Y (MULF Y (MULF Y ONE))) = MULF (MULF Y Y) (MULF Y Y) :=
    eqF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _) (by
      simp only [matF_mul, matF_ONE, mul_one, mul_assoc])
  have F2 : MULF X (MULF X ONE) = MULF X X :=
    eqF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _) (by
      simp only [matF_mul, matF_ONE, mul_one, mul_assoc])
  have F3 : MULF X (MULF Y (MULF X (MULF Y (MULF X (MULF Y (MULF X (MULF Y (MULF X
      (MULF Y ONE))))))))) =
      MULF (MULF (MULF (MULF X Y) (MULF X Y)) (MULF (MULF X Y) (MULF X Y))) (MULF X Y) :=
    eqF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _) (by
      simp only [matF_mul, matF_ONE, mul_one, mul_assoc])
  have F4 : MULF X (MULF Y (MULF Y (MULF X (MULF Y (MULF Y (MULF X (MULF Y (MULF Y (MULF X
      (MULF Y (MULF Y (MULF X (MULF Y (MULF Y ONE)))))))))))))) =
      MULF (MULF (MULF (MULF X (MULF Y Y)) (MULF X (MULF Y Y)))
        (MULF (MULF X (MULF Y Y)) (MULF X (MULF Y Y)))) (MULF X (MULF Y Y)) :=
    eqF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _) (by
      simp only [matF_mul, matF_ONE, mul_one, mul_assoc])
  rw [F1, F2, F3, F4]
  unfold relK
  simp only [strictY_eq]
  cases Nat.beq (MULF (MULF Y Y) (MULF Y Y)) ONE <;> cases Nat.beq (MULF X X) ONE <;>
    cases Nat.beq (MULF (MULF (MULF (MULF X Y) (MULF X Y)) (MULF (MULF X Y) (MULF X Y)))
      (MULF X Y)) ONE <;>
    cases Nat.beq (MULF (MULF (MULF (MULF X (MULF Y Y)) (MULF X (MULF Y Y)))
      (MULF (MULF X (MULF Y Y)) (MULF X (MULF Y Y)))) (MULF X (MULF Y Y))) ONE <;> rfl

theorem isSome_of_memK_at {R : ℕ → ℕ} {o n x : ℕ} {E : Enum}
    (hE : BInvE (fun t => arrF (recX R o t)) (recF R o 0) (recF R o 1) n E)
    (hs : ∀ m < n, recF R o 2 m < n) (h : memK R o n x = true) :
    (E.lookup (arrF x)).isSome = true := by
  obtain ⟨m, hm, he⟩ := memK_sound h
  have l := lookup_of_inv (T := fun t => arrF (recX R o t)) hE (hs m hm)
  beta_reduce at l
  rw [he] at l
  rw [l]
  rfl

theorem lookup_lift {RA SA : ℕ → ℕ} {nA nS : ℕ} {EA ES : Enum} {x : Array ℕ}
    (hEA : BInvE (fun t => arrF (recX RA 5 t)) (recF RA 5 0) (recF RA 5 1) nA EA)
    (hES : BInvE (fun t => arrF (recX SA 5 t)) (recF SA 5 0) (recF SA 5 1) nS ES)
    (hsS : ∀ m < nS, recF SA 5 2 m < nS) (hsub : subOrbK RA nA SA nS = true)
    (h : (EA.lookup x).isSome = true) : (ES.lookup x).isSome = true := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
  rw [hEA.1] at hks
  unfold subOrbK at hsub
  rw [CFSG.KC.Misc.Clos.allR_iff] at hsub
  have hm := hsub k (Nat.zero_le _) (by omega)
  rw [← hke, hEA.2.2.2.1 k hks]
  exact isSome_of_memK hES hsS hm

@[expose] def cls4Body (E EA EB : Enum) (xa xb : Array ℕ) : Bool :=
  conjTreeOK EA (genO ()) (genOInv ()) xa && conjTreeOK EB (genO ()) (genOInv ()) xb &&
    E.elems.all fun x => !(compA x x == idA ()) || x == idA () || (EA.lookup x).isSome ||
      (EB.lookup x).isSome

theorem classCheck_eq : classCheck () =
    cls4Body (bfsEnum (genA6 ()) 25920) (conjEnum (genO ()) (genOInv ()) (marr rAMat) 100)
      (conjEnum (genO ()) (genOInv ()) (marr rBMat) 400) (marr rAMat) (marr rBMat) := rfl

@[expose] def cent4Body (E EO : Enum) (xa xb : Array ℕ) : Bool :=
  [xa, xb].all fun x =>
    E.elems.all fun y => !(a6Rels.all fun w => wordA #[x, y] w == idA ()) ||
      (EO.elems.filter fun t => compA t x == compA x t && !(t == idA ())).all fun t =>
        !(compA t y == compA y t) || rank1 t

theorem centCheck_eq : centCheck () =
    cent4Body (bfsEnum (genA6 ()) 25920) (bfsEnum (genO ()) 51840) (marr rAMat) (marr rBMat) :=
  rfl

section Checks

variable {R G : ℕ → ℕ}

theorem oEnumCheck_of {L m : ℕ} (hA : aMat = matF (G 0)) (hB : bMat = matF (G 1))
    (hr : rMat = matF (G 2)) (hm : 51840 ≤ L * m) (hh : headK G 3 51840 3 = true)
    (hc : ∀ q < m, chunkF3 G (rstG G 0) 3 51840 L q = true) : oEnumCheck () = true := by
  have T := table_invF (gs := genO ()) (R := G) (o := 3) (n := 51840) (k := 3) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num)
    (fun j hj => by rw [Nat.zero_add]; exact genO_get hA hB hr j hj) hh
    (rows_of_chunks (L := L) (m := m) (fun q hq => chunkK_of_chunkF3 (hc q hq)) hm)
  change (enumOK (bfsEnum (genO ()) 51840) (genO ()) &&
    (bfsEnum (genO ()) 51840).elems.size == 51840) = true
  rw [T.2.1, T.1.1]
  rfl

theorem repCheck_of (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hrA : rAMat = matF (R 3)) (hrB : rBMat = matF (R 4)) (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (h3 : memK R 10 25920 (R 3) = true) (h4 : memK R 10 25920 (R 4) = true) :
    repCheck () = true := by
  have T := omega_inv hA hB hh hc
  have hs := srt_of_rows (rows_of_chunks (L := 512) (m := 51)
    (fun q hq => chunkK_of_chunkF (hc q hq)) (by norm_num))
  have mA : marr rAMat = arrF (R 3) := by rw [hrA]; rfl
  have mB : marr rBMat = arrF (R 4) := by rw [hrB]; rfl
  change ((bfsEnum (genA6 ()) 25920).lookup (marr rAMat)).isSome &&
    ((bfsEnum (genA6 ()) 25920).lookup (marr rBMat)).isSome = true
  rw [mA, mB, isSome_of_memK_at T.1 hs h3, isSome_of_memK_at T.1 hs h4]
  rfl

theorem classCheck_of {RA RB SA SB : ℕ → ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hrA : rAMat = matF (R 3)) (hrB : rBMat = matF (R 4)) (hlt : ∀ j < 10, R j < 2 ^ 36)
    (hA4 : RA 4 = R 3) (hB4 : RB 4 = R 4) (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (hdA : hdrC RA (R 0) (R 1) (RA 4) = true) (hhA : headC RA 5 45 = true)
    (hcA : ∀ q < 2, chunkF RA (cjG RA) 5 45 32 q = true)
    (hdB : hdrC RB (R 0) (R 1) (RB 4) = true) (hhB : headC RB 5 270 = true)
    (hcB : ∀ q < 9, chunkF RB (cjG RB) 5 270 32 q = true)
    (hcl : ∀ q < 51, clsChunk R 10 25920 RA 45 RB 270 512 q = true)
    (hA' : aMat = matF (G 0)) (hB' : bMat = matF (G 1)) (hr' : rMat = matF (G 2))
    (hdSA : hdrO SA (G 0) (G 1) (G 2) (R 3) = true) (hhSA : headC3 SA 5 45 = true)
    (hcSA : chunkF3 SA (cjO G SA) 5 45 512 0 = true)
    (hdSB : hdrO SB (G 0) (G 1) (G 2) (R 4) = true) (hhSB : headC3 SB 5 270 = true)
    (hcSB : chunkF3 SB (cjO G SB) 5 270 512 0 = true)
    (hsA : subOrbK RA 45 SA 45 = true) (hsB : subOrbK RB 270 SB 270 = true) :
    classCheck () = true := by
  have T := omega_inv hA hB hh hc
  have OA := orbitO (S := RA) (fuel := 100) hA hB (by norm_num) (by norm_num) (by norm_num)
    (by rw [hA4]; exact hlt 3 (by norm_num)) hdA hhA hcA
  have OB := orbitO (S := RB) (fuel := 400) hA hB (by norm_num) (by norm_num) (by norm_num)
    (by rw [hB4]; exact hlt 4 (by norm_num)) hdB hhB hcB
  have SA3 := orbitO3 (S := SA) (L := 512) (m := 1) (fuel := 100) hA' hB' hr' (by norm_num)
    (by norm_num) (by norm_num) (hlt 3 (by norm_num)) hdSA hhSA
    (fun q hq => by rw [Nat.lt_one_iff.mp hq]; exact hcSA)
  have SB3 := orbitO3 (S := SB) (L := 512) (m := 1) (fuel := 400) hA' hB' hr' (by norm_num)
    (by norm_num) (by norm_num) (hlt 4 (by norm_num)) hdSB hhSB
    (fun q hq => by rw [Nat.lt_one_iff.mp hq]; exact hcSB)
  have mA : marr rAMat = arrF (R 3) := by rw [hrA]; rfl
  have mB : marr rBMat = arrF (R 4) := by rw [hrB]; rfl
  rw [classCheck_eq, mA, mB, cls4Body, SA3.2.1, SB3.2.1, Bool.true_and, Bool.true_and,
    Array.all_eq_true]
  intro i hi
  have hsz := T.1.1
  have hi' : i < 25920 := by omega
  rw [← getElem!_pos _ i hi, T.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks 512 51 _ hcl i (by omega)
  change bIf(Nat.blt i 25920, strictY (recX R 10 i) (clsAt RA 45 RB 270), true) = true at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  have l := clsAt_arrF (T.2 i hi') OA.1 OA.2.2.2 OB.1 OB.2.2.2 hall
  simp only [Bool.or_eq_true] at l ⊢
  rcases l with ((l | l) | l) | l
  · exact Or.inl (Or.inl (Or.inl l))
  · exact Or.inl (Or.inl (Or.inr l))
  · exact Or.inl (Or.inr (lookup_lift OA.1 SA3.1 SA3.2.2.2 hsA l))
  · exact Or.inr (lookup_lift OB.1 SB3.1 SB3.2.2.2 hsB l)

theorem centCheck_of {L : ℕ → ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hrA : rAMat = matF (R 3)) (hrB : rBMat = matF (R 4)) (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (hA' : aMat = matF (G 0)) (hB' : bMat = matF (G 1)) (hr' : rMat = matF (G 2))
    (hhO : headK G 3 51840 3 = true)
    (hcO : ∀ q < 203, chunkF3 G (rstG G 0) 3 51840 256 q = true)
    (hE : ∀ q < 51, centChunk R 10 25920 (R 3) (R 4) L 191 512 q = true)
    (hO : ∀ q < 102, cLChunk G 3 51840 (R 4) L 191 512 q = true) :
    centCheck () = true := by
  have T := omega_inv hA hB hh hc
  have TO := oEnum_inv (L := 256) (m := 203) hA' hB' hr' (by norm_num) hhO hcO
  have mA : marr rAMat = arrF (R 3) := by rw [hrA]; rfl
  have mB : marr rBMat = arrF (R 4) := by rw [hrB]; rfl
  rw [centCheck_eq, cent4Body, mA, mB]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  have hY : ∀ i (hi : i < (bfsEnum (genA6 ()) 25920).elems.size),
      (bfsEnum (genA6 ()) 25920).elems[i] = arrF (recX R 10 i) ∧
        centAt (R 3) (R 4) L 191 (recX R 10 i) = true := by
    intro i hi
    have hi' : i < 25920 := by rw [T.1.1] at hi; exact hi
    refine ⟨by rw [← getElem!_pos _ i hi]; exact T.1.2.2.2.1 i hi', ?_⟩
    have hall := CFSG.KC.Misc.Clos.forall_of_chunks 512 51 _ hE i (by omega)
    change bIf(Nat.blt i 25920, strictY (recX R 10 i) (centAt (R 3) (R 4) L 191), true) =
      true at hall
    rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
    exact hall
  constructor
  · rw [Array.all_eq_true]
    intro i hi
    obtain ⟨e, hc'⟩ := hY i hi
    rw [e, relA_eq]
    unfold centAt at hc'
    cases h1 : relK (R 3) (recX R 10 i)
    · rfl
    · rw [h1] at hc'
      exact absurd hc' Bool.false_ne_true
  · rw [Array.all_eq_true]
    intro i hi
    obtain ⟨e, hc'⟩ := hY i hi
    rw [e, relA_eq]
    unfold centAt at hc'
    cases h1 : relK (R 3) (recX R 10 i)
    · rw [h1] at hc'
      change bIf(relK (R 4) (recX R 10 i), centL L 191 (recX R 10 i), true) = true at hc'
      cases h2 : relK (R 4) (recX R 10 i)
      · rfl
      · rw [h2] at hc'
        change centL L 191 (recX R 10 i) = true at hc'
        rw [Bool.not_true, Bool.false_or, Array.all_eq_true_iff_forall_mem]
        intro t ht
        rw [Array.mem_filter] at ht
        obtain ⟨ht1, ht2⟩ := ht
        obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp ht1
        have hj' : j < 51840 := by rw [TO.1.1] at hj; exact hj
        rw [← getElem!_pos _ j hj, TO.1.2.2.2.1 j hj'] at ht2 ⊢
        have hTl := TO.2 j hj'
        rw [arrF_mul, arrF_mul, beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _),
          ← arrF_one, beq_arrF hTl CFSG.KC.YamakiS0.ONE_lt, Bool.and_eq_true,
          Bool.not_eq_true'] at ht2
        obtain ⟨c1, c2⟩ := ht2
        have hall := CFSG.KC.Misc.Clos.forall_of_chunks 512 102 _ hO j (by omega)
        change bIf(Nat.blt j 51840, strictY (recX G 3 j) (cLAt (R 4) L 191), true) = true at hall
        rw [Nat.blt_eq.mpr hj', strictY_eq] at hall
        unfold cLAt at hall
        rw [c2] at hall
        change bIf(Nat.beq (MULF (recX G 3 j) (R 4)) (MULF (R 4) (recX G 3 j)),
          bsK L (fun m => m) (recX G 3 j) 16 0 191, true) = true at hall
        rw [c1] at hall
        change bsK L (fun m => m) (recX G 3 j) 16 0 191 = true at hall
        obtain ⟨m, -, hm, hLm⟩ := bsK_sound _ _ _ _ _ _ hall
        have hcl := (CFSG.KC.Misc.Clos.allR_iff _ _ _).mp hc' m (Nat.zero_le _) (by omega)
        rw [strictY_eq] at hcl
        beta_reduce at hLm
        rw [hLm] at hcl
        rw [arrF_mul, arrF_mul, beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]
        cases h3 : Nat.beq (MULF (recX G 3 j) (recX R 10 i)) (MULF (recX R 10 i) (recX G 3 j))
        · rfl
        · rw [h3] at hcl
          change rank1K (recX G 3 j) = true at hcl
          rw [rank1_of hcl, Bool.or_true]
    · rw [h1] at hc'
      exact absurd hc' Bool.false_ne_true

end Checks

end CFSG.KC.OmegaSix

end
