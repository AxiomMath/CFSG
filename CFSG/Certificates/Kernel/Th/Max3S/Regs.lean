
module

public import CFSG.Certificates.Kernel.Th.Max3S.RegsBase

public import CFSG.Certificates.Kernel.Th.Max3S.Words

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

section Nf

variable {A B : Array V4}

theorem rowsMatrix_nf (s : ℕ) (e : Fin 8 → ℕ) :
    rowsMatrix (nf A B s e) =
      rowsMatrix (z A B) ^ s * (List.ofFn fun i => rowsMatrix (q A B i) ^ e i).prod := by
  rw [nf, rowsMatrix_mulRows, rowsMatrix_powRows, rowsMatrix_prodRows, List.map_ofFn]
  congr 2
  exact congrArg List.ofFn (funext fun i => rowsMatrix_powRows _ _)

theorem nfAt_split (k k' : Fin 512) (m : Fin 8) (hk : 2 ≤ k.val)
    (hk' : k'.val = k.val - 2 ^ hbit k.val) (hm : m.val = hbit k.val - 1) :
    rowsMatrix (nfAt A B k) = rowsMatrix (nfAt A B k') * rowsMatrix (q A B m) := by
  obtain ⟨h1, h8, -, hs, hlo, htop, htop', hhi⟩ := nfBits k hk
  have e1 := rowsMatrix_nf (A := A) (B := B) (k.val % 2) fun i => k.val / 2 ^ (i.val + 1) % 2
  have e2 := rowsMatrix_nf (A := A) (B := B) (k'.val % 2) fun i => k'.val / 2 ^ (i.val + 1) % 2
  rw [← nfAt_eq] at e1 e2
  rw [e1, e2, mul_assoc, hk', ← hs]
  refine congrArg (rowsMatrix (z A B) ^ (k.val % 2) * ·) ?_
  refine prod_ofFn_top (M := Matrix (Fin 248) (Fin 248) (ZMod 2)) _ _ m _ (fun i hi => ?_) ?_ ?_
    (fun i hi => ?_)
  · have hi' : i.val + 1 < hbit k.val := by
      have := Fin.lt_def.1 hi
      omega
    show rowsMatrix (q A B i) ^ (k.val / 2 ^ (i.val + 1) % 2) =
      rowsMatrix (q A B i) ^ ((k.val - 2 ^ hbit k.val) / 2 ^ (i.val + 1) % 2)
    rw [hlo i hi']
  · show rowsMatrix (q A B m) ^ (k.val / 2 ^ (m.val + 1) % 2) = rowsMatrix (q A B m)
    rw [hm, show hbit k.val - 1 + 1 = hbit k.val by omega, htop, pow_one]
  · show rowsMatrix (q A B m) ^ ((k.val - 2 ^ hbit k.val) / 2 ^ (m.val + 1) % 2) = 1
    rw [hm, show hbit k.val - 1 + 1 = hbit k.val by omega, htop', pow_zero]
  · have hi' : hbit k.val < i.val + 1 := by
      have := Fin.lt_def.1 hi
      omega
    show rowsMatrix (q A B i) ^ (k.val / 2 ^ (i.val + 1) % 2) = 1 ∧
      rowsMatrix (q A B i) ^ ((k.val - 2 ^ hbit k.val) / 2 ^ (i.val + 1) % 2) = 1
    rw [(hhi i hi').1, (hhi i hi').2, pow_zero]
    exact ⟨rfl, rfl⟩

end Nf

variable {D : CFSG.KC.Th.Gen.Max3Data}

theorem regOK_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true) :
    RegOK D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)) := by
  set A := rowsOf (String.ofList D.ThSeed_LA) with hAdef
  set B := rowsOf (String.ofList D.ThSeed_LB) with hBdef
  have hk := consts_leaf h
  have hSA : pkMat D.ThSeed_SA = rowsMatrix A := (decOK_sound (decA_leaf h)).2
  have hSB : pkMat D.ThSeed_SB = rowsMatrix B :=
    (decOK_sound (segPre_true h 2 (by rw [segPre_length]; decide) : CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB = true)).2
  have hmul : ∀ {P Q : ℕ} {X Y : Array V4}, pkMat P = rowsMatrix X → pkMat Q = rowsMatrix Y →
      pkMat (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P Q) = rowsMatrix (Native.mulRows X Y) := by
    intro P Q X Y hP hQ
    rw [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  have hpow : ∀ {P : ℕ} {X : Array V4} (e nb : ℕ), e < 2 ^ nb → pkMat P = rowsMatrix X →
      pkMat (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE P e nb) = rowsMatrix (powRows X e) := by
    intro P X e nb he hP
    rw [pkMat_powB hk _ _ _ he, hP, rowsMatrix_powRows]
  have tr : ∀ {P E : ℕ} {X : Array V4}, CFSG.KC.Th.Gen.eqN P E = true → pkMat E = rowsMatrix X →
      pkMat P = rowsMatrix X := fun hl hE => by rw [eq_of_eqN hl, hE]
  have r0 : pkMat (D.ThM3_RB 0) = rowsMatrix (t3 A B) :=
    tr (segPre_true h 8 (by rw [segPre_length]; decide)) (hmul hSA hSB)
  have r1 : pkMat (D.ThM3_RB 1) = rowsMatrix (t4 A B) :=
    tr (segPre_true h 9 (by rw [segPre_length]; decide)) (hmul r0 hSB)
  have r2 : pkMat (D.ThM3_RB 2) = rowsMatrix (t5 A B) :=
    tr (segPre_true h 10 (by rw [segPre_length]; decide)) (hmul r0 r1)
  have r3 : pkMat (D.ThM3_RB 3) = rowsMatrix (t6 A B) :=
    tr (segPre_true h 11 (by rw [segPre_length]; decide)) (hmul r0 r2)
  have r4 : pkMat (D.ThM3_RB 4) = rowsMatrix (t7 A B) :=
    tr (segPre_true h 12 (by rw [segPre_length]; decide)) (hmul hSA r3)
  have r5 : pkMat (D.ThM3_RB 5) = rowsMatrix (t8 A B) :=
    tr (segPre_true h 13 (by rw [segPre_length]; decide)) (hmul r3 hSA)
  have r6 : pkMat (D.ThM3_RB 6) = rowsMatrix (u A B) :=
    tr (segPre_true h 14 (by rw [segPre_length]; decide)) (hmul (hpow 2 2 (by norm_num) r5) r4)
  have r7 : pkMat (D.ThM3_RB 7) = rowsMatrix (s8 A B) :=
    tr (segPre_true h 15 (by rw [segPre_length]; decide)) (hmul r3 r2)
  have r8 : pkMat (D.ThM3_RB 8) = rowsMatrix (s9 A B) :=
    tr (segPre_true h 16 (by rw [segPre_length]; decide)) (hmul r0 r7)
  have r9 : pkMat (D.ThM3_RB 9) = rowsMatrix (s10 A B) :=
    tr (segPre_true h 17 (by rw [segPre_length]; decide)) (hmul r8 r1)
  have r10 : pkMat (D.ThM3_RB 10) = rowsMatrix (s7 A B) :=
    tr (segPre_true h 18 (by rw [segPre_length]; decide)) (hmul hSA r9)
  have r11 : pkMat (D.ThM3_RB 11) = rowsMatrix (s8' A B) :=
    tr (segPre_true h 19 (by rw [segPre_length]; decide)) (hmul r9 hSA)
  have r12 : pkMat (D.ThM3_RB 12) = rowsMatrix (v A B) :=
    tr (segPre_true h 20 (by rw [segPre_length]; decide)) (hmul (hpow 18 5 (by norm_num) r11) r10)
  have r13 : pkMat (D.ThM3_RB 13) = rowsMatrix (x A B) :=
    tr (segPre_true h 21 (by rw [segPre_length]; decide)) (hpow 14 4 (by norm_num) r12)
  have r14 : pkMat (D.ThM3_RB 14) = rowsMatrix (y A B) :=
    tr (segPre_true h 22 (by rw [segPre_length]; decide)) (hmul r4 (hpow 9 4 (by norm_num) r6))
  have r15 : pkMat (D.ThM3_RB 15) = rowsMatrix (powRows (y A B) 5) :=
    tr (segPre_true h 23 (by rw [segPre_length]; decide)) (hpow 5 3 (by norm_num) r14)
  have hw : ∀ w : List Gen, pkMat (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13)
      (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen w) w.length) = rowsMatrix (wordRows (x A B) (y A B) w) :=
    pkMat_wordAB_encGen hk r13 r14
  have hzl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 16) (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE
      (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15)
        (encGen zWord) zWord.length) zExp 4) = true := segPre_true h 24 (by rw [segPre_length]; decide)
  have r16 : pkMat (D.ThM3_RB 16) = rowsMatrix (z A B) :=
    tr hzl (hpow zExp 4 (by decide) (hw zWord))
  have lay16 : InLayout (D.ThM3_RB 16) := by rw [eq_of_eqN hzl]; exact inLayout_powB hk _ _ _
  have rq : ∀ i : Fin 8, pkMat (D.ThM3_RB (17 + i.val)) = rowsMatrix (q A B i) := by
    intro i
    rw [q_eq]
    fin_cases i
    · have hl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 17)
        (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE
          (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen (qWord 0)) (qWord 0).length)
          (qExp 0) 3) = true :=
        segPre_true h 25 (by rw [segPre_length]; decide)
      exact tr hl (hpow _ 3 (by decide) (hw _))
    · have hl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 18)
        (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE
          (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen (qWord 1)) (qWord 1).length)
          (qExp 1) 3) = true :=
        segPre_true h 26 (by rw [segPre_length]; decide)
      exact tr hl (hpow _ 3 (by decide) (hw _))
    · have hl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 19)
        (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE
          (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen (qWord 2)) (qWord 2).length)
          (qExp 2) 3) = true :=
        segPre_true h 27 (by rw [segPre_length]; decide)
      exact tr hl (hpow _ 3 (by decide) (hw _))
    · have hl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 20)
        (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE
          (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen (qWord 3)) (qWord 3).length)
          (qExp 3) 3) = true :=
        segPre_true h 28 (by rw [segPre_length]; decide)
      exact tr hl (hpow _ 3 (by decide) (hw _))
    · have hl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 21)
        (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE
          (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen (qWord 4)) (qWord 4).length)
          (qExp 4) 3) = true :=
        segPre_true h 29 (by rw [segPre_length]; decide)
      exact tr hl (hpow _ 3 (by decide) (hw _))
    · have hl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 22)
        (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE
          (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen (qWord 5)) (qWord 5).length)
          (qExp 5) 3) = true :=
        segPre_true h 30 (by rw [segPre_length]; decide)
      exact tr hl (hpow _ 3 (by decide) (hw _))
    · have hl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 23)
        (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE
          (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen (qWord 6)) (qWord 6).length)
          (qExp 6) 3) = true :=
        segPre_true h 31 (by rw [segPre_length]; decide)
      exact tr hl (hpow _ 3 (by decide) (hw _))
    · have hl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 24)
        (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE
          (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) (encGen (qWord 7)) (qWord 7).length)
          (qExp 7) 3) = true :=
        segPre_true h 32 (by rw [segPre_length]; decide)
      exact tr hl (hpow _ 3 (by decide) (hw _))
  have hdl : CFSG.KC.Th.Gen.eqN (D.ThM3_RB 547)
      (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15)
        (encGen InvRep.dWord) InvRep.dWord.length) = true :=
    segPost_true h 10 (by rw [segPost_length]; decide)
  have rd : pkMat (D.ThM3_RB 547) = rowsMatrix (d A B) := tr hdl (hw _)
  have rnf : ∀ n (hn : n < 512),
      pkMat (D.ThM3_RB (25 + n)) = rowsMatrix (nfAt A B ⟨n, hn⟩) ∧ InLayout (D.ThM3_RB (25 + n)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hc := nfReg_true h ⟨n, hn⟩
      unfold nfReg at hc
      split_ifs at hc with h0 h1
      · simp only at h0
        subst h0
        rw [eq_of_eqN hc]
        refine ⟨?_, inLayout_one hk⟩
        rw [pkMat_one hk, nfAt_eq, rowsMatrix_nf]
        simp only [Nat.zero_mod, Nat.zero_div, pow_zero, one_mul]
        exact (prod_ofFn_eq_one _ fun _ => rfl).symm
      · simp only at h1
        subst h1
        rw [eq_of_eqN hc]
        refine ⟨?_, lay16⟩
        rw [r16, nfAt_eq, rowsMatrix_nf]
        simp only [Nat.one_mod, pow_one, show ∀ i : ℕ, 1 / 2 ^ (i + 1) % 2 = 0 from fun i => by
          rw [Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))], pow_zero]
        first
          | done
          | rw [prod_ofFn_eq_one _ fun _ => rfl, mul_one]
      · simp only at h0 h1
        have h2 : 2 ≤ n := by omega
        obtain ⟨hb1, hb8, hlt, -⟩ := nfBits ⟨n, hn⟩ h2
        simp only at hb1 hb8 hlt
        have hlt' : n - 2 ^ hbit n < 512 := by omega
        obtain ⟨ihm, -⟩ := ih _ hlt hlt'
        have hm8 : hbit n - 1 < 8 := by omega
        have hq : pkMat (D.ThM3_RB (16 + hbit n)) = rowsMatrix (q A B ⟨hbit n - 1, hm8⟩) := by
          have e17 : 16 + hbit n = 17 + (hbit n - 1) := by omega
          rw [e17]
          exact rq ⟨hbit n - 1, hm8⟩
        have hreg := eq_of_eqN hc
        have hsplit := nfAt_split (A := A) (B := B) ⟨n, hn⟩ ⟨n - 2 ^ hbit n, hlt'⟩ ⟨hbit n - 1, hm8⟩
          h2 rfl rfl
        refine ⟨?_, ?_⟩
        · rw [hreg]
          exact ((pkMat_mulB hk _ _).trans (congrArg₂ (· * ·) ihm hq)).trans hsplit.symm
        · rw [hreg]
          exact inLayout_mulB hk _ _
  exact
    { lay16 := lay16
      layNf := fun k => (rnf k.val k.isLt).2
      t8 := r5
      s8' := r11
      x := r13
      y := r14
      y5 := r15
      z := r16
      q := rq
      nf := fun k => (rnf k.val k.isLt).1
      d := rd }

end CFSG.KC.Th.Max3S

end
