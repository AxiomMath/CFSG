module

public import CFSG.Certificates.Kernel.U35Pk.Layout
public import CFSG.Quasithin.Vol2.KGFactAutSylowU35Syl

public section

namespace CFSG.Certificates.U35Pk

open CFSG.RankThree.PartOne.HNB Matrix
open CFSG.Quasithin.H13.KGAutSyl.U35Syl (Rm Sm)

set_option exponentiation.threshold 2100

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : U35Pk.strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : U35Pk.strictB y k = k y := by
  cases y <;> rfl

theorem LOW_eq : U35Pk.LOW = 2 ^ 2048 - 1 := by decide +kernel

theorem M0d_eq : U35Pk.M0d = M0 + 2 ^ 1024 * M0 := by unfold M0; decide +kernel

theorem M1d_eq : U35Pk.M1d = M1 + 2 ^ 1024 * M1 := by unfold M1; decide +kernel

theorem M2d_eq : U35Pk.M2d = M2 + 2 ^ 1024 * M2 := by unfold M2; decide +kernel

theorem LMd_eq : U35Pk.LMd = LANE + 2 ^ 1024 * LANE := by
  unfold LANE
  simp only [ev_succ, ev_zero]
  decide +kernel

theorem DIAG_eq : U35Pk.DIAG = 2 ^ 36 + 2 ^ 72 + 2 ^ 108 := by decide +kernel

theorem mulAB_eq (a b : ℕ) : U35Pk.mulAB a b = mulP a b := by
  unfold U35Pk.mulAB U35Pk.red
  rw [strictN_eq, strictN_eq, strictN_eq]
  have e1 : ∀ y : ℕ, Nat.land y U35Pk.LOW = y % 2 ^ 2048 := fun y => by
    rw [LOW_eq]
    exact Nat.and_two_pow_sub_one_eq_mod y 2048
  have e2 : ∀ y : ℕ, Nat.shiftLeft (Nat.shiftRight y 2048) 1 = 2 * (y / 2 ^ 2048) := fun y => by
    change (y >>> 2048) <<< 1 = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    ring
  have e3 : ∀ z s : ℕ, Nat.shiftRight z s = z / 2 ^ s := fun z s => Nat.shiftRight_eq_div_pow z s
  rw [e1, e2, e3, e3, e3, M0d_eq, M1d_eq, M2d_eq, LMd_eq]
  rfl

theorem mulAB_enc (X Y : Matrix (Fin 3) (Fin 3) F25) :
    U35Pk.mulAB (encA X) (encB Y) = encB (X * Y) := by
  rw [mulAB_eq, mulP_enc]

theorem re_zero : re 0 = 0 := rfl

theorem im_zero : im 0 = 0 := rfl

theorem encB_smul_one (c : F25) :
    encB (c • (1 : Matrix (Fin 3) (Fin 3) F25)) = (re c + 2 ^ 1024 * im c) * (2 ^ 36 + 2 ^ 72 + 2 ^ 108) := by
  unfold encB
  rw [packB_eq, packB_eq]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Fin.isValue, Fin.reduceEq, if_true, if_false, re_zero, im_zero]
  ring

theorem encB_lo_div (X : Matrix (Fin 3) (Fin 3) F25) :
    encB X / 2 ^ 36 % 2 ^ 8 = re (X 2 2) := by
  have hlo : packB (fun r j => re (X r j)) < 2 ^ 162 := packB_lt fun r j => lt18_of_lt5 (re_lt _)
  have e : encB X = packB (fun r j => re (X r j)) + 2 ^ 36 * (2 ^ 988 * packB fun r j => im (X r j)) := by
    unfold encB
    ring
  have e2 : packB (fun r j => re (X r j)) / 2 ^ 36 % 2 ^ 8 = re (X 2 2) := by
    unfold packB
    have h36 : (2 : ℕ) ^ 36 = 2 ^ (18 * 2) := by norm_num
    rw [h36, ev_div (fun m _ => lanesB_lt (fun r j => lt18_of_lt5 (re_lt (X r j))) (by norm_num) m)
      (by norm_num)]
    simp only [ev_succ, lanesB, List.getD_cons_succ, List.getD_cons_zero]
    have e3 : ∀ a b : ℕ, (a + 2 ^ 18 * b) % 2 ^ 8 = a % 2 ^ 8 := fun a b => by
      have : 2 ^ 18 * b = 2 ^ 8 * (2 ^ 10 * b) := by ring
      rw [this, Nat.add_mul_mod_self_left]
    rw [e3, Nat.mod_eq_of_lt (lt_trans (re_lt _) (by norm_num))]
  rw [e, Nat.add_mul_div_left _ _ (by positivity)]
  have : 2 ^ 988 * packB (fun r j => im (X r j)) = 2 ^ 8 * (2 ^ 980 * packB fun r j => im (X r j)) := by
    ring
  rw [this, Nat.add_mul_mod_self_left, e2]

theorem encB_hi_div (X : Matrix (Fin 3) (Fin 3) F25) :
    encB X / 2 ^ 1060 % 2 ^ 8 = im (X 2 2) := by
  have h : encB X / 2 ^ 1060 = encB X / 2 ^ 1024 / 2 ^ 36 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [h, (encB_split X).2]
  have e := encB_lo_div (fun r j => ((X r j : ZMod 5 × ZMod 5).2, (0 : ZMod 5)) : Matrix (Fin 3) (Fin 3) F25)
  unfold encB at e
  have h0 : ∀ x : F25, im ((((x : ZMod 5 × ZMod 5).2, (0 : ZMod 5)) : ZMod 5 × ZMod 5) : F25) = 0 :=
    fun _ => rfl
  simp only [h0] at e
  have hz : packB (fun _ _ => 0) = 0 := by unfold packB lanesB; simp [ev]
  rw [hz, Nat.mul_zero, Nat.add_zero] at e
  exact e

theorem isScal_enc (X : Matrix (Fin 3) (Fin 3) F25) :
    U35Pk.isScal (encB X) = true ↔ ∃ c : F25, X = c • 1 := by
  have h1 : Nat.land (Nat.shiftRight (encB X) 36) 255 = re (X 2 2) := by
    rw [← encB_lo_div]
    exact (Nat.and_two_pow_sub_one_eq_mod _ 8).trans
      (congrArg (· % 2 ^ 8) (Nat.shiftRight_eq_div_pow _ _))
  have h2 : Nat.land (Nat.shiftRight (encB X) 1060) 255 = im (X 2 2) := by
    rw [← encB_hi_div]
    exact (Nat.and_two_pow_sub_one_eq_mod _ 8).trans
      (congrArg (· % 2 ^ 8) (Nat.shiftRight_eq_div_pow _ _))
  have h3 : Nat.lor (re (X 2 2)) (Nat.shiftLeft (im (X 2 2)) 1024) = re (X 2 2) + 2 ^ 1024 * im (X 2 2) := by
    change re (X 2 2) ||| im (X 2 2) <<< 1024 = _
    rw [Nat.shiftLeft_eq, Nat.lor_comm, Nat.mul_comm,
      ← Nat.two_pow_add_eq_or_of_lt (lt_trans (re_lt _) (by norm_num))]
    exact Nat.add_comm _ _
  have h4 : Nat.mul (re (X 2 2) + 2 ^ 1024 * im (X 2 2)) (2 ^ 36 + 2 ^ 72 + 2 ^ 108) =
      encB (X 2 2 • 1) := (encB_smul_one _).symm
  unfold U35Pk.isScal
  rw [h1, h2, h3, DIAG_eq, h4, Nat.beq_eq]
  constructor
  · intro h
    exact ⟨X 2 2, encB_inj h⟩
  · rintro ⟨c, rfl⟩
    simp [Matrix.smul_apply]

theorem ordK_zero (XA P j : ℕ) : U35Pk.ordK XA 0 P j = 0 := rfl

theorem ordK_succ (XA f P j : ℕ) : U35Pk.ordK XA (f + 1) P j =
    Bool.rec (motive := fun _ => ℕ) (U35Pk.strictN (U35Pk.mulAB XA P) fun P' =>
      U35Pk.ordK XA f P' (Nat.add j 1)) j (U35Pk.isScal P) := rfl

theorem ordK_succ_true {XA f P j : ℕ} (hs : U35Pk.isScal P = true) :
    U35Pk.ordK XA (f + 1) P j = j := by
  rw [ordK_succ, hs]

theorem ordK_succ_false {XA f P j : ℕ} (hs : U35Pk.isScal P = false) :
    U35Pk.ordK XA (f + 1) P j = U35Pk.ordK XA f (U35Pk.mulAB XA P) (j + 1) := by
  rw [ordK_succ, hs, strictN_eq]

theorem ordK_spec (X : Matrix (Fin 3) (Fin 3) F25) : ∀ (f j o : ℕ),
    U35Pk.ordK (encA X) f (encB (X ^ j)) j = o → o ≠ 0 →
      (∃ c : F25, X ^ o = c • 1) ∧ ∀ m, j ≤ m → m < o → ¬ ∃ c : F25, X ^ m = c • 1
  | 0, j, o, h, ho => absurd (h.symm.trans (ordK_zero _ _ _)) ho
  | f + 1, j, o, h, ho => by
    cases hs : U35Pk.isScal (encB (X ^ j)) with
    | true =>
      rw [ordK_succ_true hs] at h
      subst h
      exact ⟨(isScal_enc _).1 hs, fun m h1 h2 => absurd h2 (by omega)⟩
    | false =>
      rw [ordK_succ_false hs, mulAB_enc, ← pow_succ'] at h
      obtain ⟨h1, h2⟩ := ordK_spec X f (j + 1) o h ho
      refine ⟨h1, fun m hm1 hm2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hm1 with rfl | hm
      · intro hc
        rw [(isScal_enc _).2 hc] at hs
        exact Bool.noConfusion hs
      · exact h2 m hm hm2

theorem refK_succ (XA f Q : ℕ) : U35Pk.refK XA (f + 1) Q =
    Bool.rec (motive := fun _ => Bool) (U35Pk.strictB (U35Pk.mulAB XA Q) (U35Pk.refK XA f)) false
      (U35Pk.inT Q) := rfl

theorem refK_succ_true {XA f Q : ℕ} (hi : U35Pk.inT Q = true) : U35Pk.refK XA (f + 1) Q = false := by
  rw [refK_succ, hi]

theorem refK_succ_false {XA f Q : ℕ} (hi : U35Pk.inT Q = false) :
    U35Pk.refK XA (f + 1) Q = U35Pk.refK XA f (U35Pk.mulAB XA Q) := by
  rw [refK_succ, hi, strictB_eq]

theorem refK_spec (X : Matrix (Fin 3) (Fin 3) F25) : ∀ (o : ℕ) (Q : Matrix (Fin 3) (Fin 3) F25),
    U35Pk.refK (encA X) o (encB Q) = true → ∀ k < o, U35Pk.inT (encB (X ^ k * Q)) = false
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | o + 1, Q, h, k, hk => by
    cases hi : U35Pk.inT (encB Q) with
    | true =>
      rw [refK_succ_true hi] at h
      exact Bool.noConfusion h
    | false =>
      rw [refK_succ_false hi, mulAB_enc] at h
      rcases k with _ | k
      · rw [pow_zero, one_mul]
        exact hi
      · have := refK_spec X o (X * Q) h k (by omega)
        rwa [← mul_assoc, ← pow_succ] at this

theorem pow25 : ∀ x : F25, x ^ 25 = x := by decide +kernel

theorem unitary_block {W : Matrix (Fin 3) (Fin 3) F25} (hu : (W.map (· ^ 5))ᵀ * W = 1)
    (h02 : W 0 2 = 0) (h12 : W 1 2 = 0) (h20 : W 2 0 = 0) (h21 : W 2 1 = 0) (h22 : W 2 2 = 1) :
    ∃ a b d : F25, a ^ 5 * a + b ^ 5 * b = 1 ∧ d ^ 5 * d = 1 ∧
      W = !![a, -(d * b ^ 5), 0; b, d * a ^ 5, 0; 0, 0, 1] := by
  have e : ∀ i j, ((W.map (· ^ 5))ᵀ * W) i j = W 0 i ^ 5 * W 0 j + W 1 i ^ 5 * W 1 j + W 2 i ^ 5 * W 2 j :=
    fun i j => by simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h00 := e 0 0
  have h01 := e 0 1
  have h11 := e 1 1
  rw [hu] at h00 h01 h11
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 1), h20, h21]
    at h00 h01 h11
  set a := W 0 0
  set b := W 1 0
  set c := W 0 1
  set f := W 1 1
  have z5 : (0 : F25) ^ 5 * 0 = 0 := by ring
  rw [z5, add_zero] at h00 h01 h11
  obtain ⟨d, hd_def⟩ : ∃ d : F25, d = a * f - b * c := ⟨_, rfl⟩
  have hc : c = -(d * b ^ 5) := by
    linear_combination a * h01.symm - c * h00.symm + b ^ 5 * hd_def
  have hf : f = d * a ^ 5 := by
    linear_combination b * h01.symm - f * h00.symm - a ^ 5 * hd_def
  have hd : d ^ 5 * d = 1 := by
    have g1 : c ^ 5 = -(d ^ 5 * b) := by
      rw [hc, neg_pow, mul_pow, ← pow_mul, pow25]
      ring
    have g2 : f ^ 5 = d ^ 5 * a := by rw [hf, mul_pow, ← pow_mul, pow25]
    have := h11
    rw [g1, g2] at this
    linear_combination -this + d ^ 5 * b * hc - d ^ 5 * a * hf + d ^ 6 * h00
  refine ⟨a, b, d, h00.symm, hd, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, h22, ← hc, ← hf] <;> rfl

@[expose] def ctr (M : Matrix (Fin 3) (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25 := (M.map (· ^ 5))ᵀ

@[expose] def tHat : Set (Matrix (Fin 3) (Fin 3) F25) := {T | ∃ i < 8, ∃ e < 2, T = Rm ^ i * Sm ^ e}

@[expose] def InScT (X : Matrix (Fin 3) (Fin 3) F25) : Prop := ∃ T ∈ tHat, ∃ c : F25, X = c • T

@[expose] def decA (x : ℕ) : Matrix (Fin 3) (Fin 3) F25 := Matrix.of fun i k =>
  (((x / 2 ^ (270 * i.val + 54 * k.val) % 2 ^ 8 : ℕ) : ZMod 5),
    ((x / 2 ^ (1024 + 270 * i.val + 54 * k.val) % 2 ^ 8 : ℕ) : ZMod 5))

@[expose] noncomputable def uRep(i : Fin 16) : Matrix (Fin 3) (Fin 3) F25 := decA (U35Pk.getK U35Pk.repW i)

@[expose] noncomputable def nRep: Set (Matrix (Fin 3) (Fin 3) F25) := {s | ∃ k < 48, s = decA (U35Pk.getK U35Pk.nW k)}

structure SoundFacts {ι : Type} (U : ι → Matrix (Fin 3) (Fin 3) F25)
    (nHat : Set (Matrix (Fin 3) (Fin 3) F25)) : Prop where
  unitary_U : ∀ i, ctr (U i) * U i = 1
  n_block : ∀ s ∈ nHat, s 0 2 = 0 ∧ s 1 2 = 0 ∧ s 2 0 = 0 ∧ s 2 1 = 0 ∧ s 2 2 = 1
  n_unitary : ∀ s ∈ nHat, ctr s * s = 1
  n_norm : ∀ s ∈ nHat, ∀ T ∈ tHat, InScT (s * T * ctr s)
  cov : ∀ v : Fin 3 → F25, ∑ r, v r ^ 5 * v r = 1 →
    ∃ s ∈ nHat, ∃ i, ∃ l : F25, l ^ 6 = 1 ∧ s *ᵥ v = l • (U i)ᵀ 2
  elt : ∀ i, ∀ W : Matrix (Fin 3) (Fin 3) F25, ctr W * W = 1 → W 0 2 = 0 → W 1 2 = 0 →
    W 2 0 = 0 → W 2 1 = 0 → W 2 2 = 1 → ∃ o, 0 < o ∧ (∃ c : F25, (U i * W) ^ o = c • 1) ∧
      (∀ m, 0 < m → m < o → ¬ ∃ c : F25, (U i * W) ^ m = c • 1) ∧
      (Odd o → ((U i * W) 0 2 = 0 ∧ (U i * W) 1 2 = 0 ∧ (U i * W) 2 0 = 0 ∧
          (U i * W) 2 1 = 0 ∧ o ≠ 5) ∨
        ∃ t ∈ ({Sm, Rm, Rm ^ 2} : Set (Matrix (Fin 3) (Fin 3) F25)),
          ∀ k < o, ¬ InScT ((U i * W) ^ k * t * (U i * W)))
  t_indep : ∀ i < 8, ∀ e < 2, ∀ i' < 8, ∀ e' < 2,
    (∃ c : F25, Rm ^ i * Sm ^ e = c • (Rm ^ i' * Sm ^ e')) → i = i' ∧ e = e'
  t_center : ∀ i < 8, ∀ e < 2,
    (∃ c : F25, Rm * (Rm ^ i * Sm ^ e) = c • (Rm ^ i * Sm ^ e * Rm)) →
    (∃ c : F25, Sm * (Rm ^ i * Sm ^ e) = c • (Rm ^ i * Sm ^ e * Sm)) →
      (∃ c : F25, Rm ^ i * Sm ^ e = c • 1) ∨ ∃ c : F25, Rm ^ i * Sm ^ e = c • Rm ^ 4

@[expose] def tM (k : ℕ) : Matrix (Fin 3) (Fin 3) F25 := Rm ^ (k / 2) * Sm ^ (k % 2)

@[expose] noncomputable def tiM (k : ℕ) : Matrix (Fin 3) (Fin 3) F25 := decA (U35Pk.getK U35Pk.tinvL k)

@[expose] def lamF (x : ℕ) : F25 :=
  (((x / 2 ^ 36 % 2 ^ 8 : ℕ) : ZMod 5), ((x / 2 ^ 1060 % 2 ^ 8 : ℕ) : ZMod 5))

@[expose] def diagL (l : F25) : Matrix (Fin 3) (Fin 3) F25 := !![0, 0, 0; 0, 0, 0; 0, 0, l]

theorem lens : U35Pk.lenK U35Pk.repW = 16 ∧ U35Pk.lenK U35Pk.nW = 48 ∧
    U35Pk.lenK U35Pk.tinvL = 16 ∧ U35Pk.lenK U35Pk.tBL = 16 ∧ U35Pk.lenK U35Pk.lamL = 6 := by
  decide +kernel

theorem tBL_eq : ∀ k < 16, U35Pk.getK U35Pk.tBL k = encB (tM k) := by decide +kernel

theorem tinv_eq : ∀ k < 16, encA (tiM k) = U35Pk.getK U35Pk.tinvL k ∧ tiM k * tM k = 1 := by
  decide +kernel

theorem tM_blk : ∀ k < 16, tM k 0 2 = 0 ∧ tM k 1 2 = 0 ∧ tM k 2 0 = 0 ∧ tM k 2 1 = 0 := by
  decide +kernel

theorem consts_eq : U35Pk.RA = encA Rm ∧ U35Pk.SA = encA Sm ∧ U35Pk.R2A = encA (Rm ^ 2) := by
  decide +kernel

theorem repW_eq : ∀ k < 16, encA (decA (U35Pk.getK U35Pk.repW k)) = U35Pk.getK U35Pk.repW k ∧
    ctr (decA (U35Pk.getK U35Pk.repW k)) * decA (U35Pk.getK U35Pk.repW k) = 1 := by
  decide +kernel

theorem nW_eq : ∀ k < 48, encA (decA (U35Pk.getK U35Pk.nW k)) = U35Pk.getK U35Pk.nW k ∧
    U35Pk.trB (U35Pk.cjB (U35Pk.aToB (U35Pk.getK U35Pk.nW k))) =
      encB (ctr (decA (U35Pk.getK U35Pk.nW k))) ∧
    decA (U35Pk.getK U35Pk.nW k) 0 2 = 0 ∧ decA (U35Pk.getK U35Pk.nW k) 1 2 = 0 ∧
    decA (U35Pk.getK U35Pk.nW k) 2 0 = 0 ∧ decA (U35Pk.getK U35Pk.nW k) 2 1 = 0 ∧
    decA (U35Pk.getK U35Pk.nW k) 2 2 = 1 ∧
    ctr (decA (U35Pk.getK U35Pk.nW k)) * decA (U35Pk.getK U35Pk.nW k) = 1 := by
  decide +kernel

theorem lamL_eq : ∀ k < 6, U35Pk.getK U35Pk.lamL k = encB (diagL (lamF (U35Pk.getK U35Pk.lamL k))) ∧
    lamF (U35Pk.getK U35Pk.lamL k) ^ 6 = 1 := by
  decide +kernel

theorem look_eq : (∀ i < 48, U35Pk.lookP (U35Pk.packL U35Pk.nW) i = U35Pk.getK U35Pk.nW i) ∧
    (∀ i < 16, U35Pk.lookP (U35Pk.packL U35Pk.repW) i = U35Pk.getK U35Pk.repW i) ∧
    (∀ i < 6, U35Pk.lookP (U35Pk.packL U35Pk.lamL) i = U35Pk.getK U35Pk.lamL i) := by
  decide +kernel

@[expose] def fdec (c : ℕ) : F25 := (((c % 5 : ℕ) : ZMod 5), ((c / 5 % 5 : ℕ) : ZMod 5))

@[expose] def y0M (k : ℕ) : Matrix (Fin 3) (Fin 3) F25 :=
  !![fdec (k % 25), -(fdec (k / 25) ^ 5), 0; fdec (k / 25), fdec (k % 25) ^ 5, 0; 0, 0, 1]

@[expose] def dM (d : ℕ) : Matrix (Fin 3) (Fin 3) F25 := !![1, 0, 0; 0, fdec d, 0; 0, 0, 1]

theorem y0B_eq : U35Pk.allR (fun k => Nat.beq (U35Pk.y0B k) (encB (y0M k))) 625 0 = true := by
  decide +kernel

theorem dB_eq : ∀ d < 25, U35Pk.dB d = encB (dM d) := by decide +kernel

theorem fdec_code : ∀ x : F25, fdec (re x + 5 * im x) = x := by decide +kernel

theorem re_norm : ∀ x : F25, re (x ^ 5 * x) = (re x * re x + 3 * (im x * im x)) % 5 := by
  decide +kernel

theorem re_add (x y : F25) : re (x + y) = (re x + re y) % 5 := by
  rw [re_eq, re_eq, re_eq, fst_add, ZMod.val_add]

theorem re_one : re (1 : F25) = 1 := rfl

theorem bAnd_tt {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem bIf_tt {c t e : Bool} (h : bIf(c, t, e) = true) : (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem all_at {f : ℕ → Bool} {n : ℕ} (h : U35Pk.allR f n 0 = true) {k : ℕ} (hk : k < n) : f k = true := by
  have := allR_spec f n 0 h k hk
  rwa [Nat.zero_add] at this

theorem tM_idx {i e : ℕ} (he : e < 2) : tM (2 * i + e) = Rm ^ i * Sm ^ e := by
  have h1 : (2 * i + e) / 2 = i := by omega
  have h2 : (2 * i + e) % 2 = e := by omega
  unfold tM
  rw [h1, h2]

theorem tM_mul {k : ℕ} (hk : k < 16) : tM k * tiM k = 1 :=
  mul_eq_one_comm.1 (tinv_eq k hk).2

theorem InScT_inT {Q : Matrix (Fin 3) (Fin 3) F25} (hQ : InScT Q) : U35Pk.inT (encB Q) = true := by
  obtain ⟨T, ⟨i, hi, e, he, rfl⟩, c, rfl⟩ := hQ
  have hk : 2 * i + e < 16 := by omega
  rw [← tM_idx he]
  obtain ⟨b1, b2, b3, b4⟩ := tM_blk _ hk
  unfold U35Pk.inT
  rw [blk_of ⟨by rw [Matrix.smul_apply, b1, smul_zero], by rw [Matrix.smul_apply, b2, smul_zero],
    by rw [Matrix.smul_apply, b3, smul_zero], by rw [Matrix.smul_apply, b4, smul_zero]⟩]
  change U35Pk.anyL U35Pk.tinvL _ = true
  apply anyL_of_get _ _ (2 * i + e) (by rw [lens.2.2.1]; exact hk)
  simp only [strictB_eq]
  rw [← (tinv_eq _ hk).1, mulAB_enc]
  refine (isScal_enc _).2 ⟨c, ?_⟩
  rw [Matrix.mul_smul, (tinv_eq _ hk).2]

theorem inT_InScT {Q : Matrix (Fin 3) (Fin 3) F25} (h : U35Pk.inT (encB Q) = true) : InScT Q := by
  unfold U35Pk.inT at h
  obtain ⟨-, h'⟩ := bAnd_tt h
  obtain ⟨k, hk, hs⟩ := anyL_get _ _ h'
  rw [lens.2.2.1] at hk
  simp only [strictB_eq] at hs
  rw [← (tinv_eq _ hk).1, mulAB_enc] at hs
  obtain ⟨c, hc⟩ := (isScal_enc _).1 hs
  refine ⟨tM k, ⟨k / 2, by omega, k % 2, by omega, rfl⟩, c, ?_⟩
  calc Q = (tM k * tiM k) * Q := by rw [tM_mul hk, one_mul]
    _ = tM k * (tiM k * Q) := by rw [mul_assoc]
    _ = c • tM k := by rw [hc, Matrix.mul_smul, mul_one]

theorem refute_of {X t : Matrix (Fin 3) (Fin 3) F25} {tA o : ℕ} (htA : tA = encA t)
    (hr : U35Pk.refK (encA X) o (U35Pk.mulAB tA (encB X)) = true) :
    ∀ k < o, ¬ InScT (X ^ k * t * X) := by
  rw [htA, mulAB_enc] at hr
  intro k hk hin
  have h1 := refK_spec X o (t * X) hr k hk
  rw [← mul_assoc, InScT_inT hin] at h1
  exact Bool.noConfusion h1

theorem eltK_spec (X : Matrix (Fin 3) (Fin 3) F25) (h : U35Pk.eltK (encB X) = true) :
    ∃ o, 0 < o ∧ (∃ c : F25, X ^ o = c • 1) ∧ (∀ m, 0 < m → m < o → ¬ ∃ c : F25, X ^ m = c • 1) ∧
      (Odd o → (X 0 2 = 0 ∧ X 1 2 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 ∧ o ≠ 5) ∨
        ∃ t ∈ ({Sm, Rm, Rm ^ 2} : Set (Matrix (Fin 3) (Fin 3) F25)),
          ∀ k < o, ¬ InScT (X ^ k * t * X)) := by
  unfold U35Pk.eltK at h
  simp only [strictB_eq, bToA_enc] at h
  generalize ho : U35Pk.ordK (encA X) 40 (encB X) 1 = o at h
  obtain ⟨ha, hb⟩ := bAnd_tt h
  have ho0 : o ≠ 0 := by
    rintro rfl
    exact Bool.false_ne_true ha
  obtain ⟨hsc, hmin⟩ := ordK_spec X 40 1 o (by rw [pow_one]; exact ho) ho0
  refine ⟨o, Nat.pos_of_ne_zero ho0, hsc, fun m hm1 hm2 => hmin m hm1 hm2, fun hodd => ?_⟩
  rcases bIf_tt hb with ⟨hev, -⟩ | ⟨-, hb2⟩
  · have h1 := Nat.odd_iff.1 hodd
    have h2 : o % 2 = 0 := (Nat.and_one_is_mod o).symm.trans (Nat.eq_of_beq_eq_true hev)
    omega
  rcases bIf_tt hb2 with ⟨hbk, -⟩ | ⟨-, hc⟩
  · obtain ⟨hblk, h5⟩ := bAnd_tt hbk
    obtain ⟨z1, z2, z3, z4⟩ := isBlk_enc hblk
    refine Or.inl ⟨z1, z2, z3, z4, ?_⟩
    rintro rfl
    exact Bool.false_ne_true h5
  right
  rcases bIf_tt hc with ⟨hS, -⟩ | ⟨-, hc2⟩
  · exact ⟨Sm, by simp, refute_of consts_eq.2.1 hS⟩
  rcases bIf_tt hc2 with ⟨hR, -⟩ | ⟨-, hR2⟩
  · exact ⟨Rm, by simp, refute_of consts_eq.1 hR⟩
  · exact ⟨Rm ^ 2, by simp, refute_of consts_eq.2.2 hR2⟩

theorem nrm2_of {a b : F25} (h : a ^ 5 * a + b ^ 5 * b = 1) :
    U35Pk.nrm2 (re a + 5 * im a + 25 * (re b + 5 * im b)) = true := by
  have hr := congrArg re h
  rw [re_add, re_norm, re_norm, re_one] at hr
  have := re_lt a
  have := im_lt a
  have := re_lt b
  have := im_lt b
  have d1 : (re a + 5 * im a + 25 * (re b + 5 * im b)) % 5 = re a := by omega
  have d2 : (re a + 5 * im a + 25 * (re b + 5 * im b)) / 5 % 5 = im a := by omega
  have d3 : (re a + 5 * im a + 25 * (re b + 5 * im b)) / 25 % 5 = re b := by omega
  have d4 : (re a + 5 * im a + 25 * (re b + 5 * im b)) / 125 % 5 = im b := by omega
  unfold U35Pk.nrm2
  change Nat.beq ((_ % 5 * (_ % 5) + 3 * (_ / 5 % 5 * (_ / 5 % 5)) +
    (_ / 25 % 5 * (_ / 25 % 5) + 3 * (_ / 125 % 5 * (_ / 125 % 5)))) % 5) 1 = true
  rw [d1, d2, d3, d4, Nat.beq_eq]
  generalize re a * re a + 3 * (im a * im a) = A at hr ⊢
  generalize re b * re b + 3 * (im b * im b) = B at hr ⊢
  omega

theorem nrm1_of {d : F25} (h : d ^ 5 * d = 1) : U35Pk.nrm1 (re d + 5 * im d) = true := by
  have hr := congrArg re h
  rw [re_norm, re_one] at hr
  have := re_lt d
  have := im_lt d
  have d1 : (re d + 5 * im d) % 5 = re d := by omega
  have d2 : (re d + 5 * im d) / 5 = im d := by omega
  unfold U35Pk.nrm1
  change Nat.beq ((_ % 5 * (_ % 5) + 3 * (_ / 5 * (_ / 5))) % 5) 1 = true
  rw [d1, d2, Nat.beq_eq]
  exact hr

@[expose] def vcode (w : Fin 3 → F25) : ℕ :=
  re (w 0) + 5 * im (w 0) + 25 * (re (w 1) + 5 * im (w 1)) + 625 * (re (w 2) + 5 * im (w 2))

@[expose] def vM (w : Fin 3 → F25) : Matrix (Fin 3) (Fin 3) F25 := !![0, 0, w 0; 0, 0, w 1; 0, 0, w 2]

theorem vcode_digits (w : Fin 3 → F25) :
    vcode w % 5 = re (w 0) ∧ vcode w / 5 % 5 = im (w 0) ∧ vcode w / 25 % 5 = re (w 1) ∧
      vcode w / 125 % 5 = im (w 1) ∧ vcode w / 625 % 5 = re (w 2) ∧ vcode w / 3125 % 5 = im (w 2) ∧
      vcode w < 15625 := by
  have := re_lt (w 0)
  have := im_lt (w 0)
  have := re_lt (w 1)
  have := im_lt (w 1)
  have := re_lt (w 2)
  have := im_lt (w 2)
  unfold vcode
  omega

theorem nrmV_of {w : Fin 3 → F25} (hw : ∑ r, w r ^ 5 * w r = 1) : U35Pk.nrmV (vcode w) = true := by
  have hr := congrArg re hw
  rw [Fin.sum_univ_three, re_add, re_add, re_norm, re_norm, re_norm, re_one] at hr
  obtain ⟨d1, d2, d3, d4, d5, d6, -⟩ := vcode_digits w
  unfold U35Pk.nrmV
  change Nat.beq ((_ % 5 * (_ % 5) + 3 * (_ / 5 % 5 * (_ / 5 % 5)) +
    ((_ / 25 % 5 * (_ / 25 % 5) + 3 * (_ / 125 % 5 * (_ / 125 % 5))) +
      (_ / 625 % 5 * (_ / 625 % 5) + 3 * (_ / 3125 % 5 * (_ / 3125 % 5))))) % 5) 1 = true
  rw [d1, d2, d3, d4, d5, d6, Nat.beq_eq]
  generalize re (w 0) * re (w 0) + 3 * (im (w 0) * im (w 0)) = A at hr ⊢
  generalize re (w 1) * re (w 1) + 3 * (im (w 1) * im (w 1)) = B at hr ⊢
  generalize re (w 2) * re (w 2) + 3 * (im (w 2) * im (w 2)) = C at hr ⊢
  omega

theorem ent_eq (a b p : ℕ) : U35Pk.ent a b p = 2 ^ p * a + 2 ^ 1024 * (2 ^ p * b) := by
  unfold U35Pk.ent
  change a <<< p + b <<< (p + 1024) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.pow_add]
  ring

theorem vB_code (w : Fin 3 → F25) : U35Pk.vB (vcode w) = encB (vM w) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, -⟩ := vcode_digits w
  unfold U35Pk.vB
  change U35Pk.ent (vcode w % 5) (vcode w / 5 % 5) 144 + U35Pk.ent (vcode w / 25 % 5) (vcode w / 125 % 5) 90 +
    U35Pk.ent (vcode w / 625 % 5) (vcode w / 3125 % 5) 36 = _
  rw [d1, d2, d3, d4, d5, d6, ent_eq, ent_eq, ent_eq]
  unfold encB
  rw [packB_eq, packB_eq]
  simp [vM, re_zero, im_zero]
  ring

theorem col_eq {s U : Matrix (Fin 3) (Fin 3) F25} {w : Fin 3 → F25} {l : F25}
    (h : s * vM w = U * diagL l) : s *ᵥ w = l • (U)ᵀ 2 := by
  funext r
  have := congrFun (congrFun h r) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, vM, diagL] at this
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  linear_combination this

theorem covR_spec (NP UP LP : ℕ) : ∀ (n k : ℕ) (L : List ℕ), U35Pk.covR NP UP LP n k L = true →
    ∀ v, k ≤ v → v < k + n → U35Pk.nrmV v = true → ∃ e, U35Pk.entOK NP UP LP e v = true
  | 0, k, _, _, v, h1, h2, _ => absurd h2 (by omega)
  | n + 1, k, L, h, v, hv1, hv2, hnv => by
    rw [U35Pk.covR_succ] at h
    rcases bIf_tt h with ⟨hk, h⟩ | ⟨hk, h⟩
    · cases L with
      | nil => exact absurd h Bool.false_ne_true
      | cons e t =>
        obtain ⟨he, ht⟩ := bAnd_tt h
        rcases Nat.eq_or_lt_of_le hv1 with rfl | hlt
        · exact ⟨e, he⟩
        · exact covR_spec NP UP LP n (k + 1) t ht v (by omega) (by omega) hnv
    · have hvk : v ≠ k := by
        rintro rfl
        rw [hk] at hnv
        exact Bool.false_ne_true hnv
      exact covR_spec NP UP LP n (k + 1) L h v (by omega) (by omega) hnv

theorem y0M_dM {a b d : F25} :
    y0M (re a + 5 * im a + 25 * (re b + 5 * im b)) * dM (re d + 5 * im d) =
      !![a, -(d * b ^ 5), 0; b, d * a ^ 5, 0; 0, 0, 1] := by
  have := re_lt a
  have := im_lt a
  have := re_lt b
  have := im_lt b
  have e1 : (re a + 5 * im a + 25 * (re b + 5 * im b)) % 25 = re a + 5 * im a := by omega
  have e2 : (re a + 5 * im a + 25 * (re b + 5 * im b)) / 25 = re b + 5 * im b := by omega
  unfold y0M dM
  rw [e1, e2, fdec_code, fdec_code, fdec_code]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem check_parts (h : U35Pk.u35PkCheck = true) :
    U35Pk.allL U35Pk.nW U35Pk.nChk = true ∧
    U35Pk.allR (fun j => U35Pk.allR (U35Pk.tSepK j) 16 0) 16 0 = true ∧
    U35Pk.allR (fun k => bIf(bAnd(U35Pk.comK k (U35Pk.getK U35Pk.tinvL 2) (U35Pk.getK U35Pk.tBL 2),
      U35Pk.comK k (U35Pk.getK U35Pk.tinvL 1) (U35Pk.getK U35Pk.tBL 1)),
        bIf(Nat.beq k 0, true, Nat.beq k 8), true)) 16 0 = true ∧
    U35Pk.covK = true ∧ U35Pk.allL U35Pk.repW U35Pk.gu2K = true := by
  unfold U35Pk.u35PkCheck U35Pk.nOK U35Pk.t0K at h
  revert h
  generalize U35Pk.constsOK = c1
  generalize U35Pk.repsOK = c2
  generalize U35Pk.lamOK = c3
  generalize U35Pk.covK = c4
  generalize U35Pk.allL U35Pk.repW U35Pk.gu2K = c5
  generalize U35Pk.allL U35Pk.nW U35Pk.nChk = c6
  generalize Nat.beq (U35Pk.lenK U35Pk.nW) 48 = c7
  generalize U35Pk.allR (fun j => U35Pk.allR (U35Pk.tSepK j) 16 0) 16 0 = c8
  generalize U35Pk.allR (fun k => bIf(bAnd(U35Pk.comK k (U35Pk.getK U35Pk.tinvL 2) (U35Pk.getK U35Pk.tBL 2),
      U35Pk.comK k (U35Pk.getK U35Pk.tinvL 1) (U35Pk.getK U35Pk.tBL 1)),
        bIf(Nat.beq k 0, true, Nat.beq k 8), true)) 16 0 = c9
  generalize Nat.beq (U35Pk.lenK U35Pk.tBL) 16 = d1
  generalize Nat.beq (U35Pk.lenK U35Pk.tinvL) 16 = d2
  generalize Nat.beq (U35Pk.getK U35Pk.tBL 0) U35Pk.DIAG = d3
  generalize U35Pk.allR U35Pk.tChain 8 0 = d4
  generalize U35Pk.allR U35Pk.tInvK 16 0 = d5
  generalize Nat.beq U35Pk.R2A (U35Pk.bToA (U35Pk.getK U35Pk.tBL 4)) = d6
  revert c1 c2 c3 c4 c5 c6 c7 c8 c9 d1 d2 d3 d4 d5 d6
  decide +kernel

theorem u35Pk_sound (h : U35Pk.u35PkCheck = true) : SoundFacts uRep nRep := by
  obtain ⟨hnall, hsep, hcen, hcov, hgu2⟩ := check_parts h
  refine ⟨fun i => (repW_eq i i.2).2, fun s ⟨k, hk, hs⟩ => ?_, fun s ⟨k, hk, hs⟩ => ?_,
    fun s ⟨k, hk, hs⟩ T hT => ?_, fun w hw => ?_, fun i W hu h02 h12 h20 h21 h22 => ?_,
    fun i hi e he i' hi' e' he' hc => ?_, fun i hi e he hR hS => ?_⟩
  ·
    subst hs
    obtain ⟨-, -, b1, b2, b3, b4, b5, -⟩ := nW_eq k hk
    exact ⟨b1, b2, b3, b4, b5⟩
  ·
    subst hs
    exact (nW_eq k hk).2.2.2.2.2.2.2
  ·
    subst hs
    obtain ⟨i, hi, e, he, rfl⟩ := hT
    have hj : 2 * i + e < 16 := by omega
    have hn := allL_get _ _ hnall k (by rw [lens.2.1]; exact hk)
    unfold U35Pk.nChk at hn
    obtain ⟨-, hn⟩ := bAnd_tt hn
    obtain ⟨-, hn⟩ := bAnd_tt hn
    simp only [strictB_eq] at hn
    obtain ⟨-, hn⟩ := bAnd_tt hn
    obtain ⟨-, hn⟩ := bAnd_tt hn
    have h1 := allL_get _ _ hn (2 * i + e) (by rw [lens.2.2.2.1]; exact hj)
    obtain ⟨hx, hB, -⟩ := nW_eq k hk
    set s := decA (U35Pk.getK U35Pk.nW k) with hs_def
    rw [hB, tBL_eq _ hj, ← hx, mulAB_enc, bToA_enc, mulAB_enc, tM_idx he] at h1
    exact inT_InScT h1
  ·
    obtain ⟨-, -, -, -, -, -, hv⟩ := vcode_digits w
    unfold U35Pk.covK at hcov
    rw [U35Pk.covC_eq] at hcov
    obtain ⟨e, he⟩ := covR_spec _ _ _ 15625 0 U35Pk.covW hcov (vcode w) (Nat.zero_le _) (by omega)
      (nrmV_of hw)
    unfold U35Pk.entOK at he
    obtain ⟨he1, he2⟩ := bAnd_tt he
    have he3 : e < 4608 := Nat.le_of_ble_eq_true he1
    have he4 : U35Pk.mulAB (U35Pk.lookP (U35Pk.packL U35Pk.nW) (e / 96)) (U35Pk.vB (vcode w)) =
        U35Pk.mulAB (U35Pk.lookP (U35Pk.packL U35Pk.repW) (e / 6 % 16))
          (U35Pk.lookP (U35Pk.packL U35Pk.lamL) (e % 6)) := Nat.eq_of_beq_eq_true he2
    have hs : e / 96 < 48 := by omega
    have hu : e / 6 % 16 < 16 := by omega
    have hl : e % 6 < 6 := by omega
    rw [look_eq.1 _ hs, look_eq.2.1 _ hu, look_eq.2.2 _ hl, vB_code, (lamL_eq _ hl).1,
      ← (nW_eq _ hs).1, ← (repW_eq _ hu).1, mulAB_enc, mulAB_enc] at he4
    refine ⟨decA (U35Pk.getK U35Pk.nW (e / 96)), ⟨e / 96, hs, rfl⟩, ⟨e / 6 % 16, hu⟩,
      lamF (U35Pk.getK U35Pk.lamL (e % 6)), (lamL_eq _ hl).2, col_eq (encB_inj he4)⟩
  ·
    obtain ⟨a, b, d, hab, hd, hW⟩ := unitary_block hu h02 h12 h20 h21 h22
    have hgu := allL_get _ _ hgu2 i (by rw [lens.1]; exact i.2)
    unfold U35Pk.gu2K U35Pk.gu2R at hgu
    simp only [strictB_eq] at hgu
    have := re_lt a
    have := im_lt a
    have := re_lt b
    have := im_lt b
    have := re_lt d
    have := im_lt d
    have hk : re a + 5 * im a + 25 * (re b + 5 * im b) < 625 := by omega
    have hdc : re d + 5 * im d < 25 := by omega
    have h1 := allR_spec _ 625 0 hgu _ hk
    rw [Nat.zero_add] at h1
    unfold U35Pk.gu2Step at h1
    rcases bIf_tt h1 with ⟨-, h1⟩ | ⟨hf, -⟩
    swap
    · rw [nrm2_of hab] at hf
      exact absurd hf Bool.noConfusion
    simp only [strictB_eq] at h1
    have h2 := all_at h1 hdc
    rcases bIf_tt h2 with ⟨-, h2⟩ | ⟨hf, -⟩
    swap
    · rw [nrm1_of hd] at hf
      exact absurd hf Bool.noConfusion
    have hy := Nat.eq_of_beq_eq_true (all_at y0B_eq hk)
    rw [hy, dB_eq _ hdc, ← (repW_eq _ i.2).1, mulAB_enc, bToA_enc, mulAB_enc, mul_assoc, y0M_dM,
      ← hW] at h2
    have hU : decA (U35Pk.getK U35Pk.repW i) = uRep i := rfl
    rw [hU] at h2
    exact eltK_spec _ h2
  ·
    obtain ⟨c, hc⟩ := hc
    have hj : 2 * i' + e' < 16 := by omega
    have hk : 2 * i + e < 16 := by omega
    have hs := all_at (all_at hsep hj) hk
    unfold U35Pk.tSepK at hs
    rcases bIf_tt hs with ⟨hjk, -⟩ | ⟨-, hs⟩
    · have := Nat.eq_of_beq_eq_true hjk
      omega
    simp only [strictB_eq] at hs
    rw [← (tinv_eq _ hj).1, tBL_eq _ hk, mulAB_enc,
      (isScal_enc _).2 ⟨c, by rw [tM_idx he, hc, ← tM_idx he', Matrix.mul_smul, (tinv_eq _ hj).2]⟩] at hs
    exact absurd hs Bool.false_ne_true
  ·
    have hk : 2 * i + e < 16 := by omega
    have comK_of : ∀ g < 16, (∃ c : F25, tM g * tM (2 * i + e) = c • (tM (2 * i + e) * tM g)) →
        U35Pk.comK (2 * i + e) (U35Pk.getK U35Pk.tinvL g) (U35Pk.getK U35Pk.tBL g) = true := by
      intro g hg ⟨c, hc⟩
      unfold U35Pk.comK
      simp only [strictB_eq]
      rw [tBL_eq _ hk, tBL_eq _ hg, ← (tinv_eq _ hg).1, ← (tinv_eq _ hk).1, bToA_enc, mulAB_enc,
        mulAB_enc, mulAB_enc]
      apply (isScal_enc _).2
      have e1 : c • (tiM (2 * i + e) * (tiM g * (tM (2 * i + e) * tM g))) = 1 := by
        rw [← Matrix.mul_smul, ← Matrix.mul_smul, ← hc, ← mul_assoc (tiM g), (tinv_eq _ hg).2,
          one_mul, (tinv_eq _ hk).2]
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at e1
        exact zero_ne_one e1
      refine ⟨c⁻¹, ?_⟩
      rw [← e1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have t2 : tM 2 = Rm := by simp [tM]
    have t1 : tM 1 = Sm := by simp [tM]
    have hc := all_at hcen hk
    rw [comK_of 2 (by norm_num) (by rw [t2, tM_idx he]; exact hR),
      comK_of 1 (by norm_num) (by rw [t1, tM_idx he]; exact hS)] at hc
    change bIf(Nat.beq (2 * i + e) 0, true, Nat.beq (2 * i + e) 8) = true at hc
    rcases bIf_tt hc with ⟨h0, -⟩ | ⟨-, h8⟩
    · have := Nat.eq_of_beq_eq_true h0
      have hi0 : i = 0 := by omega
      have he0 : e = 0 := by omega
      subst hi0 he0
      exact Or.inl ⟨1, by simp⟩
    · have := Nat.eq_of_beq_eq_true h8
      have hi0 : i = 4 := by omega
      have he0 : e = 0 := by omega
      subst hi0 he0
      exact Or.inr ⟨1, by simp⟩

end CFSG.Certificates.U35Pk
