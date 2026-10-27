module

public import Certificates.Data.Kernel.Sz32Twin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Data

public section

namespace CFSG.KC.Sz32T

open CFSG.AGLEmbedding.KFactProofs.Sz32 CFSG.Blueprint Matrix

@[expose] def dec (x : ℕ) : F32 :=
  ⟨((x % 2 : ℕ) : ZMod 2), ((x / 2 % 2 : ℕ) : ZMod 2), ((x / 4 % 2 : ℕ) : ZMod 2),
    ((x / 8 % 2 : ℕ) : ZMod 2), ((x / 16 % 2 : ℕ) : ZMod 2)⟩

@[expose] def enc (u : F32) : ℕ :=
  u.c0.val + 2 * u.c1.val + 4 * u.c2.val + 8 * u.c3.val + 16 * u.c4.val

theorem letN_eq {α : Sort _} (x : ℕ) (f : ℕ → α) : letN x f = f x := by
  cases x <;> rfl

theorem allLt_iff {n : ℕ} {f : ℕ → Bool} : allLt n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    rw [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem dec_mod (x : ℕ) : dec (x % 32) = dec x := by
  have h1 : x % 32 % 2 = x % 2 := by omega
  have h2 : x % 32 / 2 % 2 = x / 2 % 2 := by omega
  have h3 : x % 32 / 4 % 2 = x / 4 % 2 := by omega
  have h4 : x % 32 / 8 % 2 = x / 8 % 2 := by omega
  have h5 : x % 32 / 16 % 2 = x / 16 % 2 := by omega
  simp only [dec, h1, h2, h3, h4, h5]

theorem dec_zero : dec 0 = 0 := by decide

theorem dec_one : dec 1 = 1 := by decide

theorem dec_enc : ∀ u : F32, dec (enc u) = u ∧ enc u < 32 := by decide +kernel

theorem dec_surj (u : F32) : ∃ x < 32, dec x = u := ⟨enc u, (dec_enc u).2, (dec_enc u).1⟩

theorem dec_fa_all :
    allLt 32 (fun a => allLt 32 fun b => decide (dec (fa a b) = dec a + dec b)) = true := by
  decide +kernel

theorem dec_fm_all :
    allLt 32 (fun a => allLt 32 fun b => decide (dec (fm a b) = dec a * dec b)) = true := by
  decide +kernel

theorem dec_inj_all :
    allLt 32 (fun a => allLt 32 fun b => !decide (dec a = dec b) || decide (a = b)) = true := by
  decide +kernel

theorem dec_fa (x y : ℕ) : dec (fa x y) = dec x + dec y := by
  have h : fa x y = fa (x % 32) (y % 32) := by simp only [fa, Nat.mod_mod]
  have := of_decide_eq_true (allLt_iff.1 (allLt_iff.1 dec_fa_all _ (Nat.mod_lt x (by norm_num)))
    _ (Nat.mod_lt y (by norm_num)))
  rw [h, this, dec_mod, dec_mod]

theorem dec_fm (x y : ℕ) : dec (fm x y) = dec x * dec y := by
  have h : fm x y = fm (x % 32) (y % 32) := by simp only [fm, Nat.mod_mod]
  have := of_decide_eq_true (allLt_iff.1 (allLt_iff.1 dec_fm_all _ (Nat.mod_lt x (by norm_num)))
    _ (Nat.mod_lt y (by norm_num)))
  rw [h, this, dec_mod, dec_mod]

theorem dec_eq_iff (x y : ℕ) : dec x = dec y ↔ x % 32 = y % 32 := by
  constructor
  · intro h
    rw [← dec_mod x, ← dec_mod y] at h
    have := allLt_iff.1 (allLt_iff.1 dec_inj_all _ (Nat.mod_lt x (by norm_num))) _
      (Nat.mod_lt y (by norm_num))
    simpa [h] using this
  · intro h
    rw [← dec_mod x, h, dec_mod]

theorem eq32_iff (x y : ℕ) : eq32 x y = true ↔ dec x = dec y := by
  rw [dec_eq_iff]
  simp [eq32]

theorem dec_eq_zero_iff (y : ℕ) : dec y = 0 ↔ y % 32 = 0 := by
  rw [← dec_zero, dec_eq_iff]

theorem dec_fpow (x n : ℕ) : dec (fpow x n) = dec x ^ n := by
  induction n with
  | zero => exact dec_one
  | succ n ih => rw [fpow, dec_fm, ih, pow_succ]

theorem ent_packL (l : List ℕ) (i : ℕ) : ent (packL l) i = l.getD i 0 % 32 := by
  induction l generalizing i with
  | nil => simp [ent, packL]
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [ent, packL, pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    | succ i =>
      have h : (a % 32 + 32 * packL l) / 32 ^ (i + 1) = packL l / 32 ^ i := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      have := ih i
      simp only [ent] at this
      simp only [ent, packL, h, List.getD_cons_succ, this]

@[expose] def decV (v : ℕ) : Vec := fun i => dec (ent v i)

@[expose] def decM (M : ℕ) : Mat := Matrix.of fun i j => dec (ent M (4 * i.val + j.val))

theorem decV_mv (A v : ℕ) : decV (mv A v) = decM A *ᵥ decV v := by
  funext i
  fin_cases i <;>
    simp [decV, decM, mv, letN_eq, mvE, ent_packL, dec_mod, dec_fa, dec_fm, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

theorem decM_mm (A B : ℕ) : decM (mm A B) = decM A * decM B := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [decM, mm, letN_eq, mmE, ent_packL, dec_mod, dec_fa, dec_fm, Matrix.mul_apply, Fin.sum_univ_four]

theorem decM_polyG (I T1 T2 T3 c : ℕ) :
    decM (polyG I T1 T2 T3 c) =
      decV c 0 • decM I + decV c 1 • decM T1 + decV c 2 • decM T2 + decV c 3 • decM T3 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [decM, decV, polyG, letN_eq, polyE, ent_packL, dec_mod, dec_fa, dec_fm]

theorem decM_idN : decM idN = 1 := by decide +kernel

theorem decM_g0N : decM g0N = g0Mat := by
  rw [← toMat_g0A]
  decide +kernel

theorem decM_t1N : decM t1N = t0Mat := by decide +kernel

theorem decM_t2N : decM t2N = t0Mat2 := by decide +kernel

theorem decM_t3N : decM t3N = t0Mat3 := by decide +kernel

theorem decM_bInvN : decM bInvN = bInv := by decide +kernel

theorem decV_paN : decV paN = lineVec 1 0 := by decide +kernel

theorem decV_pbN : decV pbN = lineVec omega 0 := by decide +kernel

theorem decV_inftyW : decV inftyW = inftyVec := by decide +kernel

theorem decM_gAt (hc : chainOk = true) {k : ℕ} (hk : k < 25) : decM (gAt k) = g0Mat ^ k := by
  rw [chainOk, Bool.and_eq_true, allLt_iff] at hc
  induction k with
  | zero => rw [Nat.eq_of_beq_eq_true hc.1, decM_idN, pow_zero]
  | succ k ih =>
    rw [Nat.eq_of_beq_eq_true (hc.2 k (by omega)), decM_mm, ih (by omega), decM_g0N, pow_succ]

theorem dec_nT (x y : ℕ) : dec (nT x y) = suzukiN 2 (dec x) (dec y) := by
  simp [nT, dec_fa, dec_fm, dec_fpow, suzukiN]

theorem decV_lineW (x y : ℕ) : decV (lineW x y) = lineVec (dec x) (dec y) := by
  funext i
  fin_cases i <;> simp [decV, lineW, ent_packL, dec_mod, lineVec, dec_one, dec_nT]

@[expose] def Pw (w : Vec) : Mat :=
  polyMat ((bInv *ᵥ w) 0) ((bInv *ᵥ w) 1) ((bInv *ᵥ w) 2) ((bInv *ᵥ w) 3)

theorem decM_polyT (w : ℕ) : decM (polyT w) = Pw (decV w) := by
  simp only [polyT, decM_polyG, decV_mv, decM_bInvN, decM_idN, decM_t1N, decM_t2N, decM_t3N, Pw,
    polyMat_eq]

theorem onB_of {y0 y1 y2 y3 : ℕ} (h : OnOmega4 2 (dec y0) (dec y1) (dec y2) (dec y3)) :
    onB y0 y1 y2 y3 = true := by
  unfold onB
  rcases h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h⟩
  · rw [dec_eq_zero_iff] at h0 h1 h2
    have h3' : ¬ y3 % 32 = 0 := fun e => h3 ((dec_eq_zero_iff y3).2 e)
    simp [h0, h1, h2, h3']
  · have h0' : ¬ y0 % 32 = 0 := fun e => h0 ((dec_eq_zero_iff y0).2 e)
    rw [if_neg h0', eq32_iff]
    simp only [dec_fm, dec_fa, dec_fpow]
    norm_num at h
    linear_combination h

theorem onV_of {y : ℕ} (h : OnOmegaGen 2 (decV y)) : onV y = true := by
  rw [onV, letN_eq]
  exact onB_of h

theorem smulEq_sound {P l G : ℕ} (h : smulEq P l G = true) : decM P = dec l • decM G := by
  rw [smulEq, letN_eq, letN_eq, letN_eq] at h
  have h' := allLt_iff.1 h
  refine Matrix.ext fun i j => ?_
  have hi := i.isLt
  have hj := j.isLt
  have := (eq32_iff _ _).1 (h' (4 * i.val + j.val) (by omega))
  simp only [decM, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [this, dec_fm]

theorem wOk_sound (hc : chainOk = true) {w : ℕ} {kl : ℕ × ℕ} (h : wOk w kl = true)
    (ha : OnOmegaGen 2 (Pw (decV w) *ᵥ lineVec 1 0))
    (hb : OnOmegaGen 2 (Pw (decV w) *ᵥ lineVec omega 0)) :
    ∃ k < 25, ∃ l : F32, Pw (decV w) = l • g0Mat ^ k := by
  have hP := decM_polyT w
  have ha' : onV (mv (polyT w) paN) = true := onV_of (by rw [decV_mv, hP, decV_paN]; exact ha)
  have hb' : onV (mv (polyT w) pbN) = true := onV_of (by rw [decV_mv, hP, decV_pbN]; exact hb)
  simp only [wOk, letN_eq, wOkP, ha', hb', Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Nat.blt_eq] at h
  obtain ⟨hk, hs⟩ := h
  refine ⟨kl.1, hk, dec kl.2, ?_⟩
  rw [← hP, smulEq_sound hs, decM_gAt hc hk]

end CFSG.KC.Sz32T

end
