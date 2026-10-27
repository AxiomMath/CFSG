module

public import CFSG.Certificates.Kernel.LocalQTR9ConjSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadListCheck

public section

namespace CFSG.KC.LQT.R

open CFSG.QuasithinUnique.Unc25K1 CFSG.QuasithinUnique.Unc25L33 CFSG.KC.Ord

@[expose] noncomputable def dec (n : ℕ) : R9 := ⟨(ent n 0 : ZMod 3), (ent n 1 : ZMod 3), (ent n 2 : ZMod 3),
  (ent n 3 : ZMod 3), (ent n 4 : ZMod 3), (ent n 5 : ZMod 3), (ent n 6 : ZMod 3),
  (ent n 7 : ZMod 3), (ent n 8 : ZMod 3)⟩

theorem dec_codeR (x : R9) : dec (codeR x) = x := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := x
  simp only [dec, ent0, ent1, ent2, ent3, ent4, ent5, ent6, ent7, ent8, ZMod.natCast_zmod_val]

theorem codeR_dec_of_slOK {n : ℕ} (h : slOK n = true) : codeR (dec n) = n ∧ rdet (dec n) = 1 := by
  obtain ⟨x, rfl, hx⟩ := exists_of_slOK h
  rw [dec_codeR]
  exact ⟨rfl, hx⟩

theorem v3n (a b c d e f : ℕ) :
    (a * d + b * e + c * f) % 3 = ((a : ZMod 3) * d + b * e + c * f).val :=
  val_of (by push_cast; rfl)

theorem m3n (a b c d : ℕ) : (a * b + 2 * (c * d)) % 3 = ((a : ZMod 3) * b - c * d).val :=
  val_of (by
    push_cast
    linear_combination ((c : ZMod 3) * d) * three_eq)

theorem mulK_dec (x y : ℕ) : mulK x y = codeR (rmul (dec x) (dec y)) := by
  rw [mulK_eq, codeR_eq]
  simp only [v3n]
  rfl

theorem cofK_dec (x : ℕ) : cofK x = codeR (rcof (dec x)) := by
  rw [cofK_eq, codeR_eq]
  simp only [minor_eq, m3n]
  rfl

theorem detK_dec (x : ℕ) : detK x = (rdet (dec x)).val := by
  rw [detK_eq]
  refine val_of ?_
  push_cast
  simp only [rdet, dec]
  linear_combination ((ent x 0 : ZMod 3) * ent x 5 * ent x 7 + (ent x 1 : ZMod 3) * ent x 3 * ent x 8 +
    (ent x 2 : ZMod 3) * ent x 4 * ent x 6) * three_eq

theorem pwK_dec (x n : ℕ) : pwK x n = codeR (rpw (dec x) n) := by
  induction n with
  | zero => exact oneK_eq
  | succ n ih =>
    change mulK x (pwK x n) = _
    rw [ih, mulK_dec, dec_codeR]
    rfl

theorem transK_cofK_dec (x : ℕ) : transK (cofK x) = codeR (adj (dec x)) := by
  rw [cofK_dec, transK_codeR]
  rfl

theorem conjK_dec (g x : ℕ) : conjK g x = codeR (rmul (rmul (dec g) (dec x)) (adj (dec g))) := by
  rw [conjK, transK_cofK_dec, mulK_dec, mulK_dec, dec_codeR, dec_codeR]

theorem commK_dec (x y : ℕ) : commK x y = true ↔ rmul (dec x) (dec y) = rmul (dec y) (dec x) := by
  rw [commK, mulK_dec, mulK_dec, beq_codeR]

theorem invoK_dec (x : ℕ) : invoK x = true ↔ x ≠ oneK ∧ rmul (dec x) (dec x) = rone := by
  rw [invoK, P.andB_iff, P.notB_iff, P.beq_iff, P.beq_iff, mulK_dec, oneK_eq, codeR_eq_iff]

theorem rpw_succ' (x : R9) (n : ℕ) : rpw x (n + 1) = rmul (rpw x n) x := by
  induction n with
  | zero => exact (rmul_one x).trans (one_rmul x).symm
  | succ n ih =>
    change rmul x (rpw x (n + 1)) = rmul (rmul x (rpw x n)) x
    rw [ih, rmul_assoc]

theorem rpw_add (x : R9) (m n : ℕ) : rpw x (m + n) = rmul (rpw x m) (rpw x n) := by
  induction m with
  | zero => rw [Nat.zero_add]; exact (one_rmul _).symm
  | succ m ih =>
    rw [Nat.succ_add]
    change rmul x (rpw x (m + n)) = rmul (rmul x (rpw x m)) (rpw x n)
    rw [ih, rmul_assoc]

theorem pwB_step (x e nb : ℕ) : ∀ k ≤ nb, e < 2 ^ nb →
    Nat.rec (motive := fun _ => ℕ) oneK
      (fun k acc => CFSG.KC.Loop.strictN (mulK acc acc) fun a2 =>
        Bool.rec (motive := fun _ => ℕ) a2 (mulK a2 x)
          (Nat.blt 0 (Nat.land e (Nat.shiftLeft 1 (Nat.sub (Nat.sub nb 1) k))))) k =
    codeR (rpw (dec x) (e / 2 ^ (nb - k)))
  | 0, _, he => by
    change oneK = _
    rw [Nat.sub_zero, Nat.div_eq_of_lt he, oneK_eq]
    rfl
  | k + 1, hk, he => by
    change CFSG.KC.Loop.strictN (mulK _ _) _ = _
    rw [pwB_step x e nb k (by omega) he, strictN_eq, mulK_dec, dec_codeR, ← rpw_add, P.bit_eq]
    have hm : nb - k = (nb - 1 - k) + 1 := by omega
    have hd : e / 2 ^ (nb - k) + e / 2 ^ (nb - k) + e / 2 ^ (nb - 1 - k) % 2 =
        e / 2 ^ (nb - (k + 1)) := by
      have e1 : nb - (k + 1) = nb - 1 - k := by omega
      rw [e1, hm, pow_succ, ← Nat.div_div_eq_div_mul]
      omega
    change Bool.rec (motive := fun _ => ℕ) _ _ (e.testBit (nb - 1 - k)) = _
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases hb : e / 2 ^ (nb - 1 - k) % 2 = 1
    · rw [decide_eq_true hb]
      change mulK _ x = _
      rw [mulK_dec, dec_codeR, ← rpw_succ', ← hd, hb]
    · rw [decide_eq_false hb]
      change codeR _ = _
      rw [← hd, show e / 2 ^ (nb - 1 - k) % 2 = 0 by omega, Nat.add_zero]

theorem pwB_dec (x e nb : ℕ) (he : e < 2 ^ nb) : pwB x e nb = codeR (rpw (dec x) e) := by
  rw [pwB, pwB_step x e nb nb le_rfl he, Nat.sub_self, pow_zero, Nat.div_one]

theorem pwB351 (x : ℕ) : pwB x 351 9 = codeR (rpw (dec x) 351) := pwB_dec x 351 9 (by norm_num)

theorem pwB16 (x : ℕ) : pwB x 16 5 = codeR (rpw (dec x) 16) := pwB_dec x 16 5 (by norm_num)

@[expose] def cjw (a b x : R9) : R9 := rmul (rmul a x) b

theorem cjw_mul {a b : R9} (hba : rmul b a = rone) (x y : R9) :
    cjw a b (rmul x y) = rmul (cjw a b x) (cjw a b y) := by
  simp only [cjw, rmul_assoc]
  rw [← rmul_assoc b a, hba, one_rmul]

theorem cjw_one {a b : R9} (hab : rmul a b = rone) : cjw a b rone = rone := by
  rw [cjw, rmul_one, hab]

theorem cjw_rpw {a b : R9} (hab : rmul a b = rone) (hba : rmul b a = rone) (x : R9) (n : ℕ) :
    cjw a b (rpw x n) = rpw (cjw a b x) n := by
  induction n with
  | zero => exact cjw_one hab
  | succ n ih =>
    change cjw a b (rmul x (rpw x n)) = rmul (cjw a b x) (rpw (cjw a b x) n)
    rw [cjw_mul hba, ih]

theorem cjw_cjw {a b : R9} (hba : rmul b a = rone) (x : R9) : cjw b a (cjw a b x) = x := by
  rw [cjw, cjw, ← rmul_assoc b (rmul a x) b, ← rmul_assoc b a x, hba, one_rmul,
    rmul_assoc x b a, hba, rmul_one]

theorem cjw_inj {a b : R9} (hba : rmul b a = rone) {x y : R9} (h : cjw a b x = cjw a b y) :
    x = y := by
  rw [← cjw_cjw hba x, h, cjw_cjw hba y]

theorem rdet_mul (x y : R9) : rdet (rmul x y) = rdet x * rdet y := by
  simp only [rdet, rmul]
  ring

theorem rdet_cjw {a b : R9} (hab : rmul a b = rone) (x : R9) : rdet (cjw a b x) = rdet x := by
  have h := congrArg rdet hab
  rw [rdet_mul, rdet_one] at h
  rw [cjw, rdet_mul, rdet_mul]
  linear_combination (rdet x) * h

theorem rdet_adj {g : R9} (hg : rdet g = 1) : rdet (adj g) = 1 := by
  have h := congrArg rdet (mul_adj hg)
  rw [rdet_mul, rdet_one, hg, one_mul] at h
  exact h

theorem inv_unique {c a b : R9} (hca : rmul c a = rone) (hbc : rmul b c = rone) : a = b := by
  rw [← one_rmul a, ← hbc, rmul_assoc, hca, rmul_one]

theorem dec_zero : dec 0 = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := rfl

theorem rdet_cjw_zero (a b : R9) : rdet (cjw a b ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩) = 0 := by
  simp only [cjw, rdet, rmul]
  ring

theorem lpow_eq (x : R9) (n : ℕ) : CFSG.QuasithinUnique.Fin253.lpow rmul rone x n = rpw x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rmul x _ = rmul x _
    rw [ih]

theorem getLL_mem : ∀ (l : List (List ℕ)) (i : ℕ), getLL l i ∈ l ∨ getLL l i = []
  | [], _ => Or.inr rfl
  | x :: l, 0 => Or.inl (List.mem_cons_self ..)
  | x :: l, i + 1 => by
    change Bool.rec (motive := fun _ => List ℕ) (getLL l (Nat.sub (i + 1) 1)) x
      (Nat.beq (i + 1) 0) ∈ _ ∨ _
    rw [show Nat.beq (i + 1) 0 = false from rfl, show Nat.sub (i + 1) 1 = i from rfl]
    rcases getLL_mem l i with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

end CFSG.KC.LQT.R

end
