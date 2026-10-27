module

public import CFSG.Dihedral.Glauberman.DicksonMaxSubfield
public import CFSG.Dihedral.Glauberman.DicksonMaxTraceField

public section

namespace CFSG.Glauberman.Dickson.MaxTrace

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxSubfield
open CFSG.GorensteinWalter Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def chAB (t : F) : ℕ → F × F
  | 0 => (1, 0)
  | n + 1 => (t * (chAB t n).1 - (chAB t n).2, (chAB t n).1)

theorem pow_succ_eq_chAB {A : Matrix (Fin 2) (Fin 2) F} {t : F}
    (hA : A * A = t • A - 1) (n : ℕ) :
    A ^ (n + 1) = (chAB t n).1 • A - (chAB t n).2 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  induction n with
  | zero => simp [chAB]
  | succ n ih =>
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hA]
    simp only [chAB, smul_sub, sub_smul, smul_smul]
    module

theorem chAB_one (t : F) : chAB t 1 = (t, 1) := by simp [chAB]

theorem chAB_two (t : F) : chAB t 2 = (t ^ 2 - 1, t) := by simp [chAB]; ring

theorem chAB_three (t : F) : chAB t 3 = (t ^ 3 - 2 * t, t ^ 2 - 1) := by
  simp [chAB]
  constructor <;> ring

theorem chAB_four (t : F) : chAB t 4 = (t ^ 4 - 3 * t ^ 2 + 1, t ^ 3 - 2 * t) := by
  simp [chAB]
  constructor <;> ring

theorem trace_cond_of_pow_matrix {A : Matrix (Fin 2) (Fin 2) F} (hdet : A.det = 1) (n : ℕ)
    {ε : F} (hA : A ^ (n + 1) = ε • 1) :
    (chAB A.trace n).1 = 0 ∨ A.trace ^ 2 = 4 := by
  have hCH : A * A = A.trace • A - 1 := by
    have := TraceField.sq_eq_trace_smul_sub A
    rwa [hdet, one_smul] at this
  have hpow := pow_succ_eq_chAB hCH n
  by_cases ha : (chAB A.trace n).1 = 0
  · exact Or.inl ha
  right
  have h0 : (chAB A.trace n).1 • A - (chAB A.trace n).2 • 1 =
      ε • (1 : Matrix (Fin 2) (Fin 2) F) := hpow.symm.trans hA
  have h1 : (chAB A.trace n).1 • A =
      ((chAB A.trace n).2 + ε) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [add_smul, ← h0]
    abel
  have hAl : A = ((chAB A.trace n).1⁻¹ * ((chAB A.trace n).2 + ε)) • 1 := by
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  generalize (chAB A.trace n).1⁻¹ * ((chAB A.trace n).2 + ε) = l at hAl
  have hl : l ^ 2 = 1 := by
    rw [hAl, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hdet
    exact hdet
  have htl : A.trace = 2 * l := by
    rw [hAl, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  rw [htl]
  linear_combination 4 * hl

theorem trace_cond_of_pow (A : SL(2, F)) (n : ℕ) (hA : A ^ (n + 1) = 1 ∨ A ^ (n + 1) = -1) :
    (chAB (A : Matrix (Fin 2) (Fin 2) F).trace n).1 = 0 ∨
      (A : Matrix (Fin 2) (Fin 2) F).trace ^ 2 = 4 := by
  rcases hA with h | h
  · refine trace_cond_of_pow_matrix A.2 n (ε := 1) ?_
    rw [← Matrix.SpecialLinearGroup.coe_pow, h, one_smul, Matrix.SpecialLinearGroup.coe_one]
  · refine trace_cond_of_pow_matrix A.2 n (ε := -1) ?_
    rw [← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, neg_smul, one_smul]

theorem two_mem_subfield (K₀ : Subfield F) : (2 : F) ∈ K₀ := by
  have h := K₀.add_mem K₀.one_mem K₀.one_mem
  rwa [one_add_one_eq_two] at h

theorem mem_of_quadratic (h2 : (2 : F) ≠ 0) {K₀ : Subfield F} {b c s t : F} (hb : b ∈ K₀)
    (hs : s ∈ K₀) (hsq : s ^ 2 = b ^ 2 - 4 * c) (ht : t ^ 2 + b * t + c = 0) : t ∈ K₀ := by
  have h : (2 * t + b - s) * (2 * t + b + s) = 0 := by linear_combination 4 * ht - hsq
  rcases mul_eq_zero.mp h with h' | h'
  · have e : t = (s - b) / 2 := by field_simp; linear_combination h'
    rw [e]
    exact K₀.div_mem (K₀.sub_mem hs hb) (two_mem_subfield K₀)
  · have e : t = (-s - b) / 2 := by field_simp; linear_combination h'
    rw [e]
    exact K₀.div_mem (K₀.sub_mem (K₀.neg_mem hs) hb) (two_mem_subfield K₀)

theorem mem_of_sq_eq_four {K₀ : Subfield F} {t : F} (h : t ^ 2 = 4) : t ∈ K₀ := by
  have h' : (t - 2) * (t + 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h'' | h''
  · rw [show t = 2 by linear_combination h'']
    exact two_mem_subfield K₀
  · rw [show t = -2 by linear_combination h'']
    exact K₀.neg_mem (two_mem_subfield K₀)

theorem pow_lift {A : SL(2, F)} {n : ℕ} (h : mk A ^ n = 1) : A ^ n = 1 ∨ A ^ n = -1 := by
  rwa [← map_pow, mk_eq_one_iff] at h

theorem eq_one_or_neg_of_mul_self (h2 : (2 : F) ≠ 0) {B : SL(2, F)} (hB : B * B = 1) :
    B = 1 ∨ B = -1 := by
  have hdet : (B : Matrix (Fin 2) (Fin 2) F).det = 1 := B.2
  have hCH := TraceField.sq_eq_trace_smul_sub (B : Matrix (Fin 2) (Fin 2) F)
  rw [hdet, one_smul] at hCH
  have hB' : (B : Matrix (Fin 2) (Fin 2) F) * B = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hB, Matrix.SpecialLinearGroup.coe_one]
  rw [hB'] at hCH
  have htB : (B : Matrix (Fin 2) (Fin 2) F).trace • (B : Matrix (Fin 2) (Fin 2) F) =
      (2 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [two_smul]
    exact (eq_sub_iff_add_eq.mp hCH).symm
  have ht : (B : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at htB
    have h00 := congrFun (congrFun htB 0) 0
    rw [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    exact h2 h00.symm
  have hBl : (B : Matrix (Fin 2) (Fin 2) F) = (2 / (B : Matrix (Fin 2) (Fin 2) F).trace) • 1 := by
    rw [div_eq_inv_mul, mul_smul, ← htB, smul_smul, inv_mul_cancel₀ ht, one_smul]
  generalize 2 / (B : Matrix (Fin 2) (Fin 2) F).trace = l at hBl
  have hl2 : l ^ 2 = 1 := by
    rw [hBl, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hdet
    exact hdet
  have hl' : (l - 1) * (l + 1) = 0 := by linear_combination hl2
  rcases mul_eq_zero.mp hl' with h | h
  · left
    apply Subtype.ext
    rw [hBl, show l = 1 by linear_combination h, one_smul, Matrix.SpecialLinearGroup.coe_one]
  · right
    apply Subtype.ext
    rw [hBl, show l = -1 by linear_combination h, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, neg_smul, one_smul]

theorem lift_involution (h2 : (2 : F) ≠ 0) {A : SL(2, F)} (ha2 : mk A * mk A = 1)
    (ha1 : mk A ≠ 1) : A * A = -1 := by
  rw [← map_mul, mk_eq_one_iff] at ha2
  rcases ha2 with h | h
  · exfalso
    apply ha1
    rcases eq_one_or_neg_of_mul_self h2 h with h' | h'
    · rw [h', map_one]
    · rw [h', mk_neg, map_one]
  · exact h

theorem lift_anticomm (h2 : (2 : F) ≠ 0) {A B : SL(2, F)} (hA : A * A = -1) (hB : B * B = -1)
    (hc : mk A * mk B = mk B * mk A) (hab : mk A ≠ mk B) : B * A = -(A * B) := by
  rw [← map_mul, ← map_mul, mk_eq_mk_iff] at hc
  rcases hc with h | h
  · exfalso
    have hAinv : A⁻¹ = -A := by rw [inv_eq_iff_mul_eq_one, mul_neg, hA, neg_neg]
    have hAB : (A * B) * (A * B) = 1 := by
      calc (A * B) * (A * B) = A * (B * A) * B := by group
        _ = A * (A * B) * B := by rw [h]
        _ = (A * A) * (B * B) := by group
        _ = 1 := by rw [hA, hB, neg_mul, mul_neg, neg_neg, one_mul]
    apply hab
    rcases eq_one_or_neg_of_mul_self h2 hAB with h' | h'
    · have hBA : B = -A := by rw [← hAinv]; exact eq_inv_of_mul_eq_one_right h'
      rw [hBA, mk_neg]
    · have h'' : A * -B = 1 := by rw [mul_neg, h', neg_neg]
      have hBA : -B = -A := by rw [← hAinv]; exact eq_inv_of_mul_eq_one_right h''
      rw [neg_inj.mp hBA]
  · exact h

theorem trace_mem_of_pow {K₀ : Subfield F} {A : SL(2, F)} {n : ℕ} (hA : mk A ^ (n + 1) = 1)
    (hK : ∀ t : F, (chAB t n).1 = 0 → t ∈ K₀) : (A : Matrix (Fin 2) (Fin 2) F).trace ∈ K₀ := by
  rcases trace_cond_of_pow A n (pow_lift hA) with h | h
  · exact hK _ h
  · exact mem_of_sq_eq_four h

theorem trace_mem_of_pow_two (K₀ : Subfield F) {A : SL(2, F)} (hA : mk A ^ 2 = 1) :
    (A : Matrix (Fin 2) (Fin 2) F).trace ∈ K₀ :=
  trace_mem_of_pow (n := 1) hA fun t ht => by
    rw [chAB_one] at ht
    rw [show t = 0 from ht]
    exact K₀.zero_mem

theorem trace_mem_of_pow_three (K₀ : Subfield F) {A : SL(2, F)} (hA : mk A ^ 3 = 1) :
    (A : Matrix (Fin 2) (Fin 2) F).trace ∈ K₀ :=
  trace_mem_of_pow (n := 2) hA fun t ht => by
    rw [chAB_two] at ht
    have ht' : (t - 1) * (t + 1) = 0 := by
      have : t ^ 2 - 1 = 0 := ht
      linear_combination this
    rcases mul_eq_zero.mp ht' with h | h
    · rw [show t = 1 by linear_combination h]
      exact K₀.one_mem
    · rw [show t = -1 by linear_combination h]
      exact K₀.neg_mem K₀.one_mem

theorem trace_mem_of_pow_four (h2 : (2 : F) ≠ 0) {K₀ : Subfield F} {s : F} (hs : s ∈ K₀)
    (hs2 : s ^ 2 = 2) {A : SL(2, F)} (hA : mk A ^ 4 = 1) :
    (A : Matrix (Fin 2) (Fin 2) F).trace ∈ K₀ :=
  trace_mem_of_pow (n := 3) hA fun t ht => by
    rw [chAB_three] at ht
    have ht' : t * (t ^ 2 + 0 * t + -2) = 0 := by
      have : t ^ 3 - 2 * t = 0 := ht
      linear_combination this
    rcases mul_eq_zero.mp ht' with h | h
    · rw [h]
      exact K₀.zero_mem
    · exact mem_of_quadratic h2 K₀.zero_mem (K₀.mul_mem (two_mem_subfield K₀) hs)
        (show (2 * s) ^ 2 = 0 ^ 2 - 4 * (-2) by linear_combination 4 * hs2) h

theorem trace_mem_of_pow_five (h2 : (2 : F) ≠ 0) {K₀ : Subfield F} {s : F} (hs : s ∈ K₀)
    (hs5 : s ^ 2 = 5) {A : SL(2, F)} (hA : mk A ^ 5 = 1) :
    (A : Matrix (Fin 2) (Fin 2) F).trace ∈ K₀ :=
  trace_mem_of_pow (n := 4) hA fun t ht => by
    rw [chAB_four] at ht
    have ht' : (t ^ 2 + -1 * t + -1) * (t ^ 2 + 1 * t + -1) = 0 := by
      have : t ^ 4 - 3 * t ^ 2 + 1 = 0 := ht
      linear_combination this
    rcases mul_eq_zero.mp ht' with h | h
    · exact mem_of_quadratic h2 (K₀.neg_mem K₀.one_mem) hs
        (show s ^ 2 = (-1) ^ 2 - 4 * (-1) by linear_combination hs5) h
    · exact mem_of_quadratic h2 K₀.one_mem hs
        (show s ^ 2 = 1 ^ 2 - 4 * (-1) by linear_combination hs5) h

section FixField

variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem mem_fixField_two_of_quadratic {b c t : F} (hb : b ∈ fixField F p 1)
    (hc : c ∈ fixField F p 1) (ht : t ^ 2 + b * t + c = 0) : t ∈ fixField F p 2 := by
  rw [mem_fixField] at hb hc ⊢
  rw [pow_one] at hb hc
  have hφ : ∀ y : F, frobenius F p y = y ^ p := fun y => frobenius_def p y
  have hφb : frobenius F p b = b := by rw [hφ, hb]
  have hφc : frobenius F p c = c := by rw [hφ, hc]
  have hroot : ∀ y : F, y ^ 2 + b * y + c = 0 → y = t ∨ y = -b - t := by
    intro y hy
    have h : (y - t) * (y - (-b - t)) = 0 := by linear_combination hy - ht
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (sub_eq_zero.mp h')
  have hφt : (frobenius F p t) ^ 2 + b * frobenius F p t + c = 0 := by
    have h := congrArg (frobenius F p) ht
    rwa [map_add, map_add, map_mul, map_pow, map_zero, hφb, hφc] at h
  have e : t ^ p ^ 2 = frobenius F p (frobenius F p t) := by
    rw [hφ, hφ, ← pow_mul, ← pow_two]
  rw [e]
  rcases hroot _ hφt with h | h
  · rw [h, h]
  · rw [h, map_sub, map_neg, hφb, h]
    ring

theorem trace_mem_fixField_two_of_pow_four {A : SL(2, F)} (hA : mk A ^ 4 = 1) :
    (A : Matrix (Fin 2) (Fin 2) F).trace ∈ fixField F p 2 :=
  trace_mem_of_pow (n := 3) hA fun t ht => by
    rw [chAB_three] at ht
    have ht' : t * (t ^ 2 + 0 * t + -2) = 0 := by
      have : t ^ 3 - 2 * t = 0 := ht
      linear_combination this
    rcases mul_eq_zero.mp ht' with h | h
    · rw [h]
      exact (fixField F p 2).zero_mem
    · exact mem_fixField_two_of_quadratic (fixField F p 1).zero_mem
        ((fixField F p 1).neg_mem (two_mem_subfield _)) h

theorem trace_mem_fixField_two_of_pow_five {A : SL(2, F)} (hA : mk A ^ 5 = 1) :
    (A : Matrix (Fin 2) (Fin 2) F).trace ∈ fixField F p 2 :=
  trace_mem_of_pow (n := 4) hA fun t ht => by
    rw [chAB_four] at ht
    have ht' : (t ^ 2 + -1 * t + -1) * (t ^ 2 + 1 * t + -1) = 0 := by
      have : t ^ 4 - 3 * t ^ 2 + 1 = 0 := ht
      linear_combination this
    have hm1 : (-1 : F) ∈ fixField F p 1 := (fixField F p 1).neg_mem (fixField F p 1).one_mem
    rcases mul_eq_zero.mp ht' with h | h
    · exact mem_fixField_two_of_quadratic hm1 hm1 h
    · exact mem_fixField_two_of_quadratic (fixField F p 1).one_mem hm1 h

end FixField

theorem exists_conj_pglImage
    [Finite F] (h2 : (2 : F) ≠ 0) (K₀ : Subfield F)
    (M : Subgroup (PSL2MatrixGroup F))
    (htr : ∀ A : SL(2, F), mk A ∈ M → (A : Matrix (Fin 2) (Fin 2) F).trace ∈ K₀)
    {a b : PSL2MatrixGroup F} (ha : a ∈ M) (hb : b ∈ M) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (ha2 : a * a = 1) (hb2 : b * b = 1) (hc : a * b = b * a) :
    ∃ c : PGL2 F, ∀ x ∈ M,
      c * Matrix.ProjectiveSpecialLinearGroup.toPGL x * c⁻¹ ∈ pglImage K₀ := by
  obtain ⟨A, rfl⟩ := mk_surjective a
  obtain ⟨B, rfl⟩ := mk_surjective b
  have hA := lift_involution h2 ha2 ha1
  have hB := lift_involution h2 hb2 hb1
  have hBA := lift_anticomm h2 hA hB hc hab
  have hcoe : ∀ X Y : SL(2, F), X * Y = -1 →
      (X : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro X Y h
    rw [← Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
  let S : Set (Matrix (Fin 2) (Fin 2) F) :=
    {X | ∃ C : SL(2, F), mk C ∈ M ∧ (C : Matrix (Fin 2) (Fin 2) F) = X}
  have hS1 : (1 : Matrix (Fin 2) (Fin 2) F) ∈ S :=
    ⟨1, by rw [map_one]; exact M.one_mem, Matrix.SpecialLinearGroup.coe_one⟩
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    exact ⟨X * Y, by rw [map_mul]; exact M.mul_mem hX hY, Matrix.SpecialLinearGroup.coe_mul X Y⟩
  have hStr : ∀ x ∈ S, x.trace ∈ K₀ := by
    rintro _ ⟨X, hX, rfl⟩
    exact htr X hX
  obtain ⟨P, Q, hPQ, hQP, hent⟩ := TraceField.exists_conj_entries_mem_subfield h2 K₀ S hS1
    hSmul hStr ⟨A, ha, rfl⟩ ⟨B, hb, rfl⟩ A.2 B.2 (hcoe A A hA) (hcoe B B hB)
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hBA,
      Matrix.SpecialLinearGroup.coe_neg])
  let U : GL (Fin 2) F := ⟨Q, P, hQP, hPQ⟩
  refine ⟨Matrix.ProjGenLinGroup.mk U, fun x hx => ?_⟩
  obtain ⟨X, rfl⟩ := mk_surjective x
  have hXS : (X : Matrix (Fin 2) (Fin 2) F) ∈ S := ⟨X, hx, rfl⟩
  let Y : Matrix (Fin 2) (Fin 2) K₀ := fun i j => ⟨(Q * X * P) i j, hent _ hXS i j⟩
  have hY : K₀.subtype.mapMatrix Y = Q * (X : Matrix (Fin 2) (Fin 2) F) * P := by
    ext i j
    rfl
  have hdetY : Y.det = 1 := by
    apply K₀.subtype_injective
    rw [map_one, RingHom.map_det, hY, det_mul, det_mul, X.2, mul_one, ← det_mul, hQP, det_one]
  refine ⟨Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL ⟨Y, hdetY⟩), ?_⟩
  rw [h826_pglMap_mk, show Matrix.ProjectiveSpecialLinearGroup.toPGL (mk X) =
    Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL X) from rfl, ← map_inv, ← map_mul,
    ← map_mul]
  congr 1
  apply Units.ext
  change K₀.subtype.mapMatrix Y = Q * (X : Matrix (Fin 2) (Fin 2) F) * P
  exact hY

end CFSG.Glauberman.Dickson.MaxTrace
