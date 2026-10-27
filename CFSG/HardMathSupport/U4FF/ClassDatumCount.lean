module

public import CFSG.HardMathSupport.U4FF.ClassUminusB

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open scoped Classical

namespace Datum

section Param

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def upMat (u : ↥(UpperU K n)) : Matrix (Fin 4) (Fin 4) K :=
  ((u : SU (unitaryInvolution K 2 n) 4) : GL (Fin 4) K)

@[expose] def paramW (u : ↥(UpperU K n)) : K × K × K × K :=
  (upMat u 2 3, upMat u 1 3, upMat u 1 2, upMat u 0 3)

theorem isUpperUni_wMat (n : ℕ) (a b c d : K) : IsUpperUni (wMat n a b c d) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hji (by decide) | simp [wMat]
  · fin_cases i <;> simp [wMat]

theorem exists_paramW {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(UpperU K n)) :
    ∃ a b c d : K, UCond n a b c d ∧ upMat u = wMat n a b c d :=
  exists_wCond_of_mem n hK (u : SU (unitaryInvolution K 2 n) 4).2 (mem_UpperU.mp u.2)

theorem upMat_eq_wMat {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(UpperU K n)) :
    upMat u = wMat n (paramW u).1 (paramW u).2.1 (paramW u).2.2.1 (paramW u).2.2.2 := by
  obtain ⟨a, b, c, d, -, h⟩ := exists_paramW hK u
  have hp : paramW u = (a, b, c, d) := by
    simp only [paramW, h]
    simp [wMat]
  rw [hp]
  exact h

theorem paramW_ucond {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(UpperU K n)) :
    UCond n (paramW u).1 (paramW u).2.1 (paramW u).2.2.1 (paramW u).2.2.2 := by
  obtain ⟨a, b, c, d, h1, h⟩ := exists_paramW hK u
  have hp : paramW u = (a, b, c, d) := by
    simp only [paramW, h]
    simp [wMat]
  rw [hp]
  exact h1

theorem paramW_injective {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {u v : ↥(UpperU K n)}
    (h : paramW u = paramW v) : u = v := by
  have hm : upMat u = upMat v := by
    rw [upMat_eq_wMat hK u, upMat_eq_wMat hK v, h]
  apply Subtype.ext
  apply Subtype.ext
  exact Units.ext hm

@[expose] noncomputable def ofParamW {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {a b c d : K}
    (h : UCond n a b c d) : ↥(UpperU K n) :=
  ⟨⟨Matrix.SpecialLinearGroup.toGL (wSL n a b c d), wMat_mem_SU n hK h⟩,
    mem_UpperU.mpr (isUpperUni_wMat n a b c d)⟩

theorem paramW_ofParamW {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {a b c d : K}
    (h : UCond n a b c d) : paramW (ofParamW hK h) = (a, b, c, d) := by
  have hu : upMat (ofParamW hK h) = wMat n a b c d := rfl
  simp only [paramW, hu]
  simp [wMat]

theorem UCond_iff_shiftW {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (a b c d : K) :
    UCond n a b c d ↔ c ^ 2 ^ n = c ∧ (d + a ^ 2 ^ n * b) ^ 2 ^ n = d + a ^ 2 ^ n * b := by
  unfold UCond
  rw [shift_fix_iff hK]

theorem cardBoxW (A B C T : K → Prop) :
    Nat.card {w : K × K × K × K // A w.1 ∧ B w.2.1 ∧ C w.2.2.1 ∧ T w.2.2.2} =
      Nat.card {a // A a} * Nat.card {b // B b} * Nat.card {c // C c} * Nat.card {t // T t} := by
  have e : {w : K × K × K × K // A w.1 ∧ B w.2.1 ∧ C w.2.2.1 ∧ T w.2.2.2} ≃
      {a // A a} × {b // B b} × {c // C c} × {t // T t} :=
    { toFun := fun w => (⟨w.1.1, w.2.1⟩, ⟨w.1.2.1, w.2.2.1⟩, ⟨w.1.2.2.1, w.2.2.2.1⟩,
        ⟨w.1.2.2.2, w.2.2.2.2⟩)
      invFun := fun x => ⟨(x.1.1, x.2.1.1, x.2.2.1.1, x.2.2.2.1),
        x.1.2, x.2.1.2, x.2.2.1.2, x.2.2.2.2⟩
      left_inv := fun w => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

theorem cardShiftBoxW {n : ℕ} (P : K × K × K × K → Prop) (A B C T : K → Prop) {m₁ m₂ m₃ m₄ : ℕ}
    (h : ∀ v : K × K × K × K, (UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ P v) ↔
      (A v.1 ∧ B v.2.1 ∧ C v.2.2.1 ∧ T (v.2.2.2 + v.1 ^ 2 ^ n * v.2.1)))
    (hA : Nat.card {a // A a} = m₁) (hB : Nat.card {b // B b} = m₂)
    (hC : Nat.card {c // C c} = m₃) (hT : Nat.card {t // T t} = m₄) :
    Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ P v} =
      m₁ * m₂ * m₃ * m₄ := by
  have e1 : Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ P v} =
      Nat.card {w : K × K × K × K // A w.1 ∧ B w.2.1 ∧ C w.2.2.1 ∧ T w.2.2.2} :=
    Nat.card_congr (Equiv.subtypeEquiv (shiftE n) (fun v => h v))
  rw [e1, cardBoxW A B C T, hA, hB, hC, hT]

theorem card_subtype_paramW {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (R : K × K × K × K → Prop) :
    Nat.card {u : ↥(UpperU K n) // R (paramW u)} =
      Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ R v} := by
  refine Nat.card_eq_of_bijective
    (fun u => ⟨paramW u.1, paramW_ucond hK u.1, u.2⟩) ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    have h' : paramW u = paramW v := congrArg Subtype.val h
    have := paramW_injective hK h'
    subst this
    rfl
  · rintro ⟨⟨a, b, c, d⟩, hv, hR⟩
    refine ⟨⟨ofParamW hK hv, ?_⟩, ?_⟩
    · rw [paramW_ofParamW hK hv]
      exact hR
    · apply Subtype.ext
      exact paramW_ofParamW hK hv

@[expose] def patK (i : Fin 8) : K × K × K × K → Prop :=
  ![fun _ => True, fun v => v.1 = 0, fun v => v.2.2.1 = 0, fun v => v.1 = 0 ∧ v.2.2.2 = 0,
    fun v => v.2.1 = 0 ∧ v.2.2.1 = 0, fun v => v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2.2 = 0,
    fun v => v.2.1 = 0 ∧ v.2.2.1 = 0 ∧ v.2.2.2 = 0,
    fun v => v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2.1 = 0 ∧ v.2.2.2 = 0] i

@[expose] def cntTab : Fin 8 → ℕ := ![6, 4, 5, 3, 3, 1, 2, 0]

theorem card_patK {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (i : Fin 8) :
    Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ patK i v} =
      (2 ^ n) ^ cntTab i := by
  have hq : (2 : ℕ) ^ n ≠ 0 := by positivity
  have cA : Nat.card {a : K // True} = (2 ^ n) ^ 2 := by
    rw [← hK]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))
  have cZ : Nat.card {a : K // a = 0} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩, ⟨⟨0, rfl⟩⟩⟩
  have cF : Nat.card {c : K // c ^ 2 ^ n = c} = 2 ^ n := card_fixed_eq hK
  have hzc : ∀ c : K, c = 0 → c ^ 2 ^ n = c := fun c h => by
    subst h
    exact zero_pow hq
  fin_cases i
  · refine Eq.trans (cardShiftBoxW (n := n) (patK 0) (fun _ => True) (fun _ => True)
      (fun c => c ^ 2 ^ n = c) (fun t => t ^ 2 ^ n = t) ?_ cA cA cF cF) ?_
    · rintro ⟨a, b, c, d⟩
      show (UCond n a b c d ∧ True) ↔
        (True ∧ True ∧ c ^ 2 ^ n = c ∧ (d + a ^ 2 ^ n * b) ^ 2 ^ n = d + a ^ 2 ^ n * b)
      rw [UCond_iff_shiftW hK]
      tauto
    · show (2 ^ n) ^ 2 * (2 ^ n) ^ 2 * 2 ^ n * 2 ^ n = (2 ^ n) ^ 6
      ring
  · refine Eq.trans (cardShiftBoxW (n := n) (patK 1) (fun a => a = 0) (fun _ => True)
      (fun c => c ^ 2 ^ n = c) (fun t => t ^ 2 ^ n = t) ?_ cZ cA cF cF) ?_
    · rintro ⟨a, b, c, d⟩
      show (UCond n a b c d ∧ a = 0) ↔
        (a = 0 ∧ True ∧ c ^ 2 ^ n = c ∧ (d + a ^ 2 ^ n * b) ^ 2 ^ n = d + a ^ 2 ^ n * b)
      rw [UCond_iff_shiftW hK]
      tauto
    · show 1 * (2 ^ n) ^ 2 * 2 ^ n * 2 ^ n = (2 ^ n) ^ 4
      ring
  · refine Eq.trans (cardShiftBoxW (n := n) (patK 2) (fun _ => True) (fun _ => True)
      (fun c => c = 0) (fun t => t ^ 2 ^ n = t) ?_ cA cA cZ cF) ?_
    · rintro ⟨a, b, c, d⟩
      show (UCond n a b c d ∧ c = 0) ↔
        (True ∧ True ∧ c = 0 ∧ (d + a ^ 2 ^ n * b) ^ 2 ^ n = d + a ^ 2 ^ n * b)
      rw [UCond_iff_shiftW hK]
      constructor
      · rintro ⟨⟨-, hS⟩, hc⟩
        exact ⟨trivial, trivial, hc, hS⟩
      · rintro ⟨-, -, hc, hS⟩
        exact ⟨⟨hzc c hc, hS⟩, hc⟩
    · show (2 ^ n) ^ 2 * (2 ^ n) ^ 2 * 1 * 2 ^ n = (2 ^ n) ^ 5
      ring
  · refine Eq.trans (cardShiftBoxW (n := n) (patK 3) (fun a => a = 0) (fun _ => True)
      (fun c => c ^ 2 ^ n = c) (fun t => t = 0) ?_ cZ cA cF cZ) ?_
    · rintro ⟨a, b, c, d⟩
      show (UCond n a b c d ∧ (a = 0 ∧ d = 0)) ↔
        (a = 0 ∧ True ∧ c ^ 2 ^ n = c ∧ d + a ^ 2 ^ n * b = 0)
      rw [UCond_iff_shiftW hK]
      constructor
      · rintro ⟨⟨hF, -⟩, ha, hd⟩
        refine ⟨ha, trivial, hF, ?_⟩
        rw [hd, ha, zero_pow hq, zero_mul, add_zero]
      · rintro ⟨ha, -, hF, ht⟩
        have hd : d = 0 := by
          rw [ha, zero_pow hq, zero_mul, add_zero] at ht
          exact ht
        exact ⟨⟨hF, by rw [ht, zero_pow hq]⟩, ha, hd⟩
    · show 1 * (2 ^ n) ^ 2 * 2 ^ n * 1 = (2 ^ n) ^ 3
      ring
  · refine Eq.trans (cardShiftBoxW (n := n) (patK 4) (fun _ => True) (fun b => b = 0)
      (fun c => c = 0) (fun t => t ^ 2 ^ n = t) ?_ cA cZ cZ cF) ?_
    · rintro ⟨a, b, c, d⟩
      show (UCond n a b c d ∧ (b = 0 ∧ c = 0)) ↔
        (True ∧ b = 0 ∧ c = 0 ∧ (d + a ^ 2 ^ n * b) ^ 2 ^ n = d + a ^ 2 ^ n * b)
      rw [UCond_iff_shiftW hK]
      constructor
      · rintro ⟨⟨-, hS⟩, hb, hc⟩
        exact ⟨trivial, hb, hc, hS⟩
      · rintro ⟨-, hb, hc, hS⟩
        exact ⟨⟨hzc c hc, hS⟩, hb, hc⟩
    · show (2 ^ n) ^ 2 * 1 * 1 * 2 ^ n = (2 ^ n) ^ 3
      ring
  · refine Eq.trans (cardShiftBoxW (n := n) (patK 5) (fun a => a = 0) (fun b => b = 0)
      (fun c => c ^ 2 ^ n = c) (fun t => t = 0) ?_ cZ cZ cF cZ) ?_
    · rintro ⟨a, b, c, d⟩
      show (UCond n a b c d ∧ (a = 0 ∧ b = 0 ∧ d = 0)) ↔
        (a = 0 ∧ b = 0 ∧ c ^ 2 ^ n = c ∧ d + a ^ 2 ^ n * b = 0)
      rw [UCond_iff_shiftW hK]
      constructor
      · rintro ⟨⟨hF, -⟩, ha, hb, hd⟩
        refine ⟨ha, hb, hF, ?_⟩
        rw [hd, hb, mul_zero, add_zero]
      · rintro ⟨ha, hb, hF, ht⟩
        have hd : d = 0 := by
          rw [hb, mul_zero, add_zero] at ht
          exact ht
        exact ⟨⟨hF, by rw [ht, zero_pow hq]⟩, ha, hb, hd⟩
    · show 1 * 1 * 2 ^ n * 1 = (2 ^ n) ^ 1
      ring
  · refine Eq.trans (cardShiftBoxW (n := n) (patK 6) (fun _ => True) (fun b => b = 0)
      (fun c => c = 0) (fun t => t = 0) ?_ cA cZ cZ cZ) ?_
    · rintro ⟨a, b, c, d⟩
      show (UCond n a b c d ∧ (b = 0 ∧ c = 0 ∧ d = 0)) ↔
        (True ∧ b = 0 ∧ c = 0 ∧ d + a ^ 2 ^ n * b = 0)
      rw [UCond_iff_shiftW hK]
      constructor
      · rintro ⟨-, hb, hc, hd⟩
        refine ⟨trivial, hb, hc, ?_⟩
        rw [hd, hb, mul_zero, add_zero]
      · rintro ⟨-, hb, hc, ht⟩
        have hd : d = 0 := by
          rw [hb, mul_zero, add_zero] at ht
          exact ht
        exact ⟨⟨hzc c hc, by rw [ht, zero_pow hq]⟩, hb, hc, hd⟩
    · show (2 ^ n) ^ 2 * 1 * 1 * 1 = (2 ^ n) ^ 2
      ring
  · refine Eq.trans (cardShiftBoxW (n := n) (patK 7) (fun a => a = 0) (fun b => b = 0)
      (fun c => c = 0) (fun t => t = 0) ?_ cZ cZ cZ cZ) ?_
    · rintro ⟨a, b, c, d⟩
      show (UCond n a b c d ∧ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) ↔
        (a = 0 ∧ b = 0 ∧ c = 0 ∧ d + a ^ 2 ^ n * b = 0)
      rw [UCond_iff_shiftW hK]
      constructor
      · rintro ⟨-, ha, hb, hc, hd⟩
        refine ⟨ha, hb, hc, ?_⟩
        rw [hd, hb, mul_zero, add_zero]
      · rintro ⟨ha, hb, hc, ht⟩
        have hd : d = 0 := by
          rw [hb, mul_zero, add_zero] at ht
          exact ht
        exact ⟨⟨hzc c hc, by rw [ht, zero_pow hq]⟩, ha, hb, hc, hd⟩
    · show 1 * 1 * 1 * 1 = (2 ^ n) ^ 0
      ring

theorem card_UpperU_patK {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (i : Fin 8) :
    Nat.card {u : ↥(UpperU K n) // patK i (paramW u)} = (2 ^ n) ^ cntTab i := by
  rw [card_subtype_paramW hK, card_patK hK]

theorem card_UpperU {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card ↥(UpperU K n) = (2 ^ n) ^ 6 := by
  have h := card_UpperU_patK hK 0
  have e : Nat.card ↥(UpperU K n) = Nat.card {u : ↥(UpperU K n) // patK 0 (paramW u)} :=
    (Nat.card_congr (Equiv.subtypeUnivEquiv (fun u => by simp [patK]))).symm
  rw [e, h]
  rfl

end Param

end Datum

end CFSG.HardMathSupport.U4FF
