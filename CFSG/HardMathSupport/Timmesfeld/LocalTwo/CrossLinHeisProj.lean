module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisAlg
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {p : ℕ} [NeZero p] [Fact (1 < p)]

@[expose] noncomputable def eigProj (ψ : AddChar (ZMod p) K) (a : Module.End K V) (j : ZMod p) :
    Module.End K V :=
  (p : K)⁻¹ • ∑ k : ZMod p, ψ (-(j * k)) • a ^ k.val

theorem sum_char_mul {ψ : AddChar (ZMod p) K} (hψ : ψ.IsPrimitive) (b : ZMod p) :
    ∑ x : ZMod p, ψ (x * b) = if b = 0 then (p : K) else 0 := by
  have := AddChar.sum_mulShift (R := ZMod p) (R' := K) (ψ := ψ) b hψ
  rw [this]
  simp [ZMod.card]

theorem pow_val_add_one {a : Module.End K V} (ha : a ^ p = 1) (k : ZMod p) :
    a ^ (k + 1).val = a * a ^ k.val := by
  have h1 : (k + 1).val = (k.val + 1) % p := by
    rw [ZMod.val_add, ZMod.val_one]
  rw [h1, ← pow_eq_pow_mod _ ha, pow_succ']

theorem eigProj_eigen {ψ : AddChar (ZMod p) K} {a : Module.End K V} (ha : a ^ p = 1)
    (j : ZMod p) : a * eigProj ψ a j = ψ j • eigProj ψ a j := by
  set G : ZMod p → Module.End K V := fun k => ψ (-(j * k)) • a ^ k.val with hG
  have key : ∀ k : ZMod p, a * G k = ψ j • G (k + 1) := by
    intro k
    have e : ψ (-(j * k)) = ψ j * ψ (-(j * (k + 1))) := by
      rw [← AddChar.map_add_eq_mul]
      exact congrArg ψ (by ring)
    simp only [hG, mul_smul_comm, ← pow_val_add_one ha, smul_smul, e]
  have hE : eigProj ψ a j = (p : K)⁻¹ • ∑ k, G k := rfl
  calc a * eigProj ψ a j = (p : K)⁻¹ • ∑ k, a * G k := by
        rw [hE, mul_smul_comm, Finset.mul_sum]
    _ = (p : K)⁻¹ • ∑ k, ψ j • G (k + 1) := by simp only [key]
    _ = (p : K)⁻¹ • ψ j • ∑ k, G (k + 1) := by rw [← Finset.smul_sum]
    _ = (p : K)⁻¹ • ψ j • ∑ k, G k := by
        have := Equiv.sum_comp (Equiv.addRight (1 : ZMod p)) G
        simp only [Equiv.coe_addRight] at this
        rw [this]
    _ = ψ j • eigProj ψ a j := by rw [hE, smul_comm]

theorem pow_mul_eigProj {ψ : AddChar (ZMod p) K} {a : Module.End K V} (ha : a ^ p = 1)
    (j : ZMod p) (m : ℕ) : a ^ m * eigProj ψ a j = ψ j ^ m • eigProj ψ a j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, eigProj_eigen ha, smul_smul, pow_succ]

theorem eigProj_mul_eigProj {ψ : AddChar (ZMod p) K} (hψ : ψ.IsPrimitive) {a : Module.End K V}
    (ha : a ^ p = 1) (hpK : (p : K) ≠ 0) (i j : ZMod p) :
    eigProj ψ a i * eigProj ψ a j = if i = j then eigProj ψ a j else 0 := by
  have hi : eigProj ψ a i = (p : K)⁻¹ • ∑ k : ZMod p, ψ (-(i * k)) • a ^ k.val := rfl
  have h1 : eigProj ψ a i * eigProj ψ a j =
      (p : K)⁻¹ • (∑ k : ZMod p, ψ (k * (j - i))) • eigProj ψ a j := by
    calc eigProj ψ a i * eigProj ψ a j
        = (p : K)⁻¹ • ∑ k : ZMod p, (ψ (-(i * k)) • a ^ k.val) * eigProj ψ a j := by
          rw [hi, smul_mul_assoc, Finset.sum_mul]
      _ = (p : K)⁻¹ • ∑ k : ZMod p, ψ (k * (j - i)) • eigProj ψ a j := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_mul_assoc, pow_mul_eigProj ha, smul_smul]
          congr 1
          rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val,
            ← AddChar.map_add_eq_mul]
          exact congrArg ψ (by ring)
      _ = _ := by rw [Finset.sum_smul]
  rw [h1, sum_char_mul hψ]
  by_cases h : i = j
  · subst h
    simp [hpK]
  · have : j - i ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    simp [h, this]

theorem sum_eigProj {ψ : AddChar (ZMod p) K} (hψ : ψ.IsPrimitive) {a : Module.End K V}
    (ha : a ^ p = 1) (hpK : (p : K) ≠ 0) : ∑ j : ZMod p, eigProj ψ a j = 1 := by
  unfold eigProj
  rw [← Finset.smul_sum, Finset.sum_comm]
  have h1 : ∀ k : ZMod p, ∑ j : ZMod p, ψ (-(j * k)) • a ^ k.val =
      (if -k = 0 then (p : K) else 0) • a ^ k.val := by
    intro k
    rw [← Finset.sum_smul]
    congr 1
    rw [← sum_char_mul hψ (-k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg ψ (by ring)
  simp only [h1]
  rw [Finset.sum_eq_single (0 : ZMod p)]
  · simp only [neg_zero, if_true, ZMod.val_zero, pow_zero]
    rw [smul_smul, inv_mul_cancel₀ hpK, one_smul]
  · intro k _ hk
    have : -k ≠ 0 := neg_ne_zero.2 hk
    simp [this]
  · simp

theorem pow_mul_comm_of_mul_eq {ψ : AddChar (ZMod p) K} {a b : Module.End K V}
    (hab : a * b = ψ 1 • (b * a)) (m : ℕ) : a ^ m * b = ψ 1 ^ m • (b * a ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc a ^ (m + 1) * b = a * (a ^ m * b) := by rw [pow_succ', mul_assoc]
      _ = a * (ψ 1 ^ m • (b * a ^ m)) := by rw [ih]
      _ = ψ 1 ^ m • ((a * b) * a ^ m) := by rw [mul_smul_comm, mul_assoc]
      _ = ψ 1 ^ m • ((ψ 1 • (b * a)) * a ^ m) := by rw [hab]
      _ = ψ 1 ^ (m + 1) • (b * a ^ (m + 1)) := by
        rw [smul_mul_assoc, smul_smul, ← pow_succ, mul_assoc, ← pow_succ']

theorem shift_eigProj {ψ : AddChar (ZMod p) K} {a b : Module.End K V}
    (hab : a * b = ψ 1 • (b * a)) (j : ZMod p) :
    b * eigProj ψ a j = eigProj ψ a (j + 1) * b := by
  have hi : eigProj ψ a (j + 1) = (p : K)⁻¹ • ∑ k : ZMod p, ψ (-((j + 1) * k)) • a ^ k.val := rfl
  have hj : eigProj ψ a j = (p : K)⁻¹ • ∑ k : ZMod p, ψ (-(j * k)) • a ^ k.val := rfl
  have hterm : ∀ k : ZMod p, (ψ (-((j + 1) * k)) • a ^ k.val) * b =
      ψ (-(j * k)) • (b * a ^ k.val) := by
    intro k
    have e : -((j + 1) * k) + k = -(j * k) := by ring
    rw [smul_mul_assoc, pow_mul_comm_of_mul_eq hab, smul_smul, ← AddChar.map_nsmul_eq_pow,
      nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ← AddChar.map_add_eq_mul, e]
  rw [hi, hj, smul_mul_assoc, Finset.sum_mul, mul_smul_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hterm, mul_smul_comm]

theorem eigProj_apply_eigen {ψ : AddChar (ZMod p) K} {a : Module.End K V} (hpK : (p : K) ≠ 0)
    {j : ZMod p} {v : V} (hv : a v = ψ j • v) : eigProj ψ a j v = v := by
  have h1 : ∀ m : ℕ, (a ^ m) v = ψ j ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, ← pow_succ]
  have h2 : ∀ k : ZMod p, ψ (-(j * k)) • (a ^ k.val) v = v := by
    intro k
    rw [h1, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, smul_smul,
      ← AddChar.map_add_eq_mul]
    have : -(j * k) + k * j = 0 := by ring
    rw [this, AddChar.map_zero_eq_one, one_smul]
  unfold eigProj
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, h2]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ hpK, one_smul]

theorem heisData_of_split {ψ : AddChar (ZMod p) K} (hψ : ψ.IsPrimitive)
    {a b bi : Module.End K V} {c₀ : K} (ha : a ^ p = 1) (hpK : (p : K) ≠ 0)
    (hab : a * b = ψ 1 • (b * a)) (hb : b * bi = 1) (hbi : bi * b = 1)
    (hbp : b ^ p = c₀ • (1 : Module.End K V)) : HeisData p (eigProj ψ a) b bi c₀ where
  idem j := by simpa using eigProj_mul_eigProj hψ ha hpK j j
  orth i j hij := by rw [eigProj_mul_eigProj hψ ha hpK, if_neg hij]
  sum := sum_eigProj hψ ha hpK
  t_ti := hb
  ti_t := hbi
  tp := hbp
  shift j := shift_eigProj hab j

theorem mem_range_eigProj_iff {ψ : AddChar (ZMod p) K} {a : Module.End K V}
    (ha : a ^ p = 1) (hpK : (p : K) ≠ 0) (j : ZMod p) (v : V) :
    v ∈ LinearMap.range (eigProj ψ a j) ↔ a v = ψ j • v := by
  constructor
  · rintro ⟨w, rfl⟩
    have := congrArg (fun g : Module.End K V => g w) (eigProj_eigen (ψ := ψ) ha j)
    simpa [Module.End.mul_apply] using this
  · intro hv
    exact ⟨v, eigProj_apply_eigen hpK hv⟩

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
