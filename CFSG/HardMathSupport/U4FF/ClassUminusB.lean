module

public import CFSG.HardMathSupport.U4FF.ClassUminusA

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU antidiag_mul_single single_mul_antidiag)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open scoped Classical

variable {K : Type} [Field K]

section Fixed

variable [Finite K] [CharP K 2]

theorem one_lt_two_pow_of_card {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) : 1 < 2 ^ n := by
  by_contra h
  have h1 : 2 ^ n = 1 := by
    have : 0 < 2 ^ n := by positivity
    omega
  rw [h1] at hK
  have hsub : Subsingleton K := (Nat.card_eq_one_iff_unique.mp (by simpa using hK)).1
  exact zero_ne_one (Subsingleton.elim (0 : K) 1)

theorem two_pow_le_card_fixed {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    2 ^ n ≤ Nat.card {c : K // c ^ 2 ^ n = c} := by
  let tr : K →+ K :=
    { toFun := fun x => x + x ^ 2 ^ n
      map_zero' := by simp
      map_add' := fun x y => by rw [add_pow_char_pow]; ring }
  have hker : ∀ x, x ∈ tr.ker ↔ x ^ 2 ^ n = x := by
    intro x
    rw [AddMonoidHom.mem_ker]
    change x + x ^ 2 ^ n = 0 ↔ _
    constructor
    · intro h
      have := congrArg (· + x) h
      simp only [zero_add] at this
      rw [add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at this
      exact this
    · intro h
      rw [h, CharTwo.add_self_eq_zero]
  have hle : tr.range ≤ tr.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hker]
    change (x + x ^ 2 ^ n) ^ 2 ^ n = x + x ^ 2 ^ n
    rw [add_pow_char_pow, pow_pow_of_card hK, add_comm]
  have hcard : Nat.card K = Nat.card tr.ker * Nat.card tr.range := by
    rw [← AddSubgroup.card_mul_index tr.ker, AddSubgroup.index_ker]
  have hr : Nat.card tr.range ≤ Nat.card tr.ker := AddSubgroup.card_le_of_le hle
  have hkc : Nat.card tr.ker = Nat.card {c : K // c ^ 2 ^ n = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  rw [← hkc]
  by_contra hlt
  push Not at hlt
  have h1 : Nat.card K < (2 ^ n) ^ 2 := by
    rw [hcard, sq]
    calc Nat.card tr.ker * Nat.card tr.range ≤ Nat.card tr.ker * Nat.card tr.ker :=
          Nat.mul_le_mul_left _ hr
      _ < 2 ^ n * 2 ^ n := Nat.mul_self_lt_mul_self hlt
  omega

theorem card_fixed_le {n : ℕ} (hn : 1 < 2 ^ n) :
    Nat.card {c : K // c ^ 2 ^ n = c} ≤ 2 ^ n := by
  haveI := Fintype.ofFinite K
  have hne : (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K hn
  have hdeg : (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial K).natDegree = 2 ^ n :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K hn
  let Z : Finset K := Finset.univ.filter (fun c : K => c ^ 2 ^ n = c)
  have hsub : Z.val ⊆ (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial K).roots := by
    intro c hc
    rw [Finset.mem_val, Finset.mem_filter] at hc
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
    exact hc.2
  have h := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg] at h
  rw [Nat.subtype_card Z (fun x => by simp [Z])]
  exact h

theorem card_fixed_eq {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card {c : K // c ^ 2 ^ n = c} = 2 ^ n :=
  le_antisymm (card_fixed_le (one_lt_two_pow_of_card hK)) (two_pow_le_card_fixed hK)

theorem sum_fixed_eq [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    (∑ c : K, if c ^ 2 ^ n = c then (1 : ℕ) else 0) = 2 ^ n := by
  have h := card_fixed_eq hK
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  conv_rhs => rw [← h]
  simp [Finset.sum_boole]

end Fixed

theorem isLowerUni_uMat (n : ℕ) (a b c d : K) : IsLowerUni (uMat n a b c d) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [uMat]
  · fin_cases i <;> simp [uMat]

section Param

variable [Finite K] [CharP K 2]

@[expose] def loMat {n : ℕ} (u : ↥(LowerU K n)) : Matrix (Fin 4) (Fin 4) K :=
  ((u : SU (unitaryInvolution K 2 n) 4) : GL (Fin 4) K)

@[expose] def paramOf {n : ℕ} (u : ↥(LowerU K n)) : K × K × K × K :=
  (loMat u 1 0, loMat u 2 0, loMat u 2 1, loMat u 3 0)

theorem exists_param {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(LowerU K n)) :
    ∃ a b c d : K, UCond n a b c d ∧ loMat u = uMat n a b c d :=
  exists_uCond_of_mem n hK (u : SU (unitaryInvolution K 2 n) 4).2 (mem_LowerU.mp u.2)

theorem loMat_eq_uMat {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(LowerU K n)) :
    loMat u = uMat n (paramOf u).1 (paramOf u).2.1 (paramOf u).2.2.1 (paramOf u).2.2.2 := by
  obtain ⟨a, b, c, d, -, h⟩ := exists_param hK u
  have hp : paramOf u = (a, b, c, d) := by
    simp only [paramOf, h]
    simp [uMat]
  rw [hp]
  exact h

theorem paramOf_ucond {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(LowerU K n)) :
    UCond n (paramOf u).1 (paramOf u).2.1 (paramOf u).2.2.1 (paramOf u).2.2.2 := by
  obtain ⟨a, b, c, d, h1, h⟩ := exists_param hK u
  have hp : paramOf u = (a, b, c, d) := by
    simp only [paramOf, h]
    simp [uMat]
  rw [hp]
  exact h1

theorem paramOf_injective {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {u v : ↥(LowerU K n)}
    (h : paramOf u = paramOf v) : u = v := by
  have hm : loMat u = loMat v := by
    rw [loMat_eq_uMat hK u, loMat_eq_uMat hK v, h]
  apply Subtype.ext
  apply Subtype.ext
  exact Units.ext hm

@[expose] noncomputable def ofParam {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {a b c d : K}
    (h : UCond n a b c d) : ↥(LowerU K n) :=
  ⟨⟨Matrix.SpecialLinearGroup.toGL (uSL n a b c d), uMat_mem_SU n hK h⟩,
    mem_LowerU.mpr (isLowerUni_uMat n a b c d)⟩

theorem paramOf_ofParam {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {a b c d : K}
    (h : UCond n a b c d) : paramOf (ofParam hK h) = (a, b, c, d) := by
  have hu : ((uSL n a b c d : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = uMat n a b c d := rfl
  simp [paramOf, loMat, ofParam, hu, uMat]

theorem card_subtype_param {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (R : K × K × K × K → Prop) :
    Nat.card {u : ↥(LowerU K n) // R (paramOf u)} =
      Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ R v} := by
  refine Nat.card_eq_of_bijective
    (fun u => ⟨paramOf u.1, paramOf_ucond hK u.1, u.2⟩) ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    have h' : paramOf u = paramOf v := congrArg Subtype.val h
    have := paramOf_injective hK h'
    subst this
    rfl
  · rintro ⟨⟨a, b, c, d⟩, hv, hR⟩
    refine ⟨⟨ofParam hK hv, ?_⟩, ?_⟩
    · rw [paramOf_ofParam hK hv]
      exact hR
    · apply Subtype.ext
      exact paramOf_ofParam hK hv

theorem card_LowerU_eq {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card ↥(LowerU K n) =
      Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2} := by
  calc Nat.card ↥(LowerU K n) = Nat.card {u : ↥(LowerU K n) // True} :=
        (Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))).symm
    _ = Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ True} :=
        card_subtype_param hK (fun _ => True)
    _ = Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun v => by simp))

end Param

@[expose] def EE (n : ℕ) (a b c d : K) : K :=
  d * (b * (a ^ 2 ^ n * c + b ^ 2 ^ n) + c * d) * d ^ 2 ^ n

section Norm

variable [Finite K] [CharP K 2]

@[expose] def Eu (n : ℕ) (u : ↥(LowerU K n)) : K :=
  loMat u 3 0 * (loMat u 2 0 * loMat u 3 1 + loMat u 2 1 * loMat u 3 0) * loMat u 3 0 ^ 2 ^ n

theorem Eu_eq {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(LowerU K n)) :
    Eu n u = EE n (paramOf u).1 (paramOf u).2.1 (paramOf u).2.2.1 (paramOf u).2.2.2 := by
  unfold Eu EE
  rw [loMat_eq_uMat hK u]
  simp [uMat]

theorem EE_pow {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {a b c d : K} (h : UCond n a b c d) :
    EE n a b c d ^ 2 ^ n = EE n a b c d := by
  obtain ⟨h1, h2⟩ := h
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold EE
  simp only [mul_pow, add_pow_char_pow, pow_pow_of_card hK, h1]
  linear_combination (-(d * d ^ 2 ^ n * c)) * h2 +
    (d * d ^ 2 ^ n * c * (d ^ 2 ^ n - a ^ 2 ^ n * b)) * hchar

theorem Eu_pow {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(LowerU K n)) :
    Eu n u ^ 2 ^ n = Eu n u := by
  rw [Eu_eq hK u]
  exact EE_pow hK (paramOf_ucond hK u)

theorem EE_ne_zero_iff {n : ℕ} (a b c d : K) :
    EE n a b c d ≠ 0 ↔ d ≠ 0 ∧ c * (a ^ 2 ^ n * b + d) + b * b ^ 2 ^ n ≠ 0 := by
  have hq : (2 : ℕ) ^ n ≠ 0 := by positivity
  have e : EE n a b c d = d ^ 2 ^ n * d * (c * (a ^ 2 ^ n * b + d) + b * b ^ 2 ^ n) := by
    unfold EE
    ring
  rw [e]
  simp only [ne_eq, mul_eq_zero, not_or, pow_eq_zero_iff hq]
  tauto

end Norm

section Model

variable [Finite K] [CharP K 2]

theorem add_ne_self_iff_ne_zero (x y : K) : x + y ≠ y ↔ x ≠ 0 := by
  constructor
  · intro h hx
    apply h
    rw [hx, zero_add]
  · intro hx h
    apply hx
    linear_combination h

theorem shift_fix_iff {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (a b d : K) :
    (d + a ^ 2 ^ n * b) ^ 2 ^ n = d + a ^ 2 ^ n * b ↔
      d + d ^ 2 ^ n = a ^ 2 ^ n * b + a * b ^ 2 ^ n := by
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [add_pow_char_pow, mul_pow, pow_pow_of_card hK]
  constructor
  · intro h
    linear_combination h + (d - a * b ^ 2 ^ n) * hchar
  · intro h
    linear_combination (-1 : K) * h + (d ^ 2 ^ n - a ^ 2 ^ n * b) * hchar

@[expose] def shiftE (n : ℕ) : K × K × K × K ≃ K × K × K × K where
  toFun v := (v.1, v.2.1, v.2.2.1, v.2.2.2 + v.1 ^ 2 ^ n * v.2.1)
  invFun v := (v.1, v.2.1, v.2.2.1, v.2.2.2 + v.1 ^ 2 ^ n * v.2.1)
  left_inv v := by
    obtain ⟨a, b, c, d⟩ := v
    simp [add_assoc, CharTwo.add_self_eq_zero]
  right_inv v := by
    obtain ⟨a, b, c, d⟩ := v
    simp [add_assoc, CharTwo.add_self_eq_zero]

theorem shift_iff {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (a b c d : K) :
    (UCond n a b c d ∧ EE n a b c d ≠ 0) ↔
      (((c ^ 2 ^ n = c ∧ (d + a ^ 2 ^ n * b) ^ 2 ^ n = d + a ^ 2 ^ n * b) ∧
        c * (d + a ^ 2 ^ n * b) + b * b ^ 2 ^ n ≠ 0) ∧ d + a ^ 2 ^ n * b ≠ a ^ 2 ^ n * b) := by
  rw [EE_ne_zero_iff, shift_fix_iff hK, add_ne_self_iff_ne_zero]
  unfold UCond
  have e1 : a ^ 2 ^ n * b + d = d + a ^ 2 ^ n * b := add_comm _ _
  rw [e1]
  tauto

theorem card_model [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧
        EE n v.1 v.2.1 v.2.2.1 v.2.2.2 ≠ 0} =
      ∑ a : K, ∑ b : K, ∑ c : K, ∑ t : K,
        (if ((c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0) ∧
            t ≠ a ^ 2 ^ n * b then 1 else 0) := by
  have e1 : Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧
        EE n v.1 v.2.1 v.2.2.1 v.2.2.2 ≠ 0} =
      Nat.card {w : K × K × K × K // ((w.2.2.1 ^ 2 ^ n = w.2.2.1 ∧ w.2.2.2 ^ 2 ^ n = w.2.2.2) ∧
        w.2.2.1 * w.2.2.2 + w.2.1 * w.2.1 ^ 2 ^ n ≠ 0) ∧ w.2.2.2 ≠ w.1 ^ 2 ^ n * w.2.1} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (shiftE n) ?_)
    rintro ⟨a, b, c, d⟩
    exact shift_iff hK a b c d
  rw [e1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]

end Model

section Fibres

variable [Finite K] [CharP K 2]

@[expose] noncomputable def Acount [Fintype K] (n : ℕ) (b t : K) : ℕ :=
  ∑ a : K, if t ≠ a ^ 2 ^ n * b then 1 else 0

@[expose] noncomputable def ecount (K : Type) [Field K] [Fintype K] (n : ℕ) : ℕ :=
  ∑ c : K, if c ^ 2 ^ n = c ∧ c ≠ 0 then 1 else 0

@[expose] noncomputable def Mcount [Fintype K] (n : ℕ) (N : K) : ℕ :=
  ∑ c : K, ∑ t : K, if (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + N ≠ 0 then 1 else 0

theorem Acount_add_one [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {b : K} (hb : b ≠ 0)
    (t : K) : Acount n b t + 1 = (2 ^ n) ^ 2 := by
  have hcard : Fintype.card K = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hone : (∑ a : K, if t = a ^ 2 ^ n * b then (1 : ℕ) else 0) = 1 := by
    rw [Finset.sum_eq_single ((t * b⁻¹) ^ 2 ^ n)]
    · have h0 : ((t * b⁻¹) ^ 2 ^ n) ^ 2 ^ n * b = t := by
        rw [pow_pow_of_card hK, inv_mul_cancel_right₀ hb]
      rw [if_pos h0.symm]
    · intro a _ ha
      split_ifs with h
      · exfalso
        apply ha
        have h1 : a ^ 2 ^ n = t * b⁻¹ := by rw [h, mul_inv_cancel_right₀ hb]
        calc a = (a ^ 2 ^ n) ^ 2 ^ n := (pow_pow_of_card hK a).symm
          _ = (t * b⁻¹) ^ 2 ^ n := by rw [h1]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsplit : ∀ a : K, ((if t ≠ a ^ 2 ^ n * b then (1 : ℕ) else 0) +
      (if t = a ^ 2 ^ n * b then (1 : ℕ) else 0)) = 1 := by
    intro a
    by_cases h : t = a ^ 2 ^ n * b <;> simp [h]
  unfold Acount
  calc (∑ a : K, if t ≠ a ^ 2 ^ n * b then (1 : ℕ) else 0) + 1
      = (∑ a : K, if t ≠ a ^ 2 ^ n * b then (1 : ℕ) else 0) +
          ∑ a : K, if t = a ^ 2 ^ n * b then (1 : ℕ) else 0 := by rw [hone]
    _ = ∑ a : K, ((if t ≠ a ^ 2 ^ n * b then (1 : ℕ) else 0) +
          (if t = a ^ 2 ^ n * b then (1 : ℕ) else 0)) := by rw [Finset.sum_add_distrib]
    _ = ∑ a : K, (1 : ℕ) := Finset.sum_congr rfl (fun a _ => hsplit a)
    _ = (2 ^ n) ^ 2 := by simp [hcard]

theorem Acount_zero [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (t : K) :
    Acount n 0 t = if t = 0 then 0 else (2 ^ n) ^ 2 := by
  have hcard : Fintype.card K = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  unfold Acount
  by_cases ht : t = 0
  · simp [ht]
  · simp [ht, hcard]

theorem ecount_add_one [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    ecount K n + 1 = 2 ^ n := by
  have h := sum_fixed_eq hK
  have hQ : (2 : K) ^ 0 = 1 := by simp
  have hsplit : ∀ c : K, ((if c ^ 2 ^ n = c ∧ c ≠ 0 then (1 : ℕ) else 0) +
      (if c = 0 then (1 : ℕ) else 0)) = if c ^ 2 ^ n = c then (1 : ℕ) else 0 := by
    intro c
    by_cases hc : c = 0
    · subst hc
      have hq : (2 : ℕ) ^ n ≠ 0 := by positivity
      simp [zero_pow hq]
    · simp [hc]
  unfold ecount
  calc (∑ c : K, if c ^ 2 ^ n = c ∧ c ≠ 0 then (1 : ℕ) else 0) + 1
      = (∑ c : K, if c ^ 2 ^ n = c ∧ c ≠ 0 then (1 : ℕ) else 0) +
          ∑ c : K, if c = 0 then (1 : ℕ) else 0 := by simp
    _ = ∑ c : K, ((if c ^ 2 ^ n = c ∧ c ≠ 0 then (1 : ℕ) else 0) +
          (if c = 0 then (1 : ℕ) else 0)) := by rw [Finset.sum_add_distrib]
    _ = ∑ c : K, if c ^ 2 ^ n = c then (1 : ℕ) else 0 := Finset.sum_congr rfl (fun c _ => hsplit c)
    _ = 2 ^ n := h

theorem sum_unique_t [Fintype K] {n : ℕ} {c N : K} (hc : c ^ 2 ^ n = c) (hN : N ^ 2 ^ n = N)
    (hN0 : N ≠ 0) :
    (∑ t : K, if t ^ 2 ^ n = t ∧ c * t + N = 0 then (1 : ℕ) else 0) =
      if c ≠ 0 then 1 else 0 := by
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hc0 : c = 0
  · subst hc0
    simp [hN0]
  · rw [Finset.sum_eq_single (N * c⁻¹)]
    · have hfix : (N * c⁻¹) ^ 2 ^ n = N * c⁻¹ := by
        rw [mul_pow, inv_pow, hN, hc]
      have hval : c * (N * c⁻¹) = N := by
        rw [← mul_assoc, mul_comm c N, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
      have hsum : c * (N * c⁻¹) + N = 0 := by
        rw [hval, CharTwo.add_self_eq_zero]
      have hcond : (N * c⁻¹) ^ 2 ^ n = N * c⁻¹ ∧ c * (N * c⁻¹) + N = 0 := ⟨hfix, hsum⟩
      rw [if_pos hcond, if_pos (show c ≠ 0 from hc0)]
    · intro t _ ht
      split_ifs with h
      · exfalso
        apply ht
        obtain ⟨_, h2⟩ := h
        have h3 : c * t = N := by linear_combination h2 + (-N) * hchar
        rw [eq_mul_inv_iff_mul_eq₀ hc0]
        linear_combination h3
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem per_c [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {c N : K}
    (hc : c ^ 2 ^ n = c) (hN : N ^ 2 ^ n = N) (hN0 : N ≠ 0) :
    (∑ t : K, if (t ^ 2 ^ n = t) ∧ c * t + N ≠ 0 then (1 : ℕ) else 0) +
      (if c ≠ 0 then 1 else 0) = 2 ^ n := by
  have hsplit : ∀ t : K, (if (t ^ 2 ^ n = t) ∧ c * t + N ≠ 0 then (1 : ℕ) else 0) +
      (if t ^ 2 ^ n = t ∧ c * t + N = 0 then 1 else 0) = if t ^ 2 ^ n = t then 1 else 0 := by
    intro t
    by_cases h1 : t ^ 2 ^ n = t <;> by_cases h2 : c * t + N = 0 <;> simp [h1, h2]
  rw [← sum_unique_t hc hN hN0, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun t _ => hsplit t)]
  exact sum_fixed_eq hK

theorem Mcount_add_ecount [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {N : K}
    (hN : N ^ 2 ^ n = N) (hN0 : N ≠ 0) : Mcount n N + ecount K n = (2 ^ n) ^ 2 := by
  have hM : Mcount n N = ∑ c : K, (if c ^ 2 ^ n = c then
      (∑ t : K, if (t ^ 2 ^ n = t) ∧ c * t + N ≠ 0 then (1 : ℕ) else 0) else 0) := by
    unfold Mcount
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases hc : c ^ 2 ^ n = c <;> simp [hc]
  have hsplit : ∀ c : K, (if c ^ 2 ^ n = c then
      (∑ t : K, if (t ^ 2 ^ n = t) ∧ c * t + N ≠ 0 then (1 : ℕ) else 0) else 0) +
      (if c ^ 2 ^ n = c ∧ c ≠ 0 then 1 else 0) = if c ^ 2 ^ n = c then 2 ^ n else 0 := by
    intro c
    by_cases hc : c ^ 2 ^ n = c
    · simp only [hc, true_and, if_true]
      exact per_c hK hc hN hN0
    · simp [hc]
  have he : ecount K n = ∑ c : K, (if c ^ 2 ^ n = c ∧ c ≠ 0 then (1 : ℕ) else 0) := rfl
  rw [hM, he, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun c _ => hsplit c)]
  have hfin : (∑ c : K, if c ^ 2 ^ n = c then 2 ^ n else 0) =
      2 ^ n * ∑ c : K, if c ^ 2 ^ n = c then (1 : ℕ) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases hc : c ^ 2 ^ n = c <;> simp [hc]
  rw [hfin, sum_fixed_eq hK, pow_two]

theorem sum_reorder {f : K → K → K → K → ℕ} [Fintype K] :
    ∑ a : K, ∑ b : K, ∑ c : K, ∑ t : K, f a b c t =
      ∑ b : K, ∑ c : K, ∑ t : K, ∑ a : K, f a b c t := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]

theorem card_model_sum [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧
        EE n v.1 v.2.1 v.2.2.1 v.2.2.2 ≠ 0} =
      ∑ b : K, ∑ c : K, ∑ t : K,
        (if (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0 then Acount n b t
          else 0) := by
  rw [card_model hK, sum_reorder]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ =>
    Finset.sum_congr rfl (fun t _ => ?_)))
  by_cases h : (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0
  · simp [h, Acount]
  · simp [h]

theorem g_zero [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    (∑ c : K, ∑ t : K, if (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + 0 * 0 ^ 2 ^ n ≠ 0 then
        Acount n 0 t else 0) = (2 ^ n) ^ 2 * ecount K n * ecount K n := by
  have hpt : ∀ c t : K, (if (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + 0 * 0 ^ 2 ^ n ≠ 0 then
      Acount n 0 t else 0) = (2 ^ n) ^ 2 * ((if c ^ 2 ^ n = c ∧ c ≠ 0 then 1 else 0) *
        (if t ^ 2 ^ n = t ∧ t ≠ 0 then 1 else 0)) := by
    intro c t
    rw [Acount_zero hK]
    by_cases hc : c = 0 <;> by_cases ht : t = 0 <;> simp [hc, ht] <;>
      by_cases h1 : c ^ 2 ^ n = c <;> by_cases h2 : t ^ 2 ^ n = t <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun t _ => hpt c t))]
  have hsum : (∑ c : K, ∑ t : K, (2 ^ n) ^ 2 * ((if c ^ 2 ^ n = c ∧ c ≠ 0 then 1 else 0) *
        (if t ^ 2 ^ n = t ∧ t ≠ 0 then 1 else 0))) =
      (2 ^ n) ^ 2 * ((∑ c : K, if c ^ 2 ^ n = c ∧ c ≠ 0 then 1 else 0) *
        (∑ t : K, if t ^ 2 ^ n = t ∧ t ≠ 0 then 1 else 0)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
  rw [hsum, mul_assoc]
  rfl

theorem g_ne [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {b : K} (hb : b ≠ 0) :
    (∑ c : K, ∑ t : K, if (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0 then
        Acount n b t else 0) = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - ecount K n) := by
  have hN : (b * b ^ 2 ^ n) ^ 2 ^ n = b * b ^ 2 ^ n := by
    rw [mul_pow, pow_pow_of_card hK, mul_comm]
  have hN0 : b * b ^ 2 ^ n ≠ 0 := mul_ne_zero hb (pow_ne_zero _ hb)
  have hM := Mcount_add_ecount hK hN hN0
  have hA : ∀ t : K, Acount n b t = (2 ^ n) ^ 2 - 1 := fun t => by
    have := Acount_add_one hK hb t
    omega
  have h1 : (∑ c : K, ∑ t : K, if (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0 then
        Acount n b t else 0) =
      ∑ c : K, ∑ t : K, if (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0 then
        (2 ^ n) ^ 2 - 1 else 0 := by
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun t _ => ?_))
    by_cases h : (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0 <;>
      simp [h, hA t]
  have h2 : (∑ c : K, ∑ t : K, if (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0 then
        (2 ^ n) ^ 2 - 1 else 0) = ((2 ^ n) ^ 2 - 1) * Mcount n (b * b ^ 2 ^ n) := by
    unfold Mcount
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : (c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t) ∧ c * t + b * b ^ 2 ^ n ≠ 0 <;> simp [h]
  rw [h1, h2]
  congr 1
  omega

theorem card_model_formula [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧
        EE n v.1 v.2.1 v.2.2.1 v.2.2.2 ≠ 0} =
      (2 ^ n) ^ 2 * ecount K n * ecount K n +
        ((2 ^ n) ^ 2 - 1) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - ecount K n)) := by
  have hcard : Fintype.card K = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [card_model_sum hK, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))]
  congr 1
  · exact g_zero hK
  · rw [Finset.sum_congr rfl (fun b hb => g_ne hK (Finset.ne_of_mem_erase hb))]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hcard]

end Fibres

section Final

variable [Finite K] [CharP K 2]

theorem card_UCond [Fintype K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2} = (2 ^ n) ^ 6 := by
  have hcard : Fintype.card K = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have e1 : Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2} =
      Nat.card {w : K × K × K × K // w.2.2.1 ^ 2 ^ n = w.2.2.1 ∧ w.2.2.2 ^ 2 ^ n = w.2.2.2} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (shiftE n) ?_)
    rintro ⟨a, b, c, d⟩
    show UCond n a b c d ↔ (c ^ 2 ^ n = c ∧ (d + a ^ 2 ^ n * b) ^ 2 ^ n = d + a ^ 2 ^ n * b)
    unfold UCond
    rw [shift_fix_iff hK]
  have hcc : (∑ c : K, ∑ t : K, if c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t then (1 : ℕ) else 0) =
      (2 ^ n) ^ 2 := by
    have hpt : ∀ c : K, (∑ t : K, if c ^ 2 ^ n = c ∧ t ^ 2 ^ n = t then (1 : ℕ) else 0) =
        if c ^ 2 ^ n = c then 2 ^ n else 0 := by
      intro c
      by_cases hc : c ^ 2 ^ n = c
      · simp only [hc, true_and, if_true]
        exact sum_fixed_eq hK
      · simp [hc]
    rw [Finset.sum_congr rfl (fun c _ => hpt c)]
    have hfin : (∑ c : K, if c ^ 2 ^ n = c then 2 ^ n else 0) =
        2 ^ n * ∑ c : K, if c ^ 2 ^ n = c then (1 : ℕ) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      by_cases hc : c ^ 2 ^ n = c <;> simp [hc]
    rw [hfin, sum_fixed_eq hK, pow_two]
  rw [e1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type, hcc, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard]
  ring

theorem card_LowerU {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card ↥(LowerU K n) = (2 ^ n) ^ 6 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [card_LowerU_eq hK, card_UCond hK]

theorem odd_formula {n : ℕ} (hn : n ≠ 0) (e : ℕ) (he : e + 1 = 2 ^ n) :
    Odd ((e + 1) ^ 2 * e * e + (e ^ 2 + 2 * e) * ((e ^ 2 + 2 * e) * (e ^ 2 + e + 1))) := by
  have hev : Even (e + 1) := by
    rw [he]
    exact Nat.even_pow.mpr ⟨even_two, hn⟩
  have hO : Odd e := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hev)
  rw [← ZMod.natCast_eq_one_iff_odd]
  have he' : (e : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hO
  push_cast
  rw [he']
  decide

theorem odd_card_Eu_ne_zero {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    Odd (Nat.card {u : ↥(LowerU K n) // Eu n u ≠ 0}) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hn : n ≠ 0 := by
    rintro rfl
    have := one_lt_two_pow_of_card hK
    simp at this
  have he := ecount_add_one (K := K) hK
  have key : Nat.card {u : ↥(LowerU K n) // Eu n u ≠ 0} =
      (2 ^ n) ^ 2 * ecount K n * ecount K n +
        ((2 ^ n) ^ 2 - 1) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - ecount K n)) := by
    calc Nat.card {u : ↥(LowerU K n) // Eu n u ≠ 0}
        = Nat.card {u : ↥(LowerU K n) //
            EE n (paramOf u).1 (paramOf u).2.1 (paramOf u).2.2.1 (paramOf u).2.2.2 ≠ 0} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun u => by rw [Eu_eq hK u]))
      _ = Nat.card {v : K × K × K × K // UCond n v.1 v.2.1 v.2.2.1 v.2.2.2 ∧
            EE n v.1 v.2.1 v.2.2.1 v.2.2.2 ≠ 0} :=
          card_subtype_param hK (fun v => EE n v.1 v.2.1 v.2.2.1 v.2.2.2 ≠ 0)
      _ = _ := card_model_formula hK
  rw [key]
  generalize hE : ecount K n = e at he ⊢
  rw [← he]
  have h1 : (e + 1) ^ 2 - 1 = e ^ 2 + 2 * e := by
    rw [show (e + 1) ^ 2 = (e ^ 2 + 2 * e) + 1 by ring, Nat.add_sub_cancel]
  have h2 : (e + 1) ^ 2 - e = e ^ 2 + e + 1 := by
    rw [show (e + 1) ^ 2 = (e ^ 2 + e + 1) + e by ring, Nat.add_sub_cancel]
  rw [h1, h2]
  exact odd_formula hn e he

theorem odd_cast_eq_one {k : Type} [Field k] [CharP k 2] {m : ℕ} (hm : Odd m) :
    (m : k) = 1 := by
  obtain ⟨j, rfl⟩ := hm
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  push_cast
  rw [h2]
  ring

theorem pow_sub_one_algebraMap {k : Type} [Field k] [Algebra K k] {n : ℕ} (hq : 1 < 2 ^ n)
    {x : K} (hx : x ^ 2 ^ n = x) :
    (algebraMap K k x) ^ (2 ^ n - 1) = if x = 0 then 0 else 1 := by
  have hne : 2 ^ n - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq
  by_cases h0 : x = 0
  · subst h0
    rw [map_zero, zero_pow hne, if_pos rfl]
  · have h1 : x ^ (2 ^ n - 1) = 1 := by
      have h2 : x ^ (2 ^ n - 1) * x = x := by
        rw [← pow_succ, Nat.sub_add_cancel (le_of_lt hq), hx]
      exact mul_right_cancel₀ h0 (h2.trans (one_mul x).symm)
    rw [← map_pow, h1, map_one, if_neg h0]

theorem sum_Eu_pow_eq_one {n : ℕ} [Fintype ↥(LowerU K n)] (hK : Nat.card K = (2 ^ n) ^ 2)
    {k : Type} [Field k] [Algebra K k] [CharP k 2] :
    ∑ u : ↥(LowerU K n), (algebraMap K k (Eu n u)) ^ (2 ^ n - 1) = 1 := by
  have hq : 1 < 2 ^ n := one_lt_two_pow_of_card hK
  have hpt : ∀ u : ↥(LowerU K n), (algebraMap K k (Eu n u)) ^ (2 ^ n - 1) =
      if Eu n u = 0 then 0 else 1 := fun u => pow_sub_one_algebraMap hq (Eu_pow hK u)
  rw [Finset.sum_congr rfl (fun u _ => hpt u)]
  have hcount : (∑ u : ↥(LowerU K n), (if Eu n u = 0 then (0 : k) else 1)) =
      ((Nat.card {u : ↥(LowerU K n) // Eu n u ≠ 0} : ℕ) : k) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun u _ => ?_)
    by_cases h : Eu n u = 0 <;> simp [h]
  rw [hcount]
  exact odd_cast_eq_one (odd_card_Eu_ne_zero hK)

end Final

end CFSG.HardMathSupport.U4FF
