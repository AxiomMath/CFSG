module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {H : Type} [Group H] [Finite H]

@[expose] def zjVec (y z v₁ v₂ : H) (n : ℕ) : H :=
  y ^ (n &&& 1) * z ^ ((n >>> 1) &&& 1) * v₁ ^ ((n >>> 2) &&& 1) * v₂ ^ ((n >>> 3) &&& 1)

open Classical in
@[expose] noncomputable def zjCode (y z v₁ v₂ u : H) : ℕ :=
  if h : ∃ n, n < 16 ∧ zjVec y z v₁ v₂ n = u then Nat.find h else 0

private def zjB {M : Type*} [One M] [Mul M] (w : M) (b : Bool) : M := if b then w else 1

private theorem zjB_xor {M : Type*} [Monoid M] {w : M} (hw : w * w = 1) (b b' : Bool) :
    zjB w (b ^^ b') = zjB w b * zjB w b' := by
  cases b <;> cases b' <;> simp [zjB, hw]

private theorem pow_and_one {M : Type*} [Monoid M] (u : M) (n : ℕ) :
    u ^ (n &&& 1) = zjB u (n.testBit 0) := by
  have h : n &&& 1 = if n.testBit 0 then 1 else 0 := by
    rw [Nat.and_one_is_mod, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
  rw [h]
  cases n.testBit 0 <;> simp [zjB]

private theorem pow_shift_and_one {M : Type*} [Monoid M] (u : M) (n i : ℕ) :
    u ^ ((n >>> i) &&& 1) = zjB u (n.testBit i) := by
  have h : (n >>> i) &&& 1 = if n.testBit i then 1 else 0 := by
    have e1 : (n >>> i) &&& 1 = (n >>> i) % 2 := Nat.and_one_is_mod _
    have e2 : (n >>> i) % 2 = if (n >>> i).testBit 0 then 1 else 0 := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one (n >>> i) with h | h <;> simp [h]
    have e3 : (n >>> i).testBit 0 = n.testBit i := by
      simp only [Nat.testBit_shiftRight, Nat.add_zero]
    rw [e1, e2, e3]
  rw [h]
  cases n.testBit i <;> simp [zjB]

private theorem zjB_prod_xor {W : Type*} [CommGroup W] (a b c d : W)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) (hd : d * d = 1) (n m : ℕ) :
    zjB a ((n ^^^ m).testBit 0) * zjB b ((n ^^^ m).testBit 1) *
        zjB c ((n ^^^ m).testBit 2) * zjB d ((n ^^^ m).testBit 3) =
      (zjB a (n.testBit 0) * zjB b (n.testBit 1) * zjB c (n.testBit 2) *
          zjB d (n.testBit 3)) *
        (zjB a (m.testBit 0) * zjB b (m.testBit 1) * zjB c (m.testBit 2) *
          zjB d (m.testBit 3)) := by
  simp only [Nat.testBit_xor, zjB_xor ha, zjB_xor hb, zjB_xor hc, zjB_xor hd]
  ac_rfl

private theorem vec_xor_comm {W : Type*} [CommGroup W] (y z v₁ v₂ : W)
    (hy : y * y = 1) (hz : z * z = 1) (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1) (n m : ℕ) :
    y ^ ((n ^^^ m) &&& 1) * z ^ (((n ^^^ m) >>> 1) &&& 1) * v₁ ^ (((n ^^^ m) >>> 2) &&& 1) *
        v₂ ^ (((n ^^^ m) >>> 3) &&& 1) =
      (y ^ (n &&& 1) * z ^ ((n >>> 1) &&& 1) * v₁ ^ ((n >>> 2) &&& 1) * v₂ ^ ((n >>> 3) &&& 1)) *
        (y ^ (m &&& 1) * z ^ ((m >>> 1) &&& 1) * v₁ ^ ((m >>> 2) &&& 1) *
          v₂ ^ ((m >>> 3) &&& 1)) := by
  simp only [pow_and_one, pow_shift_and_one]
  exact zjB_prod_xor y z v₁ v₂ hy hz hv₁ hv₂ n m

private theorem bits_determine (n : ℕ) (hn : n < 16) :
    n = (n &&& 1) + 2 * ((n >>> 1) &&& 1) + 4 * ((n >>> 2) &&& 1) +
      8 * ((n >>> 3) &&& 1) := by
  interval_cases n <;> decide

private theorem and_one_lt_two (n : ℕ) : n &&& 1 < 2 := by
  rw [Nat.and_one_is_mod]
  exact Nat.mod_lt _ (by norm_num)

private theorem shift_and_one_lt_two (n i : ℕ) : (n >>> i) &&& 1 < 2 := by
  rw [Nat.and_one_is_mod]
  exact Nat.mod_lt _ (by norm_num)

private theorem xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  calc a = a ^^^ 0 := (Nat.xor_zero a).symm
    _ = a ^^^ (a ^^^ b) := by rw [h]
    _ = a ^^^ a ^^^ b := (Nat.xor_assoc a a b).symm
    _ = 0 ^^^ b := by rw [Nat.xor_self]
    _ = b := Nat.zero_xor b

private theorem and_three_eq_zero_left (n : ℕ) (h3 : n &&& 3 = 0) :
    n &&& 1 = 0 ∧ (n >>> 1) &&& 1 = 0 := by
  constructor
  · have h := (Nat.and_assoc n 3 1).symm
    rw [show (3 : ℕ) &&& 1 = 1 from by decide, h3, Nat.zero_and] at h
    exact h
  · have h := Nat.shiftRight_and_distrib (a := n) (b := 3) (i := 1)
    rw [h3] at h
    rw [show (3 : ℕ) >>> 1 = 1 from by decide, Nat.zero_shiftRight] at h
    exact h.symm

namespace ZJBase

variable {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}
variable (h : ZJBase Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem y_mem : y ∈ Y := by
  rw [h.Y_eq]
  exact Subgroup.mem_sup_left (by rw [h.V_eq]; exact Subgroup.subset_closure (by simp))

theorem z_mem : z ∈ Y := by
  rw [h.Y_eq]
  exact Subgroup.mem_sup_left (by rw [h.V_eq]; exact Subgroup.subset_closure (by simp))

theorem v₁_mem : v₁ ∈ Y := by
  rw [h.Y_eq]
  exact Subgroup.mem_sup_right (by rw [h.V'_eq]; exact Subgroup.subset_closure (by simp))

theorem v₂_mem : v₂ ∈ Y := by
  rw [h.Y_eq]
  exact Subgroup.mem_sup_right (by rw [h.V'_eq]; exact Subgroup.subset_closure (by simp))

private theorem yz_pow_eq_one {a b : ℕ} (ha : a < 2) (hb : b < 2)
    (he : y ^ a * z ^ b = 1) : a = 0 ∧ b = 0 := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · simp
  · simp at he; exact absurd he h.z_ne_one
  · simp at he; exact absurd he h.y_ne_one
  · simp only [pow_one] at he
    exfalso
    exact h.y_ne_z
      (by rw [eq_inv_of_mul_eq_one_left he, inv_eq_of_mul_eq_one_right (h.Y_sq z h.z_mem)])

private theorem v_pow_eq_one {c d : ℕ} (hc : c < 2) (hd : d < 2)
    (he : v₁ ^ c * v₂ ^ d = 1) : c = 0 ∧ d = 0 := by
  have hc' : c = 0 ∨ c = 1 := by omega
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases hc' with rfl | rfl <;> rcases hd' with rfl | rfl
  · simp
  · simp at he; exact absurd he h.v₂_ne_one
  · simp at he; exact absurd he h.v₁_ne_one
  · simp only [pow_one] at he
    exfalso
    exact h.v₁_ne_v₂
      (by rw [eq_inv_of_mul_eq_one_left he, inv_eq_of_mul_eq_one_right (h.Y_sq v₂ h.v₂_mem)])

theorem Y_normal : Y.Normal := by
  exact ⟨fun x hx g => h.normal_Y g x hx⟩

theorem Y_comm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
  intro a ha b hb
  exact h.Q_comm a (h.Y_le_Q ha) b (h.Y_le_Q hb)

theorem vec_mem (n : ℕ) : zjVec y z v₁ v₂ n ∈ Y := by
  simp only [zjVec]
  exact mul_mem (mul_mem (mul_mem (pow_mem h.y_mem _) (pow_mem h.z_mem _))
    (pow_mem h.v₁_mem _)) (pow_mem h.v₂_mem _)

theorem vec_basis : zjVec y z v₁ v₂ 0 = 1 ∧ zjVec y z v₁ v₂ 1 = y ∧ zjVec y z v₁ v₂ 2 = z ∧
    zjVec y z v₁ v₂ 4 = v₁ ∧ zjVec y z v₁ v₂ 8 = v₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [zjVec, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] <;> norm_num

theorem vec_xor {n m : ℕ} (hn : n < 16) (hm : m < 16) :
    zjVec y z v₁ v₂ (n ^^^ m) = zjVec y z v₁ v₂ n * zjVec y z v₁ v₂ m := by
  haveI : IsMulCommutative ↥Y :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (h.Y_comm a.1 a.2 b.1 b.2)
  open scoped IsMulCommutative in
  have key := vec_xor_comm (W := ↥Y) ⟨y, h.y_mem⟩ ⟨z, h.z_mem⟩ ⟨v₁, h.v₁_mem⟩
    ⟨v₂, h.v₂_mem⟩ (Subtype.ext (h.Y_sq y h.y_mem)) (Subtype.ext (h.Y_sq z h.z_mem))
    (Subtype.ext (h.Y_sq v₁ h.v₁_mem)) (Subtype.ext (h.Y_sq v₂ h.v₂_mem)) n m
  have key2 := congrArg Subtype.val key
  simp only [Subgroup.coe_mul, Subgroup.coe_pow] at key2
  simpa only [zjVec] using key2

theorem vec_eq_one {n : ℕ} (hn : n < 16) (h1 : zjVec y z v₁ v₂ n = 1) : n = 0 := by
  let p := y ^ (n &&& 1) * z ^ ((n >>> 1) &&& 1)
  let q := v₁ ^ ((n >>> 2) &&& 1) * v₂ ^ ((n >>> 3) &&& 1)
  have hpq : zjVec y z v₁ v₂ n = p * q := by simp only [zjVec, p, q, mul_assoc]
  have hpV : p ∈ V := by
    refine mul_mem ?_ ?_ <;>
      rw [h.V_eq] <;> exact pow_mem (Subgroup.subset_closure (by simp)) _
  have hqV' : q ∈ V' := by
    refine mul_mem ?_ ?_ <;>
      rw [h.V'_eq] <;> exact pow_mem (Subgroup.subset_closure (by simp)) _
  have hpq1 : p * q = 1 := by rw [← hpq]; exact h1
  have hp_bot : p ∈ V ⊓ V' :=
    ⟨hpV, by
      have hqY : q ∈ Y := mul_mem (pow_mem h.v₁_mem _) (pow_mem h.v₂_mem _)
      rw [eq_inv_of_mul_eq_one_left hpq1, inv_eq_of_mul_eq_one_right (h.Y_sq q hqY)]
      exact hqV'⟩
  rw [h.V_inf_V'] at hp_bot
  have hp1 : p = 1 := Subgroup.mem_bot.mp hp_bot
  have hq1 : q = 1 := by rw [hp1, one_mul] at hpq1; exact hpq1
  obtain ⟨ha0, hb0⟩ := h.yz_pow_eq_one (and_one_lt_two n) (shift_and_one_lt_two n 1)
    (by simpa [p] using hp1)
  obtain ⟨hc0, hd0⟩ := h.v_pow_eq_one (shift_and_one_lt_two n 2) (shift_and_one_lt_two n 3)
    (by simpa [q] using hq1)
  have hdet := bits_determine n hn
  omega

theorem vec_inj {n m : ℕ} (hn : n < 16) (hm : m < 16)
    (e : zjVec y z v₁ v₂ n = zjVec y z v₁ v₂ m) : n = m := by
  have hx : n ^^^ m < 16 := Nat.xor_lt_two_pow (show n < 2 ^ 4 from hn) (show m < 2 ^ 4 from hm)
  have h1 : zjVec y z v₁ v₂ (n ^^^ m) = 1 := by
    rw [h.vec_xor hn hm, ← e]
    exact h.Y_sq _ (h.vec_mem n)
  exact xor_eq_zero (h.vec_eq_one hx h1)

theorem vec_surj {u : H} (hu : u ∈ Y) : ∃ n, n < 16 ∧ zjVec y z v₁ v₂ n = u := by
  let W : Subgroup H :=
    { carrier := {u | ∃ n, n < 16 ∧ zjVec y z v₁ v₂ n = u}
      one_mem' := ⟨0, by norm_num, h.vec_basis.1⟩
      mul_mem' := by
        rintro a b ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
        exact ⟨n ^^^ m, Nat.xor_lt_two_pow (show n < 2 ^ 4 from hn) (show m < 2 ^ 4 from hm),
          h.vec_xor hn hm⟩
      inv_mem' := by
        rintro a ⟨n, hn, rfl⟩
        exact ⟨n, hn, (inv_eq_of_mul_eq_one_right (h.Y_sq _ (h.vec_mem n))).symm⟩ }
  have hV : V ≤ W := by
    rw [h.V_eq, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨1, by norm_num, h.vec_basis.2.1⟩
    · exact ⟨2, by norm_num, h.vec_basis.2.2.1⟩
  have hV' : V' ≤ W := by
    rw [h.V'_eq, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨4, by norm_num, h.vec_basis.2.2.2.1⟩
    · exact ⟨8, by norm_num, h.vec_basis.2.2.2.2⟩
  have hY : Y ≤ W := by rw [h.Y_eq]; exact sup_le hV hV'
  exact hY hu

theorem vec_mem_V_iff {n : ℕ} (hn : n < 16) : zjVec y z v₁ v₂ n ∈ V ↔ n < 4 := by
  constructor
  · intro hV
    let p := y ^ (n &&& 1) * z ^ ((n >>> 1) &&& 1)
    let q := v₁ ^ ((n >>> 2) &&& 1) * v₂ ^ ((n >>> 3) &&& 1)
    have hpq : zjVec y z v₁ v₂ n = p * q := by simp only [zjVec, p, q, mul_assoc]
    have hpV : p ∈ V := by
      refine mul_mem ?_ ?_ <;>
        rw [h.V_eq] <;> exact pow_mem (Subgroup.subset_closure (by simp)) _
    have hqV' : q ∈ V' := by
      refine mul_mem ?_ ?_ <;>
        rw [h.V'_eq] <;> exact pow_mem (Subgroup.subset_closure (by simp)) _
    have hpY : p ∈ Y := mul_mem (pow_mem h.y_mem _) (pow_mem h.z_mem _)
    have hqV : q ∈ V := by
      have hqeq : q = p⁻¹ * zjVec y z v₁ v₂ n := by
        calc q = 1 * q := (one_mul q).symm
          _ = p⁻¹ * p * q := by rw [inv_mul_cancel]
          _ = p⁻¹ * (p * q) := mul_assoc _ _ _
          _ = p⁻¹ * zjVec y z v₁ v₂ n := by rw [← hpq]
      rw [hqeq, inv_eq_of_mul_eq_one_right (h.Y_sq p hpY)]
      exact mul_mem hpV hV
    have hqbot : q ∈ V ⊓ V' := ⟨hqV, hqV'⟩
    rw [h.V_inf_V'] at hqbot
    have hq1 : q = 1 := Subgroup.mem_bot.mp hqbot
    obtain ⟨hc0, hd0⟩ := h.v_pow_eq_one (shift_and_one_lt_two n 2) (shift_and_one_lt_two n 3)
      (by simpa [q] using hq1)
    have hdet := bits_determine n hn
    have ha := and_one_lt_two n
    have hb := shift_and_one_lt_two n 1
    omega
  · intro hn4
    have hc : (n >>> 2) &&& 1 = 0 := by
      rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 2 = 4 from by norm_num,
        Nat.div_eq_of_lt hn4]
      simp
    have hd : (n >>> 3) &&& 1 = 0 := by
      rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 3 = 8 from by norm_num,
        Nat.div_eq_of_lt (by omega)]
      simp
    have hv : zjVec y z v₁ v₂ n = y ^ (n &&& 1) * z ^ ((n >>> 1) &&& 1) := by
      simp only [zjVec, hc, hd, pow_zero, mul_one]
    rw [hv]
    exact mul_mem
      (pow_mem (by rw [h.V_eq]; exact Subgroup.subset_closure (by simp)) _)
      (pow_mem (by rw [h.V_eq]; exact Subgroup.subset_closure (by simp)) _)

theorem vec_mem_V'_iff {n : ℕ} (hn : n < 16) : zjVec y z v₁ v₂ n ∈ V' ↔ n &&& 3 = 0 := by
  constructor
  · intro hV'
    let p := y ^ (n &&& 1) * z ^ ((n >>> 1) &&& 1)
    let q := v₁ ^ ((n >>> 2) &&& 1) * v₂ ^ ((n >>> 3) &&& 1)
    have hpq : zjVec y z v₁ v₂ n = p * q := by simp only [zjVec, p, q, mul_assoc]
    have hpV : p ∈ V := by
      refine mul_mem ?_ ?_ <;>
        rw [h.V_eq] <;> exact pow_mem (Subgroup.subset_closure (by simp)) _
    have hqV' : q ∈ V' := by
      refine mul_mem ?_ ?_ <;>
        rw [h.V'_eq] <;> exact pow_mem (Subgroup.subset_closure (by simp)) _
    have hqY : q ∈ Y := mul_mem (pow_mem h.v₁_mem _) (pow_mem h.v₂_mem _)
    have hpV' : p ∈ V' := by
      have hpeq : p = zjVec y z v₁ v₂ n * q⁻¹ := by
        calc p = p * 1 := (mul_one p).symm
          _ = p * (q * q⁻¹) := by rw [mul_inv_cancel]
          _ = (p * q) * q⁻¹ := (mul_assoc _ _ _).symm
          _ = zjVec y z v₁ v₂ n * q⁻¹ := by rw [← hpq]
      rw [hpeq, inv_eq_of_mul_eq_one_right (h.Y_sq q hqY)]
      exact mul_mem hV' hqV'
    have hpbot : p ∈ V ⊓ V' := ⟨hpV, hpV'⟩
    rw [h.V_inf_V'] at hpbot
    have hp1 : p = 1 := Subgroup.mem_bot.mp hpbot
    obtain ⟨ha0, hb0⟩ := h.yz_pow_eq_one (and_one_lt_two n) (shift_and_one_lt_two n 1)
      (by simpa [p] using hp1)
    have hdet := bits_determine n hn
    have h4 : 4 ∣ n := by
      have hh := hdet
      rw [ha0, hb0] at hh
      refine ⟨((n >>> 2) &&& 1) + 2 * ((n >>> 3) &&& 1), ?_⟩
      conv_lhs => rw [hh]
      ring
    rw [show (3 : ℕ) = 2 ^ 2 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_zero_of_dvd h4
  · intro h3
    obtain ⟨ha0, hb0⟩ := and_three_eq_zero_left n h3
    have hv : zjVec y z v₁ v₂ n = v₁ ^ ((n >>> 2) &&& 1) * v₂ ^ ((n >>> 3) &&& 1) := by
      simp only [zjVec, ha0, hb0, pow_zero, one_mul]
    rw [hv]
    exact mul_mem
      (pow_mem (by rw [h.V'_eq]; exact Subgroup.subset_closure (by simp)) _)
      (pow_mem (by rw [h.V'_eq]; exact Subgroup.subset_closure (by simp)) _)

theorem code_vec {n : ℕ} (hn : n < 16) : zjCode y z v₁ v₂ (zjVec y z v₁ v₂ n) = n := by
  classical
  have hex : ∃ k, k < 16 ∧ zjVec y z v₁ v₂ k = zjVec y z v₁ v₂ n := ⟨n, hn, rfl⟩
  rw [zjCode, dif_pos hex]
  exact h.vec_inj (Nat.find_spec hex).1 hn (Nat.find_spec hex).2

theorem vec_code {u : H} (hu : u ∈ Y) : zjVec y z v₁ v₂ (zjCode y z v₁ v₂ u) = u := by
  classical
  obtain ⟨n, hn, rfl⟩ := h.vec_surj hu
  rw [h.code_vec hn]

theorem code_lt {u : H} (hu : u ∈ Y) : zjCode y z v₁ v₂ u < 16 := by
  classical
  have hex := h.vec_surj hu
  rw [zjCode, dif_pos hex]
  exact (Nat.find_spec hex).1

theorem code_one : zjCode y z v₁ v₂ (1 : H) = 0 := by
  rw [← h.vec_basis.1]
  exact h.code_vec (by norm_num)

theorem code_mul {u u' : H} (hu : u ∈ Y) (hu' : u' ∈ Y) :
    zjCode y z v₁ v₂ (u * u') = zjCode y z v₁ v₂ u ^^^ zjCode y z v₁ v₂ u' := by
  obtain ⟨n, hn, rfl⟩ := h.vec_surj hu
  obtain ⟨m, hm, rfl⟩ := h.vec_surj hu'
  rw [← h.vec_xor hn hm, h.code_vec (Nat.xor_lt_two_pow (show n < 2 ^ 4 from hn)
    (show m < 2 ^ 4 from hm)), h.code_vec hn, h.code_vec hm]

theorem eq_of_code_eq {u u' : H} (hu : u ∈ Y) (hu' : u' ∈ Y)
    (e : zjCode y z v₁ v₂ u = zjCode y z v₁ v₂ u') : u = u' := by
  rw [← h.vec_code hu, ← h.vec_code hu', e]

theorem code_lt_four_iff {u : H} (hu : u ∈ Y) : zjCode y z v₁ v₂ u < 4 ↔ u ∈ V := by
  have hh := h.vec_mem_V_iff (h.code_lt hu)
  rw [h.vec_code hu] at hh
  exact hh.symm

theorem code_and_three_iff {u : H} (hu : u ∈ Y) :
    zjCode y z v₁ v₂ u &&& 3 = 0 ↔ u ∈ V' := by
  have hh := h.vec_mem_V'_iff (h.code_lt hu)
  rw [h.vec_code hu] at hh
  exact hh.symm

end ZJBase

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
