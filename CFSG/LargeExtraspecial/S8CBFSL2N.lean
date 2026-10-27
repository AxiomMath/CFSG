module

public import CFSG.LargeExtraspecial.S8CBFSL2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Matrix Subgroup
open scoped commutatorElement

variable {K : Type*} [Field K]

theorem exists_eq_smul_one_add_smul_of_commute_nonscalar_two {N g : Matrix (Fin 2) (Fin 2) K}
    (hN : N 0 1 ≠ 0 ∨ N 1 0 ≠ 0 ∨ N 0 0 ≠ N 1 1) (hg : g * N = N * g) :
    ∃ α β : K, g = α • (1 : Matrix (Fin 2) (Fin 2) K) + β • N := by
  have e := fun (i j : Fin 2) => congrFun (congrFun hg i) j
  have hg00 := e 0 0
  have hg01 := e 0 1
  have hg10 := e 1 0
  simp only [mul_apply, Fin.sum_univ_two] at hg00 hg01 hg10
  rcases hN with hb | hc | had
  · refine ⟨g 0 0 - g 0 1 / N 0 1 * N 0 0, g 0 1 / N 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [one_apply] <;> field_simp <;>
      first
      | linear_combination -hg00
      | linear_combination -hg01
  · refine ⟨g 0 0 - g 1 0 / N 1 0 * N 0 0, g 1 0 / N 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [one_apply] <;> field_simp <;>
      first
      | linear_combination -hg00
      | linear_combination -hg10
      | linear_combination hg00
      | linear_combination hg10
  · have had' : N 0 0 - N 1 1 ≠ 0 := sub_ne_zero.mpr had
    refine ⟨g 0 0 - (g 0 0 - g 1 1) / (N 0 0 - N 1 1) * N 0 0,
      (g 0 0 - g 1 1) / (N 0 0 - N 1 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [one_apply] <;> field_simp <;>
      first
      | linear_combination -hg01
      | linear_combination -hg10
      | linear_combination hg01
      | linear_combination hg10
      | ring

theorem exists_eq_smul_of_commute_of_sq_eq_zero_two [CharP K 2]
    {N N' : Matrix (Fin 2) (Fin 2) K} (hN : N 0 1 ≠ 0 ∨ N 1 0 ≠ 0 ∨ N 0 0 ≠ N 1 1)
    (hN2 : N * N = 0) (hN'2 : N' * N' = 0) (hc : N' * N = N * N') : ∃ β : K, N' = β • N := by
  obtain ⟨α, β, rfl⟩ := exists_eq_smul_one_add_smul_of_commute_nonscalar_two hN hc
  refine ⟨β, ?_⟩
  have h2 : (α • (1 : Matrix (Fin 2) (Fin 2) K) + β • N) * (α • 1 + β • N) =
      (α * α) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hN2, smul_zero, add_zero, smul_smul]
    rw [add_assoc, ← add_smul, mul_comm β α, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  rw [h2] at hN'2
  have h00 := congrFun (congrFun hN'2 0) 0
  simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h00
  rw [mul_self_eq_zero.mp h00, zero_smul, zero_add]

theorem sl2_conj_sub_one (g z : SpecialLinearGroup (Fin 2) K) :
    (g : Matrix (Fin 2) (Fin 2) K) * ((z : Matrix (Fin 2) (Fin 2) K) - 1) *
        ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((g * z * g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1 := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one]

variable [CharP K 2]

theorem sl2_sub_one_mul_self {z : SpecialLinearGroup (Fin 2) K} (hz : z * z = 1) :
    ((z : Matrix (Fin 2) (Fin 2) K) - 1) * ((z : Matrix (Fin 2) (Fin 2) K) - 1) = 0 := by
  have hz' : (z : Matrix (Fin 2) (Fin 2) K) * z = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.SpecialLinearGroup.coe_one]
  have h2 : ∀ M : Matrix (Fin 2) (Fin 2) K, M + M = 0 := fun M => by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  calc ((z : Matrix (Fin 2) (Fin 2) K) - 1) * ((z : Matrix (Fin 2) (Fin 2) K) - 1)
      = (z : Matrix (Fin 2) (Fin 2) K) * z + 1 -
        ((z : Matrix (Fin 2) (Fin 2) K) + (z : Matrix (Fin 2) (Fin 2) K)) := by noncomm_ring
    _ = 0 := by rw [hz', h2, h2, sub_zero]

theorem sl2_eq_bot_of_perfect_of_normalizes [Finite K]
    (M T : Subgroup (SpecialLinearGroup (Fin 2) K)) (hM : ⁅M, M⁆ = M) (hT2 : IsPGroup 2 T)
    (hMT : ∀ g ∈ M, ∀ t ∈ T, g * t * g⁻¹ ∈ T) (hT : T ≠ ⊥) : M = ⊥ := by
  classical
  have := Fact.mk Nat.prime_two
  obtain ⟨z, hzT, hz2⟩ : ∃ z ∈ T, orderOf z = 2 := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hT ((Subgroup.card_eq_one).mp (by simpa using hk))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz2, sq] at h
  set N : Matrix (Fin 2) (Fin 2) K := (z : Matrix (Fin 2) (Fin 2) K) - 1 with hNdef
  have hN2 : N * N = 0 := sl2_sub_one_mul_self hzz
  have hNs : N 0 1 ≠ 0 ∨ N 1 0 ≠ 0 ∨ N 0 0 ≠ N 1 1 := by
    rcases sl2_nonscalar_of_ne_one hz1 with h | h | h
    · left; simpa [hNdef] using h
    · right; left; simpa [hNdef] using h
    · right; right
      intro h'
      apply h
      simpa [hNdef] using h'
  have hscale : ∀ g ∈ M, ∃ c : K, (g : Matrix (Fin 2) (Fin 2) K) * N *
      ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = c • N := by
    intro g hg
    have h1 : g * z * g⁻¹ ∈ T := hMT g hg z hzT
    have hcomm := sl2_comm_of_isPGroup T hT2 _ h1 _ hzT
    have hgz : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hzz, mul_one,
        mul_inv_cancel]
    rw [hNdef, sl2_conj_sub_one]
    refine exists_eq_smul_of_commute_of_sq_eq_zero_two hNs hN2 (sl2_sub_one_mul_self hgz) ?_
    have hc' : ((g * z * g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * z =
        z * ((g * z * g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hcomm]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hc']
    abel
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, N i j ≠ 0 := by
    rcases hNs with h | h | h
    · exact ⟨0, 1, h⟩
    · exact ⟨1, 0, h⟩
    · by_cases h0 : N 0 0 = 0
      · exact ⟨1, 1, fun h1 => h (h0.trans h1.symm)⟩
      · exact ⟨0, 0, h0⟩
  let f : SpecialLinearGroup (Fin 2) K → K := fun x =>
    ((x : Matrix (Fin 2) (Fin 2) K) * N *
      ((x⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i₀ j₀ / N i₀ j₀
  have hf : ∀ x ∈ M, (x : Matrix (Fin 2) (Fin 2) K) * N *
      ((x⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = f x • N := by
    intro x hx
    obtain ⟨c, hc⟩ := hscale x hx
    have hfc : f x = c := by
      simp only [f, hc, Matrix.smul_apply, smul_eq_mul]
      field_simp
    rw [hfc, hc]
  have hsmul_inj : ∀ a b : K, a • N = b • N → a = b := by
    intro a b hab
    have := congrFun (congrFun hab i₀) j₀
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hij this
  have hmul : ∀ x ∈ M, ∀ y ∈ M, f (x * y) = f x * f y := by
    intro x hx y hy
    apply hsmul_inj
    rw [← hf _ (M.mul_mem hx hy), _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    calc (x : Matrix (Fin 2) (Fin 2) K) * y * N *
          (((y⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((x⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
        = (x : Matrix (Fin 2) (Fin 2) K) * ((y : Matrix (Fin 2) (Fin 2) K) * N *
            ((y⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
            ((x⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          simp only [Matrix.mul_assoc]
      _ = (f x * f y) • N := by
          rw [hf y hy, Matrix.mul_smul, Matrix.smul_mul, hf x hx, smul_smul, mul_comm]
  have hone : f 1 = 1 := by
    simp only [f, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
    exact div_self hij
  have hinv : ∀ x ∈ M, f x * f x⁻¹ = 1 := by
    intro x hx
    rw [← hmul x hx x⁻¹ (M.inv_mem hx), mul_inv_cancel, hone]
  have hcz : ∀ c ∈ M, f c = 1 → c * z = z * c := by
    intro c hc hfc
    have h1 := hf c hc
    rw [hfc, one_smul] at h1
    apply Subtype.ext
    have h2 : (c : Matrix (Fin 2) (Fin 2) K) * N = N * c := by
      calc (c : Matrix (Fin 2) (Fin 2) K) * N
          = (c : Matrix (Fin 2) (Fin 2) K) * N *
            (((c⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * c) := by
            rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
              Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
        _ = N * c := by rw [← Matrix.mul_assoc, h1]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have h3 : (c : Matrix (Fin 2) (Fin 2) K) * (z : Matrix (Fin 2) (Fin 2) K) =
        (c : Matrix (Fin 2) (Fin 2) K) * N + c := by
      rw [hNdef, Matrix.mul_sub, Matrix.mul_one, sub_add_cancel]
    have h4 : (z : Matrix (Fin 2) (Fin 2) K) * (c : Matrix (Fin 2) (Fin 2) K) =
        N * (c : Matrix (Fin 2) (Fin 2) K) + c := by
      rw [hNdef, Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    rw [h3, h4, h2]
  have hMz : M ≤ centralizer ({z} : Set (SpecialLinearGroup (Fin 2) K)) := by
    rw [← hM, commutator_le]
    intro x hx y hy
    rw [mem_centralizer_singleton_iff]
    have hc : ⁅x, y⁆ ∈ M := hM ▸ commutator_mem_commutator hx hy
    refine hcz _ hc ?_
    rw [commutatorElement_def, hmul _ (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) _
      (M.inv_mem hy), hmul _ (M.mul_mem hx hy) _ (M.inv_mem hx), hmul x hx y hy]
    calc f x * f y * f x⁻¹ * f y⁻¹ = (f x * f x⁻¹) * (f y * f y⁻¹) := by ring
      _ = 1 := by rw [hinv x hx, hinv y hy, one_mul]
  rw [← hM, eq_bot_iff, commutator_le]
  intro x hx y hy
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact sl2_commute_of_commute_ne_one hz1 (mem_centralizer_singleton_iff.mp (hMz hx))
    (mem_centralizer_singleton_iff.mp (hMz hy))

end CFSG.LargeExtraspecial.S8
