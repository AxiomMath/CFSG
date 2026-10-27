module

public import CFSG.ClassicalInvolution.Q3.TL4MF163Gam
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.L2

open CFSG CFSG.GorensteinWalter
open Matrix.ProjGenLinGroup
open scoped MatrixGroups

section PGL

variable {K : Type} [Field K]

theorem pgl2_comm_of_sq_eq (h2 : (2 : K) ≠ 0) {c y : PGL(2, K)} (hc2 : c ^ 2 ≠ 1)
    (hc4 : c ^ 4 = 1) (hy : y ^ 2 = c ^ 2) : y * c = c * y := by
  have hy2 : y ^ 2 ≠ 1 := hy ▸ hc2
  have hy4 : y ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hy, ← pow_mul]
    exact hc4
  induction c using Matrix.ProjGenLinGroup.induction_on with | mk C => ?_
  induction y using Matrix.ProjGenLinGroup.induction_on with | mk Y => ?_
  have hA2 := MF163.not_scalar_of_sq hc2
  have hA4 := MF163.scalar_of_pow_four hc4
  have hB2 := MF163.not_scalar_of_sq hy2
  have hB4 := MF163.scalar_of_pow_four hy4
  rw [← map_pow, ← map_pow, mk_eq_mk_iff] at hy
  obtain ⟨u, hu⟩ := hy
  set A : Matrix (Fin 2) (Fin 2) K := (C : Matrix (Fin 2) (Fin 2) K) with hAdef
  set B : Matrix (Fin 2) (Fin 2) K := (Y : Matrix (Fin 2) (Fin 2) K) with hBdef
  have hrel : (u : K) • (B * B) = A * A := by
    have := congrArg Units.val hu
    rw [Units.val_mul, MF163.scalar_val, Matrix.mul_smul, Matrix.mul_one, sq, sq,
      Units.val_mul, Units.val_mul] at this
    exact this
  have htA := MF163.trace_ne_zero hA2
  have htB := MF163.trace_ne_zero hB2
  have eA := MF163.two_mul_self_eq_smul hA2 hA4
  have eB := MF163.two_mul_self_eq_smul hB2 hB4
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hN : ((u : K) * B.trace) • MF163.twoTraceless B = A.trace • MF163.twoTraceless A := by
    rw [← eA, ← hrel, mul_smul, ← eB, smul_comm]
  have hN' : MF163.twoTraceless B =
      (((u : K) * B.trace)⁻¹ * A.trace) • MF163.twoTraceless A := by
    rw [mul_smul, ← hN, smul_smul, inv_mul_cancel₀ (mul_ne_zero hu0 htB), one_smul]
  set κ : K := ((u : K) * B.trace)⁻¹ * A.trace with hκ
  have h2B : (2 : K) • B = κ • ((2 : K) • A - A.trace • (1 : Matrix (Fin 2) (Fin 2) K)) +
      B.trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : MF163.twoTraceless B = (2 : K) • B - B.trace • (1 : Matrix (Fin 2) (Fin 2) K) :=
      rfl
    have h3 : MF163.twoTraceless A = (2 : K) • A - A.trace • (1 : Matrix (Fin 2) (Fin 2) K) :=
      rfl
    rw [← h3, ← hN', h1]
    abel
  have hcomm2 : A * ((2 : K) • B) = ((2 : K) • B) * A := by
    rw [h2B]
    simp only [mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hcomm : A * B = B * A := by
    rw [Matrix.mul_smul, Matrix.smul_mul] at hcomm2
    exact smul_right_injective _ h2 hcomm2
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact hcomm.symm

theorem pgl2_eq_or_eq_inv_of_sq_eq (h2 : (2 : K) ≠ 0) {c y : PGL(2, K)} (hc2 : c ^ 2 ≠ 1)
    (hc4 : c ^ 4 = 1) (hy : y ^ 2 = c ^ 2) : y = c ∨ y = c⁻¹ := by
  have hyc := pgl2_comm_of_sq_eq h2 hc2 hc4 hy
  have hcy : Commute y c := hyc
  have hb : y * c⁻¹ * c = c * (y * c⁻¹) := by
    rw [inv_mul_cancel_right, ← mul_assoc, ← hyc, mul_inv_cancel_right]
  have hbb : y * c⁻¹ * (y * c⁻¹) = 1 := by
    have h1 : y * c⁻¹ * (y * c⁻¹) = y ^ 2 * (c ^ 2)⁻¹ := by
      have := (hcy.inv_right).mul_mul_mul_comm y c⁻¹
      rw [sq, sq, mul_inv_rev]
      calc y * c⁻¹ * (y * c⁻¹) = y * (c⁻¹ * y) * c⁻¹ := by group
        _ = y * (y * c⁻¹) * c⁻¹ := by rw [(hcy.inv_right).eq]
        _ = y * y * (c⁻¹ * c⁻¹) := by group
    rw [h1, hy, mul_inv_cancel]
  rcases MF163.pgl2_eq_of_comm h2 hc2 hc4 hb hbb with h | h
  · left
    exact mul_inv_eq_one.mp h
  · right
    rw [mul_inv_eq_iff_eq_mul] at h
    rw [h, ← pow_succ, show c ^ (2 + 1) = c⁻¹ * c ^ 4 by group, hc4, mul_one]

theorem exists_toPGL_eq (hsq : IsSquare (2 : K)) {c : PGL(2, K)} (hc2 : c ^ 2 ≠ 1)
    (hc4 : c ^ 4 = 1) :
    ∃ s : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K,
      Matrix.ProjectiveSpecialLinearGroup.toPGL s = c := by
  induction c using Matrix.ProjGenLinGroup.induction_on with | mk C => ?_
  have hA2 := MF163.not_scalar_of_sq hc2
  have hA4 := MF163.scalar_of_pow_four hc4
  have htr := MF163.trace_sq_eq hA2 hA4
  have ht0 := MF163.trace_ne_zero hA2
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    have h2 : (2 : K) ≠ 0 := by
      intro h0
      apply ht0
      have : (C : Matrix (Fin 2) (Fin 2) K).trace ^ 2 = 0 := by rw [htr, h0, zero_mul]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    exact h2 hr
  set d : K := (C : Matrix (Fin 2) (Fin 2) K).trace / r with hd
  have hd0 : d ≠ 0 := div_ne_zero ht0 hr0
  have hdd : d * d = (C : Matrix (Fin 2) (Fin 2) K).det := by
    have h2 : (2 : K) ≠ 0 := by rw [hr]; exact mul_ne_zero hr0 hr0
    rw [hd, div_mul_div_comm, ← sq, htr, ← hr]
    field_simp
  have hdet : (d⁻¹ • (C : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hdd, inv_pow, sq, inv_mul_cancel₀
      (mul_ne_zero hd0 hd0)]
  let S : Matrix.SpecialLinearGroup (Fin 2) K := ⟨d⁻¹ • (C : Matrix (Fin 2) (Fin 2) K), hdet⟩
  refine ⟨QuotientGroup.mk S, ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, mk_eq_mk_iff]
  refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
  rw [Units.val_mul, MF163.scalar_val, Matrix.mul_smul, Matrix.mul_one]
  show d • (d⁻¹ • (C : Matrix (Fin 2) (Fin 2) K)) = C
  rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]

end PGL

theorem isSquare_two {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : Even f) (hF : Nat.card F = p ^ f) : IsSquare (2 : F) := by
  have := Fintype.ofFinite F
  rw [FiniteField.isSquare_two_iff, ← Nat.card_eq_fintype_card, hF]
  obtain ⟨k, rfl⟩ := hf
  obtain ⟨m, hm⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
  have h1 : p ^ (k + k) = (2 * m + 1) ^ 2 := by rw [← hm]; ring
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
  have h2 : (2 * m + 1) ^ 2 = 8 * j + 1 := by nlinarith [hj]
  rw [h1, h2]
  omega

section Gamma

variable {F : Type} [Field F] [Finite F]

theorem exists_right_eq_one (hK : IsOddPrimePower (Nat.card F))
    (ρ : QuaternionGroup 2 →* PGammaL2 F) :
    ∃ g : QuaternionGroup 2, g ^ 2 = QuaternionGroup.a 2 ∧ (ρ g).right = 1 := by
  have : IsCyclic (F ≃+* F) := MF163.ringAut_isCyclic F hK
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  have hr2 : ∀ g : QuaternionGroup 2, g ^ 2 = QuaternionGroup.a 2 →
      (ρ g).right * (ρ g).right = 1 := by
    intro g hg
    rw [← SemidirectProduct.mul_right, ← map_mul, ← sq, hg, MF163.right_a_two hK]
  by_cases h1 : (ρ (QuaternionGroup.a 1)).right = 1
  · exact ⟨QuaternionGroup.a 1, by decide, h1⟩
  by_cases h2 : (ρ (QuaternionGroup.xa 0)).right = 1
  · exact ⟨QuaternionGroup.xa 0, by decide, h2⟩
  refine ⟨QuaternionGroup.a 1 * QuaternionGroup.xa 0, by decide, ?_⟩
  have he := MF163.eq_of_mul_self_eq_one (hr2 _ (by decide)) (hr2 _ (by decide)) h1 h2
  rw [map_mul, SemidirectProduct.mul_right, he, ← SemidirectProduct.mul_right, ← map_mul,
    ← sq, show (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 by decide,
    MF163.right_a_two hK]

end Gamma

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.L2
