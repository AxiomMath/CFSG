module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10U38Mat
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniPlane

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.U38

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Solomon.Coordinator

variable {K : Type} [Field K]

theorem u38_two_eq_zero (h : UnitaryFieldData 2 3 K) : (2 : K) = 0 := by
  have := h.charP
  exact CharP.cast_eq_zero K 2

theorem u38_bar_eq_pow (h : UnitaryFieldData 2 3 K) (x : K) : h.bar x = x ^ 8 := by
  rw [UnitaryFieldData.bar_apply]
  norm_num

theorem exists_omega (h : UnitaryFieldData 2 3 K) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  have := h.finite
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, h.card]
    norm_num
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard]; norm_num)
  refine ⟨(u : K), ?_⟩
  have hu3 : (u : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : K) ≠ 1 := by
    intro e
    have : u = 1 := Units.ext e
    rw [this, orderOf_one] at hu
    norm_num at hu
  have hprod : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = 0 := by
    linear_combination hu3
  exact (mul_eq_zero.1 hprod).resolve_left (sub_ne_zero.2 hu1)

section Omega

variable (h : UnitaryFieldData 2 3 K) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)

include hω in
theorem u38_omega_pow_three : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω

include h hω in
theorem u38_omega_ne_one : ω ≠ 1 := by
  rintro rfl
  have := u38_two_eq_zero h
  have h3 : (3 : K) = 0 := by linear_combination hω
  have h1 : (1 : K) = 0 := by linear_combination h3 - this
  exact one_ne_zero h1

include hω in
theorem u38_bar_omega : h.bar ω = ω ^ 2 := by
  rw [u38_bar_eq_pow h]
  have := u38_omega_pow_three hω
  calc ω ^ 8 = (ω ^ 3) ^ 2 * ω ^ 2 := by ring
    _ = ω ^ 2 := by rw [this]; ring

theorem u38_mem_U {g : GL (Fin 3) K}
    (hg : ((g : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (g : Matrix (Fin 3) (Fin 3) K) = 1) :
    g ∈ primeFormUnitary h (idGram K 3) := by
  rw [mem_primeFormUnitary]
  simpa [idGram] using hg

@[expose] def uA : primeFormUnitary h (idGram K 3) :=
  ⟨glA ω hω (u38_two_eq_zero h),
    u38_mem_U h (unitary_mA ω hω (u38_two_eq_zero h) h.bar (u38_bar_omega h hω))⟩

@[expose] def uP : primeFormUnitary h (idGram K 3) :=
  ⟨glP, u38_mem_U h (unitary_mP ω hω (u38_two_eq_zero h) h.bar (u38_bar_omega h hω))⟩

@[expose] def uF : primeFormUnitary h (idGram K 3) :=
  ⟨glF ω hω (u38_two_eq_zero h),
    u38_mem_U h (unitary_mF ω hω (u38_two_eq_zero h) h.bar (u38_bar_omega h hω))⟩

@[expose] def uQ : primeFormUnitary h (idGram K 3) :=
  ⟨glQ ω hω (u38_two_eq_zero h),
    u38_mem_U h (unitary_mQ ω hω (u38_two_eq_zero h) h.bar (u38_bar_omega h hω))⟩

@[expose] def uR : primeFormUnitary h (idGram K 3) :=
  ⟨glR ω hω (u38_two_eq_zero h),
    u38_mem_U h (unitary_mR ω hω (u38_two_eq_zero h) h.bar (u38_bar_omega h hω))⟩

theorem coe_uA :
    (((uA h hω : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = mA ω :=
  rfl

theorem coe_uP :
    (((uP h hω : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = mP :=
  rfl

theorem coe_uQ :
    (((uQ h hω : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = mQ ω :=
  rfl

theorem coe_uR :
    (((uR h hω : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = mR ω :=
  rfl

@[expose] noncomputable def uω : Kˣ :=
  Units.mk0 ω (fun h0 => by rw [h0] at hω; norm_num at hω)

theorem uA_mul_uP :
    ((uA h hω : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) * (uP h hω : GL (Fin 3) K) =
      (uP h hω : GL (Fin 3) K) * (uA h hω : GL (Fin 3) K) *
        GeneralLinearGroup.scalar (Fin 3) (uω hω) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  change mA ω * mP = mP * mA ω * Matrix.scalar (Fin 3) ω
  rw [mA_mP ω hω (u38_two_eq_zero h), Matrix.scalar_apply]
  ext i j
  simp [Matrix.smul_apply, Matrix.mul_diagonal, mul_comm]

end Omega

end CFSG.HardMathSupport.Solomon.Coordinator.U38
