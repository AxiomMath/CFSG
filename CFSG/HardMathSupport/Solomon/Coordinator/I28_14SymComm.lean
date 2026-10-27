module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymModel
public import Mathlib.RingTheory.PiTensorProduct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal Module

variable {m : ℕ} {H : Type} [AddCommGroup H] [Module (ZMod 2) H] (M : SymModel m H)

theorem i28_14_symModel_fix_center (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j)
    (c : LinearMap.GeneralLinearGroup (ZMod 2) H)
    (hc : c * M.ψ (Equiv.swap i j) = M.ψ (Equiv.swap i j) * c) :
    (c : H →ₗ[ZMod 2] H) (M.γ (pairVec i j)) = M.γ (pairVec i j) := by
  obtain ⟨φ, h, hφ, -, heq⟩ := i28_14_symModel_swap_tv M hm hij
  obtain ⟨x, hx⟩ := exists_apply_eq_one hφ
  set a := M.γ (pairVec i j) with ha
  have hne : a ≠ 0 := i28_14_symModel_center_ne M hm hij
  have e := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) H =>
    (g : H →ₗ[ZMod 2] H) x) hc
  simp only [heq, Units.val_mul, Module.End.mul_apply, tv_apply, map_add, hx,
    one_smul] at e
  have e' : (c : H →ₗ[ZMod 2] H) a = φ ((c : H →ₗ[ZMod 2] H) x) • a := by
    have := add_left_cancel (a := (c : H →ₗ[ZMod 2] H) x) e
    exact this
  have hca : (c : H →ₗ[ZMod 2] H) a ≠ 0 := by
    intro h0
    apply hne
    have := congrArg (fun v => ((c⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) H) :
      H →ₗ[ZMod 2] H) v) h0
    simpa [← Module.End.mul_apply, ← Units.val_mul] using this
  rcases zmod2_eq_zero_or_one (φ ((c : H →ₗ[ZMod 2] H) x)) with h0 | h1
  · exact absurd (by rw [e', h0, zero_smul]) hca
  · rw [e', h1, one_smul]

theorem i28_14_sym_pairVec_self (i : Fin m) : pairVec i i = 0 :=
  Subtype.ext (funext fun z => by
    simp only [coe_pairVec, Pi.add_apply]
    exact add_self_zmod2 _)

theorem i28_14_sym_eq_sum_pairVec (i₀ : Fin m) (y : sumZero m) :
    y = ∑ j, (y : Fin m → ZMod 2) j • pairVec i₀ j := by
  apply Subtype.ext
  funext z
  have hy := y.2
  rw [mem_sumZero] at hy
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, coe_pairVec, Pi.add_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hy, zero_mul, zero_add]
  simp [Pi.single_apply]

theorem i28_14_symModel_eq_one_of_comm (hm : 3 ≤ m) (c : LinearMap.GeneralLinearGroup (ZMod 2) H)
    (hc : ∀ σ : Equiv.Perm (Fin m), c * M.ψ σ = M.ψ σ * c) : c = 1 := by
  have i₀ : Fin m := ⟨0, by omega⟩
  have hfix : ∀ j : Fin m, (c : H →ₗ[ZMod 2] H) (M.γ (pairVec i₀ j)) = M.γ (pairVec i₀ j) := by
    intro j
    by_cases hj : i₀ = j
    · rw [← hj, i28_14_sym_pairVec_self, map_zero, map_zero]
    · exact i28_14_symModel_fix_center M hm hj c (hc _)
  apply tv_ext
  intro v
  obtain ⟨y, rfl⟩ := M.surj v
  conv_lhs => rw [i28_14_sym_eq_sum_pairVec i₀ y]
  conv_rhs => rw [i28_14_sym_eq_sum_pairVec i₀ y]
  simp only [map_sum, map_smul, hfix]
  rfl

end CFSG.HardMathSupport.Solomon.Coordinator
