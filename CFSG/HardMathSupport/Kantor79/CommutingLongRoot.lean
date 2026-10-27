module

public import CFSG.HardMathSupport.Kantor79.LongRoot

public section

namespace CFSG.HardMathSupport.Kantor79

open QuadraticMap LinearMap Module

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

theorem IsLongRootElement.sub_one_eq_rootEnd {Q : QuadraticForm K E} {x : E ≃ₗ[K] E}
    (hx : IsLongRootElement Q x) :
    ∃ a b : E, Q a = 0 ∧ Q b = 0 ∧ polar Q a b = 0 ∧
      (x : E →ₗ[K] E) - 1 = rootEnd Q a b := by
  unfold IsLongRootElement at hx
  obtain ⟨a, b, hQa, hQb, hab, -, -, -, hform⟩ := hx
  refine ⟨a, b, hQa, hQb, hab, ?_⟩
  ext v
  rw [LinearMap.sub_apply, Module.End.one_apply, rootEnd_apply]
  have hxapp : (x : E →ₗ[K] E) v = x v := rfl
  rw [hxapp, hform v]
  abel

private theorem one_add_one_end : ((1 : E →ₗ[K] E) + 1) = 0 := by
  ext v
  simp only [LinearMap.add_apply, Module.End.one_apply]
  calc v + v = (2 : K) • v := (two_smul K v).symm
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_smul]

private theorem neg_one_end : ((-1 : E →ₗ[K] E)) = 1 := by
  ext v
  simp only [LinearMap.neg_apply, Module.End.one_apply]
  rw [neg_eq_iff_add_eq_zero]
  calc v + v = (2 : K) • v := (two_smul K v).symm
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_smul]

theorem movedSpace_le_orthogonal_of_commute {Q : QuadraticForm K E} {x y : E ≃ₗ[K] E}
    (hx : IsLongRootElement Q x) (hy : IsLongRootElement Q y)
    (hcomm : x * y = y * x) (hdisj : Disjoint (movedSpace x) (movedSpace y)) :
    movedSpace y ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (movedSpace x) := by
  obtain ⟨a, b, hQa, hQb, hab, hp⟩ := hx.sub_one_eq_rootEnd
  set p : E →ₗ[K] E := (x : E →ₗ[K] E) - 1 with hpdef
  set q : E →ₗ[K] E := (y : E →ₗ[K] E) - 1 with hqdef
  have hp' : p = rootEnd Q a b := hpdef.symm.trans hp
  have hpq : p * q = q * p := by
    have hxy : (x : E →ₗ[K] E) * (y : E →ₗ[K] E) = (y : E →ₗ[K] E) * (x : E →ₗ[K] E) :=
      congrArg (fun e : E ≃ₗ[K] E => (e : E →ₗ[K] E)) hcomm
    have hxsplit : (x : E →ₗ[K] E) = 1 + p := by
      rw [hpdef, sub_eq_add_neg, neg_one_end]
      calc (x : E →ₗ[K] E) = (x : E →ₗ[K] E) + 0 := (add_zero _).symm
        _ = (x : E →ₗ[K] E) + (1 + 1) := by rw [one_add_one_end]
        _ = 1 + ((x : E →ₗ[K] E) + 1) := by abel
    have hysplit : (y : E →ₗ[K] E) = 1 + q := by
      rw [hqdef, sub_eq_add_neg, neg_one_end]
      calc (y : E →ₗ[K] E) = (y : E →ₗ[K] E) + 0 := (add_zero _).symm
        _ = (y : E →ₗ[K] E) + (1 + 1) := by rw [one_add_one_end]
        _ = 1 + ((y : E →ₗ[K] E) + 1) := by abel
    have h' : (1 + p) * (1 + q) = (1 + q) * (1 + p) := by
      simpa [hxsplit, hysplit] using hxy
    have h2 : (1 + p) * (1 + q) - (1 + q) * (1 + p) = p * q - q * p := by
      simp only [add_mul, mul_add, one_mul, mul_one]
      abel
    have h3 : p * q - q * p = 0 := by
      rw [← h2, h', sub_self]
    exact sub_eq_zero.mp h3
  intro u hu
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  obtain ⟨s, rfl⟩ := hv
  obtain ⟨t, rfl⟩ := hu
  have hself : QuadraticMap.polarBilin Q (p s) (q t) = polar Q s (p (q t)) := by
    rw [hp']
    exact rootEnd_self_adjoint Q a b s (q t)
  have hcomm_apply : p (q t) = q (p t) := by
    have := congrArg (fun f : E →ₗ[K] E => f t) hpq
    simpa [Module.End.mul_apply] using this
  have hpq_mem : p (q t) ∈ movedSpace x ⊓ movedSpace y := by
    refine ⟨?_, ?_⟩
    · exact ⟨q t, rfl⟩
    · rw [hcomm_apply]
      exact ⟨p t, rfl⟩
  have hzero : p (q t) = 0 := by
    have hle : movedSpace x ⊓ movedSpace y ≤ (⊥ : Submodule K E) :=
      disjoint_iff_inf_le.mp hdisj
    exact (Submodule.mem_bot K).mp (hle hpq_mem)
  rw [hself, hzero]
  exact polar_zero_right Q s

end CFSG.HardMathSupport.Kantor79
