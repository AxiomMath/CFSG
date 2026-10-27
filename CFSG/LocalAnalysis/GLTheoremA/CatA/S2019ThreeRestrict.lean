module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.Algebra.Module.Submodule.Ker

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019.Three

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

@[expose] def stabSub (W : Submodule F V) : Subgroup (LinearMap.GeneralLinearGroup F V) where
  carrier := {g | (∀ w ∈ W, (g : V →ₗ[F] V) w ∈ W) ∧
    ∀ w ∈ W, ((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w ∈ W}
  mul_mem' {a b} ha hb := by
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [Units.val_mul, Module.End.mul_apply]
      exact ha.1 _ (hb.1 w hw)
    · rw [mul_inv_rev, Units.val_mul, Module.End.mul_apply]
      exact hb.2 _ (ha.2 w hw)
  one_mem' := ⟨fun w hw => hw, fun w hw => hw⟩
  inv_mem' {a} ha := ⟨ha.2, fun w hw => by rw [inv_inv]; exact ha.1 w hw⟩

@[expose] noncomputable def restrictGL (W : Submodule F V) :
    stabSub W →* LinearMap.GeneralLinearGroup F W where
  toFun g :=
    { val := (g.1 : V →ₗ[F] V).restrict g.2.1
      inv := ((g.1⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V).restrict g.2.2
      val_inv := by
        ext w
        simp only [Module.End.mul_apply, LinearMap.restrict_coe_apply, Module.End.one_apply]
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply]
      inv_val := by
        ext w
        simp only [Module.End.mul_apply, LinearMap.restrict_coe_apply, Module.End.one_apply]
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply] }
  map_one' := by
    ext w
    rfl
  map_mul' a b := by
    ext w
    rfl

theorem restrictGL_apply (W : Submodule F V) (g : stabSub W) (w : W) :
    (((restrictGL W g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) w : V) =
      ((g : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w := rfl

theorem restrictGL_eq_one_iff (W : Submodule F V) (g : stabSub W) :
    restrictGL W g = 1 ↔ ∀ w ∈ W, ((g : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w = w := by
  constructor
  · intro h w hw
    have := congrArg (fun k : LinearMap.GeneralLinearGroup F W => ((k : W →ₗ[F] W) ⟨w, hw⟩ : V)) h
    simpa [restrictGL_apply] using this
  · intro h
    ext w
    exact h w w.2

theorem eq_one_of_fix_eigen (h2 : (2 : F) ≠ 0) {c g : LinearMap.GeneralLinearGroup F V}
    (hc : c * c = 1)
    (hp : ∀ w ∈ LinearMap.ker ((c : V →ₗ[F] V) - 1), (g : V →ₗ[F] V) w = w)
    (hm : ∀ w ∈ LinearMap.ker ((c : V →ₗ[F] V) + 1), (g : V →ₗ[F] V) w = w) : g = 1 := by
  have hcc : ∀ v, (c : V →ₗ[F] V) ((c : V →ₗ[F] V) v) = v := fun v => by
    have := congrArg (fun k : LinearMap.GeneralLinearGroup F V => (k : V →ₗ[F] V) v) hc
    simpa using this
  apply Units.ext
  ext v
  have hv1 : v + (c : V →ₗ[F] V) v ∈ LinearMap.ker ((c : V →ₗ[F] V) - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_add, hcc]
    abel
  have hv2 : v - (c : V →ₗ[F] V) v ∈ LinearMap.ker ((c : V →ₗ[F] V) + 1) := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_sub, hcc]
    abel
  have e : v = (2 : F)⁻¹ • (v + (c : V →ₗ[F] V) v) + (2 : F)⁻¹ • (v - (c : V →ₗ[F] V) v) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul F v, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [Units.val_one, Module.End.one_apply]
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, hp _ hv1, hm _ hv2, ← e]

theorem sq_mem_frattini {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) (x : P) :
    x ^ 2 ∈ frattini P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hP.isNilpotent
  unfold frattini Order.radical
  rw [Subgroup.mem_iInf]
  intro M
  rw [Subgroup.mem_iInf]
  intro hM
  exact Subgroup.sq_mem_of_index_two ((IsPGroup.isCoatom_iff_index_eq_prime hP).mp hM) x

theorem frattini_ne_top {P : Type*} [Group P] [Finite P] [Nontrivial P] : frattini P ≠ ⊤ := by
  intro h
  have := frattini_nongenerating (K := (⊥ : Subgroup P)) (by rw [h, sup_top_eq])
  exact bot_ne_top this

end CFSG.LocalAnalysis.GLTheoremA.S2019.Three
