module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GroupTheory

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  {T : V →ₗ[k] V}

theorem exists_mem_sub_one_eq_of_mem [FiniteDimensional k V]
    (hker : LinearMap.ker (T - (1 : V →ₗ[k] V)) = ⊥) {U : Submodule k V}
    (hU : ∀ u ∈ U, T u ∈ U) {w : V} (hw : w ∈ U) :
    ∃ u ∈ U, T u - u = w := by
  let f : U →ₗ[k] U :=
    { toFun := fun u => ⟨T (u : V) - (u : V), U.sub_mem (hU (u : V) u.2) u.2⟩
      map_add' := fun u v => Subtype.ext (by
        simp only [Subtype.coe_mk, AddMemClass.coe_add, map_add, add_sub_add_comm])
      map_smul' := fun c u => Subtype.ext (by
        simp only [Subtype.coe_mk, SetLike.val_smul, map_smul, smul_sub]
        rfl) }
  have hf : Function.Injective f := by
    intro u v huv
    have h0 : f (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h0' : T ((u : V) - (v : V)) - ((u : V) - (v : V)) = 0 :=
      congrArg Subtype.val h0
    have hmem : (u : V) - (v : V) ∈ LinearMap.ker (T - (1 : V →ₗ[k] V)) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply]
      exact h0'
    rw [hker, Submodule.mem_bot] at hmem
    exact Subtype.ext (sub_eq_zero.mp hmem)
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hf ⟨w, hw⟩
  exact ⟨u, u.2, by simpa [f] using congrArg Subtype.val hu⟩

end CFSG.GroupTheory

end
