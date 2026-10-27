module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.PolyIndep

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

theorem mem_of_forall_sum_pow_map_smul_mem {F k M ι : Type*} [Field F] [Fintype F] [Field k]
    [AddCommGroup M] [Module k M] [Fintype ι] (φ : F →+* k) (N : Submodule k M) (e : ι → ℕ)
    (he : Function.Injective e) (hb : ∀ i, e i < Fintype.card F) (w : ι → M)
    (h : ∀ t : F, ∑ i, φ t ^ e i • w i ∈ N) (i : ι) : w i ∈ N :=
  letI : Module F M := Module.compHom M φ
  let N' : Submodule F M :=
    { carrier := N
      add_mem' := fun hx hy => N.add_mem hx hy
      zero_mem' := N.zero_mem
      smul_mem' := fun c x hx => by
        change φ c • x ∈ N
        exact N.smul_mem (φ c) hx }
  have h' : ∀ t : F, ∑ j, t ^ e j • w j ∈ N' := by
    intro t
    rw [show (∑ j, t ^ e j • w j) = ∑ j, φ t ^ e j • w j from
      Finset.sum_congr rfl fun j _ => by
        change φ (t ^ e j) • w j = φ t ^ e j • w j
        rw [map_pow]]
    simpa [N'] using h t
  mem_of_forall_poly_inj N' e he hb w h' i

end CFSG.LieType.SpecialLinear.ExteriorModel

end
