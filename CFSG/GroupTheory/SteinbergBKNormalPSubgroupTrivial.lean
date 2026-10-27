module

public import CFSG.GroupTheory.SteinbergBKLinearFixedVector
public import CFSG.GroupTheory.SteinbergBKRepresentationSum

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem normal_p_subgroup_irreducible_trivial {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {P : Subgroup G} [P.Normal] (hP : IsPGroup p P) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hirr : ∀ W : Submodule (ZMod p) V,
      (∀ g : G, ∀ w ∈ W, (ρ g : V →ₗ[ZMod p] V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∀ x ∈ P, ρ x = 1 := by
  have hinv : ∀ g : G, ∀ w ∈ fixedSubspace ρ P, (ρ g : V →ₗ[ZMod p] V) w ∈ fixedSubspace ρ P := by
    intro g w hw x hx
    have hx' : g⁻¹ * x * g ∈ P := by
      simpa only [inv_inv] using Subgroup.Normal.conj_mem inferInstance x hx g⁻¹
    rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul,
      show x * g = g * (g⁻¹ * x * g) by group, map_mul, Units.val_mul, Module.End.mul_apply,
      hw _ hx']
  obtain ⟨v, hv0, hv⟩ := p_group_linear_fixed_vector hP (ρ.comp P.subtype)
  rcases hirr _ hinv with h | h
  · exfalso
    apply hv0
    rw [← Submodule.mem_bot (ZMod p), ← h]
    exact fun x hx => hv ⟨x, hx⟩
  · intro x hx
    refine Units.ext (LinearMap.ext fun w => ?_)
    have hw : w ∈ fixedSubspace ρ P := h ▸ Submodule.mem_top
    exact hw x hx

end CFSG.GroupTheory.SteinbergBK
