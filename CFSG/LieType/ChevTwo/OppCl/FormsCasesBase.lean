module

public import CFSG.LieType.ChevTwo.OppCl.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section Semilin

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem semilin_zero {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) : r 0 = 0 :=
  map_zero (AddMonoidHom.mk' (fun v : V => r v) hr.1)

theorem semilin_sub {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) (u v : V) :
    r (u - v) = r u - r v :=
  map_sub (AddMonoidHom.mk' (fun v : V => r v) hr.1) u v

theorem perp_invariant (Φ : ReflForm F V) (Rh : Subgroup (Equiv.Perm V))
    (hiso : ∀ r ∈ Rh, SemiIso Φ r) (U : Submodule F V) (hU : ∀ r ∈ Rh, ∀ v ∈ U, r v ∈ U) :
    ∀ r ∈ Rh, ∀ v ∈ Φ.perp U, r v ∈ Φ.perp U := by
  intro r hr v hv w hw
  obtain ⟨τ, hτ⟩ := hiso r hr
  have hw' : r⁻¹ w ∈ U := hU r⁻¹ (inv_mem hr) w hw
  have hrw : r (r⁻¹ w) = w := r.apply_symm_apply w
  have h1 : Φ.β (r (r⁻¹ w)) (r v) = τ (Φ.β (r⁻¹ w) v) := hτ (r⁻¹ w) v
  rw [hrw] at h1
  rw [h1, hv (r⁻¹ w) hw', map_zero]

end Semilin

section Stab

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem mapsTo_inv [Finite V] (ρ : H →* Module.End F V) (W : Submodule F V) (u : H)
    (hu : ∀ w ∈ W, ρ u w ∈ W) : ∀ w ∈ W, ρ u⁻¹ w ∈ W := by
  have h1 : ∀ z : V, ρ u⁻¹ (ρ u z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  intro w hw
  let f : W → W := fun x => ⟨ρ u (x : V), hu (x : V) x.2⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : ρ u (x : V) = ρ u (y : V) := congrArg Subtype.val hxy
    have h2 := congrArg (ρ u⁻¹) hxy'
    rwa [h1, h1] at h2
  obtain ⟨w₁, hw₁⟩ := Finite.surjective_of_injective hfinj ⟨w, hw⟩
  have hw₁' : ρ u (w₁ : V) = w := congrArg Subtype.val hw₁
  have key : ρ u⁻¹ w = (w₁ : V) := by
    rw [← hw₁']
    exact h1 _
  rw [key]
  exact w₁.2

theorem mem_flagStab_of_forall' [Finite V] (ρ : H →* Module.End F V) {Fl : ℕ → Submodule F V}
    {g : H} (hg : ∀ k, ∀ v ∈ Fl k, ρ g v ∈ Fl k) : g ∈ flagStab ρ Fl :=
  (mem_flagStab ρ).mpr fun k v hv => ⟨hg k v hv, mapsTo_inv ρ (Fl k) g (hg k) v hv⟩

theorem mem_flagKernel_of_sub_mem' [Finite V] (ρ : H →* Module.End F V) {A : ℕ → Submodule F V}
    (hA : Monotone A) (hA0 : A 0 = ⊥) {g : H} (hg : ∀ k, ∀ v ∈ A (k + 1), ρ g v - v ∈ A k) :
    g ∈ flagKernel ρ A := by
  refine (mem_flagKernel ρ).mpr ⟨mem_flagStab_of_forall' ρ ?_, hg⟩
  intro k v hv
  cases k with
  | zero =>
    rw [hA0, Submodule.mem_bot] at hv
    subst hv
    rw [map_zero]
    exact Submodule.zero_mem _
  | succ k =>
    have h1 : ρ g v - v ∈ A (k + 1) := hA (Nat.le_succ k) (hg k v hv)
    have h2 := add_mem h1 hv
    rwa [sub_add_cancel] at h2

end Stab

section Isometry

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem beta_rho_inv {Φ : ReflForm F V} {ρ : H →* Module.End F V} (hρ : IsIsometric Φ ρ)
    (h : H) (u v : V) : Φ.β (ρ h u) v = Φ.β u (ρ h⁻¹ v) := by
  have := hρ h u (ρ h⁻¹ v)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  exact this

end Isometry

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
