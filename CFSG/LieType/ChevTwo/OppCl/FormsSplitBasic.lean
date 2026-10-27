module

public import CFSG.LieType.ChevTwo.OppCl.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl.FS

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem semilin_zero {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) : r 0 = 0 := by
  have h : r (0 + 0) = r 0 + r 0 := hr.1 0 0
  rw [add_zero] at h
  have h' : r 0 + 0 = r 0 + r 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

theorem semilin_sum {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : r (∑ i ∈ s, f i) = ∑ i ∈ s, r (f i) := by
  exact map_sum (AddMonoidHom.mk' (fun v : V => r v) hr.1) f s

theorem β_sum_right (Φ : ReflForm F V) {ι : Type*} (s : Finset ι) (u : V) (f : ι → V) :
    Φ.β u (∑ i ∈ s, f i) = ∑ i ∈ s, Φ.β u (f i) := by
  exact map_sum (AddMonoidHom.mk' (Φ.β u) (Φ.add_right u)) f s

theorem β_sum_left (Φ : ReflForm F V) {ι : Type*} (s : Finset ι) (f : ι → V) (v : V) :
    Φ.β (∑ i ∈ s, f i) v = ∑ i ∈ s, Φ.β (f i) v := by
  exact map_sum (AddMonoidHom.mk' (fun x => Φ.β x v) (fun a b => Φ.add_left a b v)) f s

theorem perp_inv (Φ : ReflForm F V) (Rh : Subgroup (Equiv.Perm V))
    (hiso : ∀ r ∈ Rh, SemiIso Φ r) (U : Submodule F V) (hU : ∀ r ∈ Rh, ∀ v ∈ U, r v ∈ U) :
    ∀ r ∈ Rh, ∀ v ∈ Φ.perp U, r v ∈ Φ.perp U := by
  intro r hr v hv w hw
  obtain ⟨τ, hτ⟩ := hiso r hr
  have hw' : r⁻¹ w ∈ U := hU r⁻¹ (inv_mem hr) w hw
  have hrw : r (r⁻¹ w) = w := r.apply_symm_apply w
  have h1 : Φ.β (r (r⁻¹ w)) (r v) = τ (Φ.β (r⁻¹ w) v) := hτ (r⁻¹ w) v
  rw [hrw] at h1
  rw [h1, hv (r⁻¹ w) hw', map_zero]

theorem semiIso_polar (Φ : QuadForm F V) {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V)
    (h : SemiIsoQ Φ r) : SemiIso Φ.polar r := by
  obtain ⟨τ, hτ⟩ := h
  have hadd : ∀ u v, r (u + v) = r u + r v := hr.1
  have hpolar : ∀ x y, Φ.polar.β x y = Φ.Q (x + y) - Φ.Q x - Φ.Q y := by
    intro x y
    rw [Φ.Q_add x y]
    ring
  refine ⟨τ, fun u v => ?_⟩
  rw [hpolar, hpolar, ← hadd, hτ, hτ, hτ, map_sub, map_sub]

end CFSG.LieType.ChevTwo.OppCl.FS
