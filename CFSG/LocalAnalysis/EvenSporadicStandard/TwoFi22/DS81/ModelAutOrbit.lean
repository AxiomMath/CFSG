module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

namespace AutOrbit

variable {X : Type*} {P R V : Subgroup (Equiv.Perm X)}

theorem mem_of_commute_of_regular_orbit (t : X → Equiv.Perm X)
    (ht : ∀ r ∈ R, ∀ p, t (r p) = r * t p * r⁻¹)
    (hcent : ∀ g : Equiv.Perm X, (∀ h ∈ P, g * h = h * g) → g = 1)
    (hVR : V ≤ R) (hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (p₀ : X)
    (hreg : ∀ v ∈ V, v p₀ = p₀ → v = 1)
    (huniq : ∀ q : X, (∀ v ∈ V, v q = q → v = 1) → ∃ v ∈ V, v p₀ = q)
    (hgen : P ≤ closure (t '' {q | ∃ v ∈ V, v p₀ = q})) :
    ∀ r ∈ R, (∀ e ∈ V, r * e = e * r) → r ∈ V := by
  intro r hr hrV
  have hq : ∀ v ∈ V, v (r p₀) = r p₀ → v = 1 := by
    intro v hv hvq
    apply hreg v hv
    have h1 : r (v p₀) = r p₀ := by
      have := hrV v hv
      have h2 := congrArg (fun σ : Equiv.Perm X => σ p₀) this
      simp only [Equiv.Perm.mul_apply] at h2
      rw [h2]
      exact hvq
    exact r.injective h1
  obtain ⟨e, he, hep⟩ := huniq (r p₀) hq
  set g : Equiv.Perm X := e⁻¹ * r with hg
  have hgR : g ∈ R := R.mul_mem (R.inv_mem (hVR he)) hr
  have hgp₀ : g p₀ = p₀ := by
    rw [hg, Equiv.Perm.mul_apply, ← hep]
    simp
  have hgV : ∀ v ∈ V, g * v = v * g := by
    intro v hv
    rw [hg, mul_assoc, hrV v hv, ← mul_assoc, ← mul_assoc]
    congr 1
    exact (hVcomm v hv e⁻¹ (V.inv_mem he)).symm
  have hfix : ∀ q ∈ {q | ∃ v ∈ V, v p₀ = q}, g q = q := by
    rintro _ ⟨v, hv, rfl⟩
    have h2 := congrArg (fun σ : Equiv.Perm X => σ p₀) (hgV v hv)
    simp only [Equiv.Perm.mul_apply] at h2
    rw [h2, hgp₀]
  have hcomm : ∀ q ∈ {q | ∃ v ∈ V, v p₀ = q}, g * t q = t q * g := by
    intro q hq'
    have h1 := ht g hgR q
    rw [hfix q hq'] at h1
    exact (eq_mul_inv_iff_mul_eq.1 h1).symm
  have hle : closure (t '' {q | ∃ v ∈ V, v p₀ = q}) ≤ centralizer {g} := by
    rw [closure_le]
    rintro _ ⟨q, hq', rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (hcomm q hq').symm
  have hg1 : g = 1 := hcent g fun h hh => by
    have := mem_centralizer_singleton_iff.1 (hle (hgen hh))
    exact this.symm
  have : e⁻¹ * r = 1 := hg1
  rw [inv_mul_eq_one] at this
  rw [← this]
  exact he

end AutOrbit

end CFSG.EvenSporadicStandard.TwoFi22.DS81
