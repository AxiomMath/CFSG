module

public import CFSG.LieType.ChevTwo.OppCl.FormsCasesUrad
public import CFSG.LieType.ChevTwo.OppCl.FormsCasesLift

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section CaseG

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

variable {Φ : ReflForm F V} {Sing : V → Prop} {TS : Submodule F V → Prop}
  {ρ : H →* Module.End F V} {p : ℕ} [Fact p.Prime]
  {Rh : Subgroup (Equiv.Perm V)} {X : ℕ → Submodule F V} {m : ℕ} {M W' : Submodule F V}

private theorem perm_apply_inv_self {α : Type} (r : Equiv.Perm α) (v : α) : r (r⁻¹ v) = v :=
  r.apply_symm_apply v

private theorem preserves_of_conj {r : Equiv.Perm V} (hr : r ∈ Rh) {g' h : H}
    (hh : ∀ v, r (ρ g' v) = ρ h (r v)) (U : Submodule F V)
    (hU : ∀ r ∈ Rh, ∀ v ∈ U, r v ∈ U) (hg' : ∀ v ∈ U, ρ g' v ∈ U) :
    ∀ v ∈ U, ρ h v ∈ U := by
  intro v hv
  have h1 := hh (r⁻¹ v)
  rw [perm_apply_inv_self] at h1
  rw [← h1]
  exact hU r hr _ (hg' _ (hU r⁻¹ (inv_mem hr) v hv))

theorem lift_levi_core (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (g : V →ₗ[F] V)
    (hgc : ∀ r ∈ Rh, ∀ v, r (g v) = g (r v)) (u₀ : H) (hu₀ : LevProp Φ ρ (X m) g u₀) :
    ∃ y : H, CommR ρ Rh y ∧ LevProp Φ ρ (X m) g y := by
  have hWiso : Φ.IsTotallyIsotropic (X m) := C.hTS _ (C.hXts m)
  obtain ⟨hu1, hu2⟩ := hu₀
  set Fw : ℕ → Submodule F V :=
    isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else X m) 1
  have hWinv : ∀ r ∈ Rh, ∀ v ∈ X m, r v ∈ X m := fun r hr v hv => C.hXinv r hr m v hv
  have hPinv : ∀ r ∈ Rh, ∀ v ∈ Φ.perp (X m), r v ∈ Φ.perp (X m) :=
    perp_invariant Φ Rh C.hiso (X m) hWinv
  have hu₀W : ∀ w ∈ X m, ρ u₀ w ∈ X m := by
    intro w hw
    have h1 : g w ∈ X m := by
      have := hu2 w (hWiso hw)
      rwa [hu1 w hw, add_sub_cancel_left] at this
    rw [hu1 w hw]
    exact add_mem hw h1
  have hu₀P : ∀ v ∈ Φ.perp (X m), ρ u₀ v ∈ Φ.perp (X m) := by
    intro v hv
    have h1 : ρ u₀ v - v ∈ Φ.perp (X m) := hWiso (hu2 v hv)
    have := add_mem h1 hv
    rwa [sub_add_cancel] at this
  have hu₀G : u₀ ∈ flagStab ρ Fw := (mem_flagStab_Fw hWiso C.hρ).mpr ⟨hu₀W, hu₀P⟩
  have hNG : Urad Φ ρ (X m) ≤ flagStab ρ Fw := flagKernel_le_flagStab ρ Fw
  have hNn : ((Urad Φ ρ (X m)).subgroupOf (flagStab ρ Fw)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).mpr
      (flagStab_le_normalizer_flagKernel ρ Fw)
  have hN2 : IsPGroup 2 (Urad Φ ρ (X m)) := urad_isPGroup C.hinj
  have hG : ∀ r ∈ Rh, ∀ g' ∈ flagStab ρ Fw, ∀ h : H, (∀ v, r (ρ g' v) = ρ h (r v)) →
      h ∈ flagStab ρ Fw := by
    intro r hr g' hg' h hh
    obtain ⟨hg'W, hg'P⟩ := (mem_flagStab_Fw hWiso C.hρ).mp hg'
    exact (mem_flagStab_Fw hWiso C.hρ).mpr
      ⟨preserves_of_conj hr hh (X m) hWinv hg'W, preserves_of_conj hr hh _ hPinv hg'P⟩
  have hinv : ∀ v, ρ u₀⁻¹ (ρ u₀ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hg : ∀ r ∈ Rh, ∀ h : H, (∀ v, r (ρ u₀ v) = ρ h (r v)) →
      u₀⁻¹ * h ∈ Urad Φ ρ (X m) := by
    intro r hr h hh
    have hrepr : ∀ v, ρ h v = r (ρ u₀ (r⁻¹ v)) := fun v => by
      have h1 := hh (r⁻¹ v)
      rw [perm_apply_inv_self] at h1
      exact h1.symm
    have hradd : ∀ u v : V, r (u + v) = r u + r v := (C.hs hr).1
    have hmul : ∀ v, ρ (u₀⁻¹ * h) v = ρ u₀⁻¹ (ρ h v) := fun v => by
      rw [map_mul, Module.End.mul_apply]
    have hW : ∀ w ∈ X m, ρ h w = ρ u₀ w := by
      intro w hw
      have hw' : r⁻¹ w ∈ X m := hWinv r⁻¹ (inv_mem hr) w hw
      rw [hrepr, hu1 _ hw', hu1 _ hw, hradd, hgc r hr, perm_apply_inv_self]
    rw [mem_Urad_iff hWiso C.hρ]
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · rw [hmul, hW w hw, hinv]
    · have hv' : r⁻¹ v ∈ Φ.perp (X m) := hPinv r⁻¹ (inv_mem hr) v hv
      have e1 : ρ u₀ (r⁻¹ v) - r⁻¹ v ∈ X m := hu2 _ hv'
      have e2 : ρ h v - v ∈ X m := by
        have : ρ h v - v = r (ρ u₀ (r⁻¹ v) - r⁻¹ v) := by
          rw [hrepr, semilin_sub (C.hs hr), perm_apply_inv_self]
        rw [this]
        exact hWinv r hr _ e1
      have e3 : ρ u₀ v - v ∈ X m := hu2 v hv
      have e4 : ρ h v - ρ u₀ v ∈ X m := by
        have := sub_mem e2 e3
        rwa [sub_sub_sub_cancel_right] at this
      have e5 := mapsTo_inv ρ (X m) u₀ hu₀W _ e4
      rw [map_sub, hinv] at e5
      rw [hmul]
      exact e5
  obtain ⟨c, hcG, hcR, hcN⟩ := exists_fixed_coset_H p hp2 ρ C.hinj Rh C.hR C.hN
    (flagStab ρ Fw) (Urad Φ ρ (X m)) hNG hNn hN2 hG u₀ hu₀G hg
  refine ⟨c, hcR, ?_⟩
  obtain ⟨hcW, -⟩ := (mem_flagStab_Fw hWiso C.hρ).mp hcG
  obtain ⟨hn1, hn2⟩ := (mem_Urad_iff hWiso C.hρ).mp hcN
  have hu : ∀ v, ρ u₀ v = ρ c (ρ (c⁻¹ * u₀) v) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  refine ⟨fun w hw => ?_, fun y hy => ?_⟩
  · rw [← hu1 w hw, hu, hn1 w hw]
  · have e1 : ρ (c⁻¹ * u₀) y - y ∈ X m := hn2 y hy
    have e2 : ρ c (ρ (c⁻¹ * u₀) y - y) ∈ X m := hcW _ e1
    have e3 : ρ u₀ y - y ∈ X m := hu2 y hy
    have : ρ c y - y = (ρ u₀ y - y) - ρ c (ρ (c⁻¹ * u₀) y - y) := by
      rw [hu y, map_sub]
      abel
    rw [this]
    exact sub_mem e3 e2

end CaseG

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
