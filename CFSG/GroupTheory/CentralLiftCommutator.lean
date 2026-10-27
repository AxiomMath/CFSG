module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Plane

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

section CentralLift

variable {H Y : Type*} [Group H] [Group Y]

theorem commutator_commutator_comap_zpowers_eq_bot (π : H →* Y)
    (hker : π.ker ≤ Subgroup.center H) {S : Subgroup Y} {x : H} {T : Subgroup H}
    (hxT : ⁅Subgroup.zpowers x, T⁆ ≤ Subgroup.center H)
    (hST : ∀ s ∈ S, ∀ t ∈ T, s * π t = π t * s) :
    ⁅⁅S.comap π, Subgroup.zpowers x⁆, T⁆ = ⊥ := by
  have hAT : ⁅S.comap π, T⁆ ≤ π.ker := by
    rw [Subgroup.commutator_le]
    intro a ha t ht
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hST (π a) ha t ht)
  have hcenter : ⁅S.comap π, T⁆ ≤ Subgroup.center H := hAT.trans hker
  have h1 : ⁅⁅Subgroup.zpowers x, T⁆, S.comap π⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hxT.trans (Subgroup.center_le_centralizer (S.comap π : Set H))
  have h2 : ⁅⁅T, S.comap π⁆, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcenter.trans (Subgroup.center_le_centralizer (Subgroup.zpowers x : Set H))
  exact Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := S.comap π)
    (H₂ := Subgroup.zpowers x) (H₃ := T) h1 h2

theorem map_commutator_comap_zpowers_eq (π : H →* Y) {S : Subgroup Y} {x : H}
    (hS : S ≤ π.range) (hSx : ⁅S, Subgroup.zpowers (π x)⁆ = S) :
    (⁅S.comap π, Subgroup.zpowers x⁆).map π = S := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hS, MonoidHom.map_zpowers, hSx]

theorem map_commutator_commutator_comap_zpowers_eq (π : H →* Y) {S : Subgroup Y} {x : H}
    (hS : S ≤ π.range) (hSx : ⁅S, Subgroup.zpowers (π x)⁆ = S) :
    (⁅⁅S.comap π, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆).map π = S := by
  rw [Subgroup.map_commutator, map_commutator_comap_zpowers_eq π hS hSx,
    MonoidHom.map_zpowers, hSx]

end CentralLift

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem commutator_zpow_apply_eq_self_of_eq_smul {U : Submodule K V} {g x : V ≃ₗ[K] V} {c : K}
    (hg : U.map (g : V →ₗ[K] V) = U) (hx : ∀ u ∈ U, x u = c • u) (k : ℤ) :
    ∀ u ∈ U, ⁅g, x ^ k⁆ u = u := by
  by_cases hc : c = 0
  · have hbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_bot]
      exact x.injective (by rw [hx u hu, hc, zero_smul, map_zero])
    intro u hu
    rw [hbot] at hu
    rw [Submodule.mem_bot] at hu
    subst hu
    simp [commutatorElement_def]
  · intro u hu
    have hgu : g⁻¹ u ∈ U := by
      have hu' : u ∈ U.map (g : V →ₗ[K] V) := by rw [hg]; exact hu
      simpa using (Submodule.mem_map_equiv (p := U) (e := g)).mp hu'
    have hxpow : (x ^ k) (g⁻¹ u) = c ^ k • g⁻¹ u := by
      simpa using
        CFSG.SeitzReduction.OmegaPilot.zpow_apply_of_apply_eq_smul
          (a := Units.mk0 c hc) (hx (g⁻¹ u) hgu) k
    have hxpowinv : ((x ^ k)⁻¹) u = c ^ (-k) • u := by
      rw [← zpow_neg]
      simpa using
        CFSG.SeitzReduction.OmegaPilot.zpow_apply_of_apply_eq_smul
          (a := Units.mk0 c hc) (hx u hu) (-k)
    calc ⁅g, x ^ k⁆ u
        = g ((x ^ k) (g⁻¹ ((x ^ k)⁻¹ u))) := by
          simp only [commutatorElement_def, LinearEquiv.mul_apply]
      _ = g ((x ^ k) (c ^ (-k) • g⁻¹ u)) := by rw [hxpowinv, map_smul]
      _ = g (c ^ (-k) • (x ^ k) (g⁻¹ u)) := by rw [map_smul]
      _ = g (c ^ (-k) • (c ^ k • g⁻¹ u)) := by rw [hxpow]
      _ = g ((c ^ (-k) * c ^ k) • g⁻¹ u) := by rw [smul_smul]
      _ = g ((1 : K) • g⁻¹ u) := by rw [← zpow_add₀ hc, neg_add_cancel, zpow_zero]
      _ = u := by simp

theorem commutator_apply_eq_self_of_mapsTo_of_eq_smul {U : Submodule K V}
    {S₁ : Subgroup (V ≃ₗ[K] V)} {x : V ≃ₗ[K] V} {c : K}
    (hS : ∀ s ∈ S₁, U.map (s : V →ₗ[K] V) = U) (hx : ∀ u ∈ U, x u = c • u) :
    ∀ g ∈ ⁅S₁, Subgroup.zpowers x⁆, ∀ u ∈ U, g u = u := by
  let F : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {g | ∀ u ∈ U, g u = u}
      one_mem' := fun u _ => rfl
      mul_mem' := by
        rintro g h hg hh u hu
        rw [LinearEquiv.mul_apply, hh u hu, hg u hu]
      inv_mem' := by
        rintro g hg u hu
        apply g.injective
        rw [show g (g⁻¹ u) = u by simp, hg u hu] }
  show ⁅S₁, Subgroup.zpowers x⁆ ≤ F
  rw [Subgroup.commutator_le]
  intro s hs z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact commutator_zpow_apply_eq_self_of_eq_smul (hS s hs) hx k

theorem commute_of_fixes_of_mapsTo_of_sup_eq_top {U W : Submodule K V} {g h : V ≃ₗ[K] V}
    (hgU : ∀ u ∈ U, g u = u) (hgW : ∀ w ∈ W, g w ∈ W)
    (hhW : ∀ w ∈ W, h w = w) (hhU : ∀ u ∈ U, h u ∈ U) (hUW : U ⊔ W = ⊤) :
    g * h = h * g := by
  ext v
  have hv : v ∈ U ⊔ W := by rw [hUW]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [LinearEquiv.mul_apply, map_add]
  congr 1
  · rw [hgU _ (hhU u hu), hgU u hu]
  · rw [hhW w hw, hhW _ (hgW w hw)]

end Linear

end CFSG.GroupTheory
