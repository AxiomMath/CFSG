module

public import CFSG.ClassicalInvolution.SmallOrth.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_scalars_of_forall_singular_small (P : HypPair Q) {a : V} (ha : a ∈ P.perp)
    (hc : Q a ≠ 0) {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ v, v ≠ 0 → Q v = 0 → ∃ c : K, g v = c • v) : g ∈ scalars K V := by
  obtain ⟨α, hα⟩ := hfix P.e P.e_ne_zero P.Q_e
  obtain ⟨γ, hγ⟩ := hfix P.f P.f_ne_zero P.Q_f
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at hα
    exact P.e_ne_zero hα
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at hγ
    exact P.f_ne_zero hγ
  have hW : ∀ w ∈ P.perp, g w = γ • w + (Q w * (α - γ)) • P.e ∧ Q w * (α - γ) = 0 := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := HypPair.mem_perp.mp hw
    obtain ⟨hs, hes⟩ := singular_f_add P hw
    set s := P.f + w - Q w • P.e with hsdef
    have hs0 : s ≠ 0 := by
      rintro h0
      rw [h0, polar_zero_right] at hes
      exact zero_ne_one hes
    obtain ⟨μ, hμ⟩ := hfix s hs0 hs
    have hgw : g w = (μ - γ) • P.f + μ • w + (Q w * (α - μ)) • P.e := by
      have h1 : g s = γ • P.f + g w - (Q w * α) • P.e := by
        rw [hsdef, map_sub, map_add, map_smul, hα, hγ, smul_smul]
      rw [h1, hsdef] at hμ
      have : g w = μ • (P.f + w - Q w • P.e) - γ • P.f + (Q w * α) • P.e := by
        rw [← hμ]; abel
      rw [this]
      module
    have hgwe : polar Q (g w) P.e = 0 := by
      have h1 : polar Q (g w) (g P.e) = 0 := by rw [polar_map_of_mem hg, polar_comm, hw1]
      rwa [hα, polar_smul_right_eq, mul_eq_zero, or_iff_right hα0] at h1
    have hgwf : polar Q (g w) P.f = 0 := by
      have h1 : polar Q (g w) (g P.f) = 0 := by rw [polar_map_of_mem hg, polar_comm, hw2]
      rwa [hγ, polar_smul_right_eq, mul_eq_zero, or_iff_right hγ0] at h1
    have hμγ : μ = γ := by
      rw [hgw, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        polar_smul_left_eq, P.polar_fe, polar_comm Q w P.e, hw1, P.polar_ee] at hgwe
      linear_combination hgwe
    subst hμγ
    refine ⟨?_, ?_⟩
    · rw [hgw]
      simp
    · rw [hgw, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        polar_smul_left_eq, P.polar_ff, polar_comm Q w P.f, hw2, P.polar_ef] at hgwf
      linear_combination hgwf
  have hαγ : α = γ := by
    have := (hW a ha).2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
  refine mem_scalars.mpr ⟨γ, fun x => ?_⟩
  have hx := P.eq_add_proj x
  have hxp := (hW _ (P.proj_mem_perp x)).1
  rw [hαγ, sub_self, mul_zero, zero_smul, add_zero] at hxp
  rw [hx, map_add, map_add, map_smul, map_smul, hα, hγ, hxp, hαγ]
  module

end CFSG.ClassicalGroups.Orthogonal.Small
