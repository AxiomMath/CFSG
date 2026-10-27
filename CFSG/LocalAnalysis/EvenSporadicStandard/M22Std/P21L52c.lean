module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21L52b

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21L52

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K]

theorem false_of_outer_psl5 (hK : Nat.card K = 2) {G : Type} [Group G] (U : Subgroup G)
    [U.Normal] (Θ : U ≃* projectiveSL 5 K) {z : G}
    (hz : z ∉ U ⊔ Subgroup.centralizer (U : Set G))
    (hNoInv : ∀ x t : G, x ^ 31 = 1 → x ≠ 1 → t * x * t⁻¹ = x⁻¹ → False) : False := by
  set α : MulAut (projectiveSL 5 K) := MulAut.congr Θ (MulAut.conjNormal z) with hαdef
  have hα : ∀ u : U, α (Θ u) = Θ (MulAut.conjNormal z u) := by
    intro u
    simp [hαdef, MulAut.congr_apply]
  obtain ⟨A', ε, hε, hαeq⟩ := automorphism_form hK α
  have hconj : ∀ g : SpecialLinearGroup (Fin 5) K,
      conjAut 5 K (Matrix.SpecialLinearGroup.toGL A') (proj 5 K g) =
        proj 5 K A' * proj 5 K g * (proj 5 K A')⁻¹ := by
    intro g
    rw [conjAut_proj, slConjugation_eq rfl, map_mul, map_mul, map_inv]
  set a : U := Θ.symm (proj 5 K A') with ha
  have hΘa : Θ a = proj 5 K A' := Θ.apply_symm_apply _
  have hcoe : ∀ u : U, ((MulAut.conjNormal z u : U) : G) = z * (u : G) * z⁻¹ := fun u =>
    MulAut.conjNormal_apply z u
  have hact : ∀ u : U, Θ (MulAut.conjNormal z u) = α (Θ u) := fun u => (hα u).symm
  interval_cases ε
  ·
    apply hz
    have hα0 : α = conjAut 5 K (Matrix.SpecialLinearGroup.toGL A') := by
      rw [hαeq, pow_zero, mul_one]
    have hu : ∀ u : U, z * (u : G) * z⁻¹ = (a : G) * (u : G) * (a : G)⁻¹ := by
      intro u
      obtain ⟨g, hg⟩ := proj_surjective 5 K (Θ u)
      have h1 : Θ (MulAut.conjNormal z u) = Θ (a * u * a⁻¹) := by
        rw [hact, hα0, ← hg, hconj, map_mul, map_mul, map_inv, hΘa, hg]
      have h2 := Θ.injective h1
      rw [← hcoe, h2]
      rfl
    have hk : (a : G)⁻¹ * z ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu'
      have := hu ⟨u, hu'⟩
      calc u * ((a : G)⁻¹ * z) = (a : G)⁻¹ * ((a : G) * u * (a : G)⁻¹) * z := by group
        _ = (a : G)⁻¹ * (z * u * z⁻¹) * z := by rw [← this]
        _ = (a : G)⁻¹ * z * u := by group
    have hz' : z = (a : G) * ((a : G)⁻¹ * z) := by group
    rw [hz']
    exact Subgroup.mul_mem_sup a.2 hk
  ·
    obtain ⟨x, hx31, hx1, hxT⟩ := exists_symm_order_31 hK
    have hδ : dualAut 5 K (proj 5 K x) = (proj 5 K x)⁻¹ := by
      rw [dualAut_proj, hxT, map_inv]
    have hα1 : α (proj 5 K x) = proj 5 K A' * (proj 5 K x)⁻¹ * (proj 5 K A')⁻¹ := by
      rw [hαeq, pow_one, MulAut.mul_apply, hδ, ← map_inv, hconj]
    set xG : U := Θ.symm (proj 5 K x) with hxG
    have hΘx : Θ xG = proj 5 K x := Θ.apply_symm_apply _
    have h1 : Θ (MulAut.conjNormal z xG) = Θ (a * xG⁻¹ * a⁻¹) := by
      rw [hact, hΘx, hα1, map_mul, map_mul, map_inv, map_inv, hΘa, hΘx]
    have h2 := Θ.injective h1
    have hzx : z * (xG : G) * z⁻¹ = (a : G) * (xG : G)⁻¹ * (a : G)⁻¹ := by
      rw [← hcoe, h2]
      rfl
    have hxG31 : (xG : G) ^ 31 = 1 := by
      have : xG ^ 31 = 1 := by
        apply Θ.injective
        rw [map_pow, hΘx, ← map_pow, hx31, map_one, map_one]
      exact congrArg Subtype.val this
    have hxG1 : (xG : G) ≠ 1 := by
      intro h
      have h' : xG = 1 := Subtype.ext h
      have : proj 5 K x = 1 := by rw [← hΘx, h', map_one]
      have hx : x ∈ scalars 5 K := by
        rw [← ker_proj]
        exact this
      rw [scalars_eq_bot hK 5, Subgroup.mem_bot] at hx
      exact hx1 hx
    refine hNoInv (xG : G) ((a : G)⁻¹ * z) hxG31 hxG1 ?_
    calc (a : G)⁻¹ * z * (xG : G) * ((a : G)⁻¹ * z)⁻¹ = (a : G)⁻¹ * (z * (xG : G) * z⁻¹) * a := by
          group
      _ = (xG : G)⁻¹ := by rw [hzx]; group

end CFSG.EvenSporadicStandard.M22Std.P21L52
