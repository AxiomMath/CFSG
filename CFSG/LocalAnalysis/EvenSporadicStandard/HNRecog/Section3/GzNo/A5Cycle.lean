module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_a5_cycle : ∀ t : alternatingGroup (Fin 5), t ^ 2 = 1 → t ≠ 1 →
    ∃ s : alternatingGroup (Fin 5), (s * t * s⁻¹) * t = t * (s * t * s⁻¹) ∧
      s * t * s⁻¹ ≠ t ∧ s * (s * t * s⁻¹) * s⁻¹ = t * (s * t * s⁻¹) := by
  decide +kernel

private theorem z5_sq_eq_one : ∀ k : Z 5, k ^ 2 = 1 → k = 1 := by
  decide

theorem gzNo_exists_cycle {Γ : Type*} [Group Γ] {r u : Γ}
    (hr : IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({r} : Set Γ))) (hu : u * r = r * u)
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ s : Γ, s * r = r * s ∧ (s * u * s⁻¹) * u = u * (s * u * s⁻¹) ∧ s * u * s⁻¹ ≠ u ∧
      s * (s * u * s⁻¹) * s⁻¹ = u * (s * u * s⁻¹) := by
  obtain ⟨e⟩ := hr
  let ψ : alternatingGroup (Fin 5) →* Γ :=
    (Subgroup.centralizer ({r} : Set Γ)).subtype.comp
      (e.symm.toMonoidHom.comp (MonoidHom.inr (Z 5) (alternatingGroup (Fin 5))))
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : e.symm ((1 : Z 5), a) = e.symm ((1 : Z 5), b) := Subtype.ext hab
    exact congrArg Prod.snd (e.symm.injective h1)
  have hψr : ∀ a, ψ a * r = r * ψ a := fun a =>
    Subgroup.mem_centralizer_singleton_iff.mp (e.symm ((1 : Z 5), a)).2
  let û : ↥(Subgroup.centralizer ({r} : Set Γ)) :=
    ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr hu⟩
  have hû2 : û ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hu2)
  have hû1 : û ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have he2 : (e û) ^ 2 = 1 := by rw [← map_pow, hû2, map_one]
  have hk : (e û).1 = 1 := z5_sq_eq_one _ (by
    have h1 := congrArg Prod.fst he2
    simpa using h1)
  have ht2 : (e û).2 ^ 2 = 1 := by
    have h1 := congrArg Prod.snd he2
    simpa using h1
  have ht1 : (e û).2 ≠ 1 := by
    intro h
    apply hû1
    apply e.injective
    rw [map_one]
    exact Prod.ext hk h
  have hψt : ψ (e û).2 = u := by
    have h1 : ((1 : Z 5), (e û).2) = e û := Prod.ext hk.symm rfl
    change ((e.symm ((1 : Z 5), (e û).2) : ↥(Subgroup.centralizer ({r} : Set Γ))) : Γ) = u
    rw [h1, MulEquiv.symm_apply_apply]
  obtain ⟨s₀, h1, h2, h3⟩ := gzNo_a5_cycle (e û).2 ht2 ht1
  refine ⟨ψ s₀, hψr s₀, ?_, ?_, ?_⟩
  · have h4 := congrArg ψ h1
    simpa only [map_mul, map_inv, hψt] using h4
  · intro h
    apply h2
    apply hψinj
    simpa only [map_mul, map_inv, hψt] using h
  · have h4 := congrArg ψ h3
    simpa only [map_mul, map_inv, hψt] using h4

end CFSG.EvenSporadicStandard.HNRecog.Section3
