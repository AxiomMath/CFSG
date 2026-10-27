module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.Layer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Fusion

public section

namespace CFSG.EvenSporadicStandard.Co3Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier.Co3

section Certified


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem co3_inner_swap (h : StdHyp G L) (hL : IsSporadic L .Co3) :
    ∃ (z t : G) (T₀ P : Subgroup G) (x : G), Fin76b.InnerConfig G L z t T₀ ∧ IsPGroup 2 P ∧
      T₀ ⊔ zpowers z ≤ P ∧ x ∈ P ∧ x ∉ T₀ ⊔ zpowers z ∧
      x ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G) ∧
      x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t := by
  have := h.simple
  obtain ⟨e⟩ := hL
  have : Finite (Carrier .Co3) := Finite.of_equiv L e.toEquiv
  obtain ⟨z, hz2, hzC, hcent, hdisj, -, -⟩ := exists_layer0_co3 h ⟨e⟩
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; omega
  have hX : Fin76b.SylowData (Carrier .Co3) :=
    Fin76b.SylowData.of_mulEquiv co3PermEquiv.symm sylowData_co3P
  obtain ⟨t, T₀, hcfg⟩ := Fin76b.InnerConfig.of_sylowData e.symm hX hz2' hz1 hzC hdisj hcent
  obtain ⟨P, x, hP⟩ := hcfg.exists_swap h.nonabelian
  exact ⟨z, t, T₀, P, x, hcfg, hP⟩

end Certified

end CFSG.EvenSporadicStandard.Co3Std
