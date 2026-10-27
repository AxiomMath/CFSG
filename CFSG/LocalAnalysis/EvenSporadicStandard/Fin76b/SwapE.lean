module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.EData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Fusion

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inner_swap_of_sylowEData (h : StdHyp G L) {X : Type*} [Group X] [Finite X] (φ : X ≃* L)
    (hX : SylowEData X) (hZ : center L = ⊥)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hinner : normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    ∃ (z t : G) (T₀ E : Subgroup G) (Q : Sylow 2 G) (x : G), InnerConfig G L z t T₀ ∧
      EConfig L T₀ E t ∧ T₀ ⊔ zpowers z ≤ (Q : Subgroup G) ∧ x ∈ (Q : Subgroup G) ∧
      x ∉ T₀ ⊔ zpowers z ∧ x ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G) ∧
      x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t := by
  have := h.simple
  obtain ⟨z, hzC, hz2⟩ := h.exists_involution_centralizer
  have hinn : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) :=
    (h.centralizer_le_normalizer hzC hz2).trans hinner
  obtain ⟨hcent, hdisj, -⟩ := h.centralizer_eq_prod_of_center_eq_bot hS hzC hz2 hinn hZ
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; omega
  obtain ⟨t, T₀, E, hcfg, hE⟩ := InnerConfig.of_sylowEData φ hX hz2' hz1 hzC hdisj hcent
  obtain ⟨P, x, hP, hTP, hxP, hxT, hxN, hxz, hxt⟩ := hcfg.exists_swap h.nonabelian
  obtain ⟨Q, hTQ, hxQ⟩ := exists_sylow_containing hP hTP hxP
  exact ⟨z, t, T₀, E, Q, x, hcfg, hE, hTQ, hxQ, hxT, hxN, hxz, hxt⟩

end CFSG.EvenSporadicStandard.Fin76b
