module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.CentHomSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.NoNormal2S5

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

section Cert


theorem r0_max (hP : Nat.card ↥P1408 = 177408000) :
    ∀ P : Subgroup ↥P1408, P ≤ centralizer ({pZ} : Set ↥P1408) → IsPGroup 2 ↥P →
      (∀ c ∈ centralizer ({pZ} : Set ↥P1408), ∀ x ∈ P, c * x * c⁻¹ ∈ P) →
        P ≤ wordSubgroupP nWords1 := by
  obtain ⟨ψ, hsurj, hker, -⟩ := HaradaModel27.exists_hom_centralizer_pZ hP
  intro P hPC hP2 hPn
  let C : Subgroup ↥P1408 := centralizer ({pZ} : Set ↥P1408)
  let P' : Subgroup ↥C := P.subgroupOf C
  have hP'2 : IsPGroup 2 ↥P' := hP2.comap_of_injective C.subtype Subtype.val_injective
  have hP'n : P'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ((g * n * g⁻¹ : ↥C) : ↥P1408) ∈ P
    have hn' : (n : ↥P1408) ∈ P := hn
    have h := hPn (g : ↥P1408) g.2 (n : ↥P1408) hn'
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hQ2 : IsPGroup 2 ↥(P'.map ψ) := hP'2.map ψ
  have hQn : (P'.map ψ).Normal := hP'n.map ψ hsurj
  have hQ : P'.map ψ = ⊥ := eq_bot_of_normal_isPGroup_perm5 _ hQ2 hQn
  intro x hx
  have hxC : x ∈ C := hPC hx
  have hxP' : (⟨x, hxC⟩ : ↥C) ∈ P' := hx
  have hψ : ψ ⟨x, hxC⟩ ∈ P'.map ψ := Subgroup.mem_map_of_mem ψ hxP'
  rw [hQ, Subgroup.mem_bot] at hψ
  have hxker : (⟨x, hxC⟩ : ↥C) ∈ ψ.ker := hψ
  rw [hker] at hxker
  exact hxker

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
