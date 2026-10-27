module

public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.Standard
import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.SEITZ2

section Main


theorem fieldAutData_G2_odd_ne_three_at {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hpair : SubfieldPairG2At K) (hp5 : 5 ≤ p) :
    FieldAutData (adjointGroup .G2 K) p := by
  classical
  obtain ⟨hNFpt, Θ, hΘspec, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
      (Or.inr ⟨rfl, hℓ3⟩)
  have hNF := conj_normalForm_of_pointwise hNFpt
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card hℓ hf hK
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  refine fieldAutData_G2_of_descent hℓ hf hK hp hpair hp5 ?_ ?_
  · intro E hE hEc
    exact exists_conj_mem_of_plane_of_hom hp Θ hker E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
    obtain ⟨hσp, -, ⟨δ, hδ⟩, -⟩ :=
      odd_Chevalley_inner_field_noninner_prime_local_core_trivial .G2 hℓ hℓ2 hf K hK hNF hp ⊤
        le_top ⟨α, Subgroup.mem_top _⟩ (fun ⟨g, hg⟩ => hout g hg.symm)
        (by rw [Subgroup.orderOf_mk]; exact hord) x σ hxσ
    set τ : K ≃+* K := Θ δ with hτ
    have hΘτ : Θ (entrywiseAdjointAut .G2 τ) = τ := by
      refine hΘspec _ 1 τ fun h => ?_
      rw [coe_entrywiseAdjointAut]
      simp
    have hker1 : δ⁻¹ * entrywiseAdjointAut .G2 τ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hΘτ, ← hτ, inv_mul_cancel]
    rw [hker] at hker1
    obtain ⟨g, hg⟩ := hker1
    have hcomm : τ * σ = σ * τ := by
      let _ := IsCyclic.commGroup (α := K ≃+* K)
      exact mul_comm τ σ
    have hcomm' : entrywiseAdjointAut .G2 σ * entrywiseAdjointAut .G2 τ =
        entrywiseAdjointAut .G2 τ * entrywiseAdjointAut .G2 σ := by
      rw [← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, hcomm]
    refine ⟨g⁻¹, σ, hσp, ?_⟩
    have hgi : MulAut.conj g⁻¹ = (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹ := by
      rw [map_inv, hg]
    rw [hgi]
    calc (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹ * α * (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹⁻¹
        = (entrywiseAdjointAut .G2 τ)⁻¹ * (δ * α * δ⁻¹) * entrywiseAdjointAut .G2 τ := by
          group
      _ = (entrywiseAdjointAut .G2 τ)⁻¹ * (entrywiseAdjointAut .G2 σ *
            entrywiseAdjointAut .G2 τ) := by rw [hδ, mul_assoc]
      _ = entrywiseAdjointAut .G2 σ := by
          rw [hcomm', inv_mul_cancel_left]

theorem fieldAutData_G2_odd_ne_three (hpair : SubfieldPairG2Odd) {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp5 : 5 ≤ p) :
    FieldAutData (adjointGroup .G2 K) p :=
  fieldAutData_G2_odd_ne_three_at hℓ hℓ2 hℓ3 hf hK hp
    (hpair.at (by rw [ringChar_eq_of_card_pow hℓ hf hK]; exact hℓ2)) hp5

end Main

end CFSG.HardMathSupport.Seitz.G2Noninner
