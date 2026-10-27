module

public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Pairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Signs

public section

namespace CFSG.ClassicalInvolution.Models.Transfer

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups commutatorElement

variable {K K' V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {X : Type} [Group X] [Finite K] {θ : ↥(elementaryGroup Q) →* X}
  {L₁ L₂ L₃ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ i₃ : V ≃ₗ[K] V}
  [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime] [CharP K' p]

section Lifts

variable (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q))

include hker

theorem lemma_6_10_unitary_map_of_commute [FiniteDimensional K V]
    (hcard : Nat.card K = p ^ f) (hcard' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hs : ¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    UnitaryBlockStandardPair K' p f ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
      (L₂.subgroupOf (elementaryGroup Q)).map θ)
      ((L₁.subgroupOf (elementaryGroup Q)).map θ)
      ((L₂.subgroupOf (elementaryGroup Q)).map θ) := by
  have hN' : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)) :=
    (map_mem_normalizer_iff_fundamental hker (by omega) h₁).mp hN
  have hC' : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)) := fun hmem =>
    hC ((map_mem_centralizer_iff_fundamental hker (by omega) h₁).mpr hmem)
  obtain ⟨θ₀, hinj, hrange, hU, hV⟩ :=
    exists_hom_of_lemma_6_10_unitary hcard hcard' hodd h₁ h₂ hc hN' hC' hs
  obtain ⟨ρ, hρinj, hρrange, hρ₁, hρ₂⟩ := exists_hom_subgroupOf h₁.le_elementaryGroup
    h₂.le_elementaryGroup (B12 K' p f) (B23 K' p f) θ₀ hinj hrange hU hV
  refine unitaryBlockStandardPair_of_normalized (θ := θ.comp ρ)
    (ker_comp_le_center ρ hρinj hker) ?_ ?_ ?_
  · rw [MonoidHom.range_comp, hρrange, Subgroup.map_sup]
  · rw [← Subgroup.map_map, hρ₁]
  · rw [← Subgroup.map_map, hρ₂]

theorem lemma_6_10_dichotomy_map_of_commute [FiniteDimensional K V]
    (hcard : Nat.card K = p ^ f) (hcard' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X)) :
    PairDecomposition Q i₁ i₂ ∧
      ((HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
          LinearBlockStandardPair K ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
            (L₂.subgroupOf (elementaryGroup Q)).map θ)
            ((L₁.subgroupOf (elementaryGroup Q)).map θ)
            ((L₂.subgroupOf (elementaryGroup Q)).map θ)) ∨
        (¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
          UnitaryBlockStandardPair K' p f ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
            (L₂.subgroupOf (elementaryGroup Q)).map θ)
            ((L₁.subgroupOf (elementaryGroup Q)).map θ)
            ((L₂.subgroupOf (elementaryGroup Q)).map θ))) := by
  obtain ⟨hP, hlin⟩ := lemma_6_10_map_of_commute hker hodd h5 h₁ h₂ hc hN hC
  by_cases hs : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)
  · exact ⟨hP, Or.inl ⟨hs, hlin hs⟩⟩
  · exact ⟨hP, Or.inr ⟨hs,
      lemma_6_10_unitary_map_of_commute hker hcard hcard' hodd h5 h₁ h₂ hc hN hC hs⟩⟩

theorem lemma_6_11_signs_map_of_commute [FiniteDimensional K V]
    (hcard : Nat.card K = p ^ f) (hcard' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (h₃ : IsFundamental Q L₃ i₃)
    (h₁₂ : i₁ * i₂ = i₂ * i₁) (h₃₂ : i₃ * i₂ = i₂ * i₃) (h₁₃ : i₁ * i₃ = i₃ * i₁)
    (hL : ∀ x ∈ (L₁.subgroupOf (elementaryGroup Q)).map θ,
      ∀ y ∈ (L₃.subgroupOf (elementaryGroup Q)).map θ, x * y = y * x)
    (hN₁ : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hN₃ : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₃.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC₁ : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC₃ : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₃.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X)) :
    (HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
        HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) ∧
        LinearBlockStandardPair K ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₁.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ) ∧
        LinearBlockStandardPair K ((L₂.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₃.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₃.subgroupOf (elementaryGroup Q)).map θ)) ∨
      (¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
        ¬ HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) ∧
        UnitaryBlockStandardPair K' p f ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₁.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ) ∧
        UnitaryBlockStandardPair K' p f ((L₂.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₃.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₃.subgroupOf (elementaryGroup Q)).map θ)) := by
  have hiff := lemma_6_11_map_of_commute hker hodd h5 h₁ h₂ h₃ h₁₂ h₃₂ h₁₃ hL hN₁ hN₃ hC₁ hC₃
  obtain ⟨-, hd₁₂⟩ := lemma_6_10_dichotomy_map_of_commute hker hcard hcard' hodd h5 h₁ h₂ h₁₂
    hN₁ hC₁
  obtain ⟨-, hd₃₂⟩ := lemma_6_10_dichotomy_map_of_commute hker hcard hcard' hodd h5 h₃ h₂ h₃₂
    hN₃ hC₃
  rw [inf_comm (negSpace i₃) (negSpace i₂), sup_comm ((L₃.subgroupOf (elementaryGroup Q)).map θ)]
    at hd₃₂
  rcases hd₁₂ with ⟨hs₁, hl₁⟩ | ⟨hs₁, hu₁⟩
  · rcases hd₃₂ with ⟨hs₃, hl₃⟩ | ⟨hs₃, -⟩
    · exact Or.inl ⟨hs₁, hs₃, hl₁, linearBlockStandardPair_swap hl₃⟩
    · exact absurd (hiff.mp hs₁) hs₃
  · rcases hd₃₂ with ⟨hs₃, -⟩ | ⟨hs₃, hu₃⟩
    · exact absurd (hiff.mpr hs₃) hs₁
    · exact Or.inr ⟨hs₁, hs₃, hu₁, unitaryBlockStandardPair_swap hu₃⟩

end Lifts

section WithLift

variable [FiniteDimensional K V] (hodd : Odd (Nat.card K))
  (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q)) (hZ : CenterScalar Q)
  (hdim : 4 < Module.finrank K V) (hlift : Module.finrank K V ≠ 8 ∨ KerInvolutionFree θ)
  (hcard : Nat.card K = p ^ f) (hcard' : Nat.card K' = (p ^ f) ^ 2)

include hodd hker hZ hdim hlift hcard hcard'

theorem lemma_6_10_unitary_map (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : Commute (θ (fundElt h₁)) (θ (fundElt h₂)))
    (hN : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hs : ¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    UnitaryBlockStandardPair K' p f ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
      (L₂.subgroupOf (elementaryGroup Q)).map θ)
      ((L₁.subgroupOf (elementaryGroup Q)).map θ)
      ((L₂.subgroupOf (elementaryGroup Q)).map θ) :=
  lemma_6_10_unitary_map_of_commute hker hcard hcard' hodd h5 h₁ h₂
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₂ hc) hN hC hs

theorem lemma_6_10_dichotomy_map (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : Commute (θ (fundElt h₁)) (θ (fundElt h₂)))
    (hN : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X)) :
    PairDecomposition Q i₁ i₂ ∧
      ((HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
          LinearBlockStandardPair K ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
            (L₂.subgroupOf (elementaryGroup Q)).map θ)
            ((L₁.subgroupOf (elementaryGroup Q)).map θ)
            ((L₂.subgroupOf (elementaryGroup Q)).map θ)) ∨
        (¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
          UnitaryBlockStandardPair K' p f ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
            (L₂.subgroupOf (elementaryGroup Q)).map θ)
            ((L₁.subgroupOf (elementaryGroup Q)).map θ)
            ((L₂.subgroupOf (elementaryGroup Q)).map θ))) :=
  lemma_6_10_dichotomy_map_of_commute hker hcard hcard' hodd h5 h₁ h₂
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₂ hc) hN hC

theorem lemma_6_11_signs_map (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (h₃ : IsFundamental Q L₃ i₃)
    (hc₁₂ : Commute (θ (fundElt h₁)) (θ (fundElt h₂)))
    (hc₃₂ : Commute (θ (fundElt h₃)) (θ (fundElt h₂)))
    (hc₁₃ : Commute (θ (fundElt h₁)) (θ (fundElt h₃)))
    (hL : ∀ x ∈ (L₁.subgroupOf (elementaryGroup Q)).map θ,
      ∀ y ∈ (L₃.subgroupOf (elementaryGroup Q)).map θ, x * y = y * x)
    (hN₁ : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hN₃ : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₃.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC₁ : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC₃ : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₃.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X)) :
    (HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
        HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) ∧
        LinearBlockStandardPair K ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₁.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ) ∧
        LinearBlockStandardPair K ((L₂.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₃.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₃.subgroupOf (elementaryGroup Q)).map θ)) ∨
      (¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
        ¬ HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) ∧
        UnitaryBlockStandardPair K' p f ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₁.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ) ∧
        UnitaryBlockStandardPair K' p f ((L₂.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₃.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₃.subgroupOf (elementaryGroup Q)).map θ)) :=
  lemma_6_11_signs_map_of_commute hker hcard hcard' hodd h5 h₁ h₂ h₃
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₂ hc₁₂)
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₃ h₂ hc₃₂)
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₃ hc₁₃) hL hN₁ hN₃ hC₁ hC₃

end WithLift

end CFSG.ClassicalInvolution.Models.Transfer
