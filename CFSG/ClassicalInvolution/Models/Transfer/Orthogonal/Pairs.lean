module

public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Image

public section

namespace CFSG.ClassicalInvolution.Models.Transfer

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {X : Type} [Group X] [Finite K] {θ : ↥(elementaryGroup Q) →* X}
  {L₁ L₂ L₃ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ i₃ : V ≃ₗ[K] V}

section Lifts

variable (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q))

include hker

theorem map_mem_centralizer_iff_fundamental (h4 : 4 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    {g : ↥(elementaryGroup Q)} :
    θ g ∈ Subgroup.centralizer (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) :
      Set X) ↔ (g : V ≃ₗ[K] V) ∈ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)) := by
  rw [← mem_centralizer_subgroupOf_iff h₁.le_elementaryGroup]
  refine ⟨mem_centralizer_of_map hker (commutator_subgroupOf_eq_of_isFundamental h4 h₁), ?_⟩
  intro hg
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hg x hx]

theorem map_mem_normalizer_iff_fundamental (h4 : 4 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    {g : ↥(elementaryGroup Q)} :
    θ g ∈ Subgroup.normalizer (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) :
      Set X) ↔ (g : V ≃ₗ[K] V) ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)) := by
  rw [← mem_normalizer_subgroupOf_iff h₁.le_elementaryGroup]
  exact ⟨mem_normalizer_of_map hker (commutator_subgroupOf_eq_of_isFundamental h4 h₁),
    map_mem_normalizer θ⟩

omit [Finite K] hker in
theorem map_fundElt_mem (h₂ : IsFundamental Q L₂ i₂) :
    θ (fundElt h₂) ∈ (L₂.subgroupOf (elementaryGroup Q)).map θ :=
  ⟨fundElt h₂, Subgroup.mem_subgroupOf.mpr h₂.mem, rfl⟩

theorem commute_iff_map_of_commute (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hne : (L₁.subgroupOf (elementaryGroup Q)).map θ ≠
      (L₂.subgroupOf (elementaryGroup Q)).map θ) :
    (∀ x ∈ (L₁.subgroupOf (elementaryGroup Q)).map θ,
        ∀ y ∈ (L₂.subgroupOf (elementaryGroup Q)).map θ, x * y = y * x) ↔
      θ (fundElt h₂) ∈ Subgroup.centralizer
        (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X) := by
  have hne' : L₁ ≠ L₂ := fun e => hne (by rw [e])
  refine (mem_centralizer_map_iff hker
    (commutator_subgroupOf_eq_of_isFundamental (by omega) h₁)
    (Subgroup.mem_subgroupOf.mpr h₂.mem) ?_).symm
  rw [mem_centralizer_subgroupOf_iff h₁.le_elementaryGroup,
    forall_comm_subgroupOf_iff h₁.le_elementaryGroup h₂.le_elementaryGroup]
  exact (IsFundamental.commute_iff hodd h₁ h₂ hc hne').symm

theorem mem_normalizer_map_iff_even_of_commute (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁) :
    θ (fundElt h₂) ∈ Subgroup.normalizer
        (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X) ↔
      Even (Module.finrank K ↥(negSpace i₁ ⊓ negSpace i₂)) := by
  rw [map_mem_normalizer_iff_fundamental hker (by omega) h₁]
  exact mem_normalizer_iff_even hodd h₁ h₂ hc

omit hker in
theorem exists_hom_of_lemma_6_10 [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hs : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    ∃ θ₀ : SL(3, K) →* (V ≃ₗ[K] V), Function.Injective θ₀ ∧ θ₀.range = L₁ ⊔ L₂ ∧
      (B12 K).map θ₀ = L₁ ∧ (B23 K).map θ₀ = L₂ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  have hdim' := Frame.finrank_inf_span_eq_two h2 hc.symm (conjSubgroup_eq_of_mem_normalizer hN)
    (exists_ne_of_not_mem_centralizer hC)
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hs
  exact Frame.exists_hom_of_hasSingularVector h2 hc.symm hdim' hs

theorem lemma_6_10_map_of_commute [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂)
    (hc : i₁ * i₂ = i₂ * i₁)
    (hN : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X)) :
    PairDecomposition Q i₁ i₂ ∧
      (HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) →
        LinearBlockStandardPair K ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₁.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ)) := by
  have hN' : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)) :=
    (map_mem_normalizer_iff_fundamental hker (by omega) h₁).mp hN
  have hC' : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)) := fun hmem =>
    hC ((map_mem_centralizer_iff_fundamental hker (by omega) h₁).mpr hmem)
  refine ⟨(lemma_6_10 hodd h₁ h₂ hc hN' hC').1, fun hs => ?_⟩
  obtain ⟨θ₀, hinj, hrange, hU, hV⟩ := exists_hom_of_lemma_6_10 hodd h₁ h₂ hc hN' hC' hs
  obtain ⟨ρ, hρinj, hρrange, hρ₁, hρ₂⟩ := exists_hom_subgroupOf h₁.le_elementaryGroup
    h₂.le_elementaryGroup (B12 K) (B23 K) θ₀ hinj hrange hU hV
  refine linearBlockStandardPair_of_normalized (θ := θ.comp ρ)
    (ker_comp_le_center ρ hρinj hker) ?_ ?_ ?_
  · rw [MonoidHom.range_comp, hρrange, Subgroup.map_sup]
  · rw [← Subgroup.map_map, hρ₁]
  · rw [← Subgroup.map_map, hρ₂]

theorem lemma_6_10_third_map_of_commute [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂)
    (hc : i₁ * i₂ = i₂ * i₁)
    (hN : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hs : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    ∃ (L₃ : Subgroup (V ≃ₗ[K] V)) (i₃ : V ≃ₗ[K] V) (h₃ : IsFundamental Q L₃ i₃),
      θ (fundElt h₃) = θ (fundElt h₁) * θ (fundElt h₂) ∧
        (L₃.subgroupOf (elementaryGroup Q)).map θ ≤
          (L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
            (L₂.subgroupOf (elementaryGroup Q)).map θ := by
  have hN' : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)) :=
    (map_mem_normalizer_iff_fundamental hker (by omega) h₁).mp hN
  have hC' : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)) := fun hmem =>
    hC ((map_mem_centralizer_iff_fundamental hker (by omega) h₁).mpr hmem)
  obtain ⟨L₃, h₃, hle⟩ := lemma_6_10_third hodd h₁ h₂ hc hN' hC' hs
  refine ⟨L₃, i₁ * i₂, h₃, ?_, ?_⟩
  · rw [← map_mul]
    exact congrArg θ (Subtype.ext rfl)
  · rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup h₁.le_elementaryGroup h₂.le_elementaryGroup]
    refine Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr ?_
    exact hle (Subgroup.mem_subgroupOf.mp hx)

theorem lemma_6_11_map_of_commute [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K)
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (h₃ : IsFundamental Q L₃ i₃)
    (h₁₂ : i₁ * i₂ = i₂ * i₁) (h₃₂ : i₃ * i₂ = i₂ * i₃) (h₁₃ : i₁ * i₃ = i₃ * i₁)
    (hK : ∀ x ∈ (L₁.subgroupOf (elementaryGroup Q)).map θ,
      ∀ y ∈ (L₃.subgroupOf (elementaryGroup Q)).map θ, x * y = y * x)
    (hN₁ : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hN₃ : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₃.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC₁ : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC₃ : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₃.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X)) :
    HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ↔
      HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) := by
  have h4 : 4 ≤ Nat.card K := by omega
  refine lemma_6_11 hodd h₁ h₂ h₃ h₁₂ h₃₂ h₁₃ ?_
    ((map_mem_normalizer_iff_fundamental hker h4 h₁).mp hN₁)
    ((map_mem_normalizer_iff_fundamental hker h4 h₃).mp hN₃)
    (fun hmem => hC₁ ((map_mem_centralizer_iff_fundamental hker h4 h₁).mpr hmem))
    (fun hmem => hC₃ ((map_mem_centralizer_iff_fundamental hker h4 h₃).mpr hmem))
  refine (forall_comm_subgroupOf_iff h₁.le_elementaryGroup h₃.le_elementaryGroup).mp ?_
  intro x hx y hy
  have hy' : θ y ∈ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => hK z hz (θ y) ⟨y, hy, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp
    (mem_centralizer_of_map hker (commutator_subgroupOf_eq_of_isFundamental h4 h₁) hy') x hx)

end Lifts

section WithLift

variable [FiniteDimensional K V] (hodd : Odd (Nat.card K))
  (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q)) (hZ : CenterScalar Q)
  (hdim : 4 < Module.finrank K V) (hlift : Module.finrank K V ≠ 8 ∨ KerInvolutionFree θ)

include hodd hker hZ hdim hlift

theorem commute_of_map_commute_fundElt (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : Commute (θ (fundElt h₁)) (θ (fundElt h₂))) :
    i₁ * i₂ = i₂ * i₁ :=
  congrArg Subtype.val
    (commute_of_commute_map θ (kerConjFree_of_isFundamental hodd hker hZ hdim hlift h₂) hc).eq

theorem commute_iff_map (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : Commute (θ (fundElt h₁)) (θ (fundElt h₂)))
    (hne : (L₁.subgroupOf (elementaryGroup Q)).map θ ≠
      (L₂.subgroupOf (elementaryGroup Q)).map θ) :
    (∀ x ∈ (L₁.subgroupOf (elementaryGroup Q)).map θ,
        ∀ y ∈ (L₂.subgroupOf (elementaryGroup Q)).map θ, x * y = y * x) ↔
      θ (fundElt h₂) ∈ Subgroup.centralizer
        (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X) :=
  commute_iff_map_of_commute hker hodd h5 h₁ h₂
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₂ hc) hne

theorem mem_normalizer_map_iff_even (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : Commute (θ (fundElt h₁)) (θ (fundElt h₂))) :
    θ (fundElt h₂) ∈ Subgroup.normalizer
        (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X) ↔
      Even (Module.finrank K ↥(negSpace i₁ ⊓ negSpace i₂)) :=
  mem_normalizer_map_iff_even_of_commute hker hodd h5 h₁ h₂
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₂ hc)

theorem lemma_6_10_map (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : Commute (θ (fundElt h₁)) (θ (fundElt h₂)))
    (hN : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X)) :
    PairDecomposition Q i₁ i₂ ∧
      (HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) →
        LinearBlockStandardPair K ((L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
          (L₂.subgroupOf (elementaryGroup Q)).map θ)
          ((L₁.subgroupOf (elementaryGroup Q)).map θ)
          ((L₂.subgroupOf (elementaryGroup Q)).map θ)) :=
  lemma_6_10_map_of_commute hker hodd h5 h₁ h₂
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₂ hc) hN hC

theorem lemma_6_10_third_map (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : Commute (θ (fundElt h₁)) (θ (fundElt h₂)))
    (hN : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hs : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    ∃ (L₃ : Subgroup (V ≃ₗ[K] V)) (i₃ : V ≃ₗ[K] V) (h₃ : IsFundamental Q L₃ i₃),
      θ (fundElt h₃) = θ (fundElt h₁) * θ (fundElt h₂) ∧
        (L₃.subgroupOf (elementaryGroup Q)).map θ ≤
          (L₁.subgroupOf (elementaryGroup Q)).map θ ⊔
            (L₂.subgroupOf (elementaryGroup Q)).map θ :=
  lemma_6_10_third_map_of_commute hker hodd h5 h₁ h₂
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₂ hc) hN hC hs

theorem lemma_6_11_map (h5 : 5 ≤ Nat.card K) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (h₃ : IsFundamental Q L₃ i₃)
    (hc₁₂ : Commute (θ (fundElt h₁)) (θ (fundElt h₂)))
    (hc₃₂ : Commute (θ (fundElt h₃)) (θ (fundElt h₂)))
    (hc₁₃ : Commute (θ (fundElt h₁)) (θ (fundElt h₃)))
    (hK : ∀ x ∈ (L₁.subgroupOf (elementaryGroup Q)).map θ,
      ∀ y ∈ (L₃.subgroupOf (elementaryGroup Q)).map θ, x * y = y * x)
    (hN₁ : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hN₃ : θ (fundElt h₂) ∈ Subgroup.normalizer
      (((L₃.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC₁ : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₁.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X))
    (hC₃ : θ (fundElt h₂) ∉ Subgroup.centralizer
      (((L₃.subgroupOf (elementaryGroup Q)).map θ : Subgroup X) : Set X)) :
    HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ↔
      HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) :=
  lemma_6_11_map_of_commute hker hodd h5 h₁ h₂ h₃
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₂ hc₁₂)
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₃ h₂ hc₃₂)
    (commute_of_map_commute_fundElt hodd hker hZ hdim hlift h₁ h₃ hc₁₃) hK hN₁ hN₃ hC₁ hC₃

end WithLift

end CFSG.ClassicalInvolution.Models.Transfer
