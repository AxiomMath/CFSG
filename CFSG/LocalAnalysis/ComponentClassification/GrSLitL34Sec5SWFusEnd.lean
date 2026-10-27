module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWFus
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWNon

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

theorem exists_conj_of_le_withKernel {G : Type} [Group G] [Finite G] {a x : G}
    {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (h3 : IsThreeConnected (S ⊓ withKernel J))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) {g : G} {E : Subgroup G} (hES : E ≤ S)
    (hEK : E ≤ withKernel J) (hE : IsEightGroup E) (hbE : g⁻¹ * a * g ∈ E) :
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m := by
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJper : ⁅J, J⁆ = J :=
    UnbalancedCorr.commutator_eq_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  obtain ⟨D⟩ := exists_wStd hJper hL34 (GrS4.isSylowTwoIn_inf hS) hS.1
  obtain ⟨F₁, F₂, hF₁S, hF₂S, hF₁, hF₂, hne⟩ := D.exists_two_eights hS2
  have hPS₁ : S ⊓ J ≤ S ⊓ withKernel J := inf_le_inf_left _ le_sup_left
  obtain ⟨s₀, hs₀S, hs₀2, hs₀E, hs₀n⟩ := exists_not_isolated_of_threeConnected h3
    (hF₁S.trans hPS₁) (hF₂S.trans hPS₁) hF₁ hF₂ hne (le_inf hES hEK) hE
  exact exists_conj_of_not_isolated hset hcent hWB hSyl hES hE (fun e he => hE.1.1 e he _ hbE)
    (mem_inf.mp hs₀S).1 hs₀2 hs₀E hs₀n (hs₀E _ hbE)

theorem exists_conj_of_mem_withKernel {G : Type} [Group G] [Finite G] {a x : G}
    {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (h3 : IsThreeConnected (S ⊓ withKernel J))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) {g : G} (hgS : g⁻¹ * a * g ∈ S)
    (hgK : g⁻¹ * a * g ∈ withKernel J) :
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m := by
  by_cases hga : g⁻¹ * a * g = a
  · exact ⟨1, one_mem _, by rw [hga]; group⟩
  obtain ⟨c, hc, E, hES, hE, hbE, -, hK, -⟩ := exists_eight_of_conj hset hcent hgS hga
  have hgc : (g * c)⁻¹ * a * (g * c) = c⁻¹ * (g⁻¹ * a * g) * c := by group
  obtain ⟨m, hm, hbm⟩ := exists_conj_of_le_withKernel hset hcent h3 hWB hSyl (g := g * c) hES
    (hK hgK) hE (hgc ▸ hbE)
  refine ⟨m * c⁻¹, mul_mem hm (hNJ (inv_mem (mem_inf.mp hc).1)), ?_⟩
  calc g⁻¹ * a * g = c * ((g * c)⁻¹ * a * (g * c)) * c⁻¹ := by group
    _ = (m * c⁻¹)⁻¹ * a * (m * c⁻¹) := by rw [hbm]; group

end CFSG.ComponentClassification.GrSLit.GrS5S
