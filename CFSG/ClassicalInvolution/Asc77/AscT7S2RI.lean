module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RF
public import CFSG.ClassicalInvolution.Asc77.AscT7AEnd

public section

namespace CFSG.ClassicalInvolution.Asc77.T7S2R

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Spin

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem normalizer_sup_eq_top (hperf : Group.IsPerfect (spinGroup Q))
    (hrange : (spinAction Q).range = elementaryGroup Q) {R₁ R₂ : Subgroup (spinGroup Q)}
    (hR₁ : ⁅R₁, R₁⁆ = R₁) (hR₂ : ⁅R₂, R₂⁆ = R₂)
    (hgen : elementaryGroup Q ≤
      normE Q (R₁.map (spinAction Q)) ⊔ normE Q (R₂.map (spinAction Q))) :
    Subgroup.normalizer (R₁ : Set (spinGroup Q)) ⊔ Subgroup.normalizer (R₂ : Set (spinGroup Q)) =
      ⊤ := by
  have hker := ker_spinAction_le_center Q
  have hle : ∀ R : Subgroup (spinGroup Q), ⁅R, R⁆ = R →
      normE Q (R.map (spinAction Q)) ≤
        (Subgroup.normalizer (R : Set (spinGroup Q))).map (spinAction Q) := by
    intro R hR g hg
    have hgE : g ∈ (spinAction Q).range := by rw [hrange]; exact hg.2
    obtain ⟨x, hx⟩ := hgE
    refine ⟨x, Models.Transfer.mem_normalizer_of_map hker hR ?_, hx⟩
    rw [hx]
    exact hg.1
  have := hperf
  refine eq_top_of_range_le_map (spinAction Q) hker ?_
  rw [hrange]
  refine hgen.trans (sup_le ?_ ?_)
  · exact (hle R₁ hR₁).trans (Subgroup.map_mono le_sup_left)
  · exact (hle R₂ hR₂).trans (Subgroup.map_mono le_sup_right)

end Spin

section Graph

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem normalizer_le_sigmaStarNorm_of_mem_dstarComp (hΩ : ConjInvariant Ω) {K M : Subgroup G}
    (hK : K ∈ Ω) (hM : M ∈ dstarComp Ω K) :
    Subgroup.normalizer (M : Set G) ≤ sigmaStarNorm Ω K := by
  intro x hx
  have hMΩ : M ∈ Ω := (T3.mem_dstarComp_symm hK hM).1
  have hxM : conjSub x M ∈ dstarComp Ω M := by
    rw [mem_normalizer_iff_conjSub_eq.mp hx]
    exact Relation.ReflTransGen.refl
  have h1 : x ∈ sigmaStarNorm Ω M := T7A.mem_sigmaStarNorm_of_conj hΩ hMΩ hxM
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hM)] at h1

theorem dstarConnected_of_normalizers (hΩ : ConjInvariant Ω)
    (htrans : ∀ A ∈ Ω, ∀ B ∈ Ω, ∃ g : G, conjSub g A = B) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ dstarComp Ω K)
    (hgen : Subgroup.normalizer (K : Set G) ⊔ Subgroup.normalizer (J : Set G) = ⊤) :
    T3.DStarConnected Ω := by
  refine T3.dstarConnected_of_pivot hK fun B hB => ?_
  obtain ⟨g, hg⟩ := htrans K hK B hB
  have hle : Subgroup.normalizer (K : Set G) ⊔ Subgroup.normalizer (J : Set G) ≤
      sigmaStarNorm Ω K :=
    sup_le (normalizer_le_sigmaStarNorm_of_mem_dstarComp hΩ hK Relation.ReflTransGen.refl)
      (normalizer_le_sigmaStarNorm_of_mem_dstarComp hΩ hK hJ)
  have hgN : g ∈ sigmaStarNorm Ω K := hle (by rw [hgen]; exact Subgroup.mem_top g)
  have h1 := (mem_sigmaStarNorm_iff.mp hgN K).mp Relation.ReflTransGen.refl
  rwa [hg] at h1

theorem normalizer_map_sup_eq_top {K₀ : Type} [Group K₀] (ψ : K₀ →* G)
    (hsurj : Function.Surjective ψ) {R₁ R₂ : Subgroup K₀}
    (h : Subgroup.normalizer (R₁ : Set K₀) ⊔ Subgroup.normalizer (R₂ : Set K₀) = ⊤) :
    Subgroup.normalizer ((R₁.map ψ : Subgroup G) : Set G) ⊔
      Subgroup.normalizer ((R₂.map ψ : Subgroup G) : Set G) = ⊤ := by
  have h1 : (⊤ : Subgroup G) = (⊤ : Subgroup K₀).map ψ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj]
  rw [eq_top_iff, h1, ← h, Subgroup.map_sup]
  exact sup_le_sup
    (Subgroup.map_le_iff_le_comap.mpr fun x hx => Models.Transfer.map_mem_normalizer ψ hx)
    (Subgroup.map_le_iff_le_comap.mpr fun x hx => Models.Transfer.map_mem_normalizer ψ hx)

end Graph

end CFSG.ClassicalInvolution.Asc77.T7S2R
