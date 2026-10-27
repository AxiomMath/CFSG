module

public import CFSG.ClassicalInvolution.Asc77.AscAETSecFinal
public import CFSG.ClassicalInvolution.Asc77.AscAETWeak
public import CFSG.ClassicalInvolution.Asc77.AscAETShape
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinMain

public section

namespace CFSG.ClassicalInvolution.Asc77.AscAET

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.T3

section Conj

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem omegaOfSet_conj (hΩ : ConjInvariant Ω) {M L : Subgroup G}
    (hL : L ∈ omegaOfSet Ω (twinSet Ω M)) (g : G) :
    conjSub g L ∈ omegaOfSet Ω (twinSet Ω (conjSub g M)) := by
  refine ⟨hΩ g L hL.1, fun K' hK' => ?_⟩
  have h1 : conjSub g⁻¹ K' ∈ twinSet Ω M := by
    have := twinSet_conj hΩ hK' g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have h2 := omegaNbr_conj hΩ (hL.2 _ h1) g
  rwa [conjSub_conjSub_inv] at h2

end Conj

variable {p f : ℕ} [Fact p.Prime]

theorem aEmptyTwinExact_proved (hΩall : HypOmegaModAll p f) : AEmptyTwinExact p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hshape M hM
  have hΩK : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩall G hnab hp2 hq K z hz hBelow
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hall : ∀ J ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = J := by
    rintro J ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hKz : IsUniqueInvolution K z := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one
  have hA : AEmpty (CoreAssembly.conjClass K) K := by
    by_contra hn
    obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hn
    obtain ⟨M₀, hM₀, L₀, hL₀⟩ :=
      exists_omegaOfSet_nonempty_of_twinExactShape hp2 hq hΩK hz hshape
    obtain ⟨h, hh⟩ := hall L₀ hL₀.1
    have hKW : K ∈ omegaOfSet (CoreAssembly.conjClass K)
        (twinSet (CoreAssembly.conjClass K) (conjSub h⁻¹ M₀)) := by
      have := omegaOfSet_conj hΩK.conjInvariant hL₀ h⁻¹
      rwa [← hh, conjSub_inv_conjSub] at this
    have hM'Ω : conjSub h⁻¹ M₀ ∈ CoreAssembly.conjClass K := hΩK.conjInvariant h⁻¹ M₀ hM₀
    obtain ⟨g, hg⟩ := hall _ hM'Ω
    have hv' := hv.conj hΩK.conjInvariant g
    rw [hg] at hv'
    obtain ⟨J', zJ', hv'', hMc, hJc⟩ :=
      exists_weak_transfer hp2 hq hΩK hM'Ω hv' hKW hKz
    obtain ⟨D₀, hD₀⟩ := hshape.1
    exact false_of_aViol_twinShape hp2 hq hΩK hc2 D₀ hD₀ hM'Ω hv'' hMc hJc
  exact aEmpty_forall_of_transitive' hΩK.conjInvariant hall hA M hM

end CFSG.ClassicalInvolution.Asc77.AscAET
