module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.AutImageStar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerPermutable

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.AutImageStar

theorem autImageOK_of_quot {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hlay : IsRankTwoLayer M L) (E : Subgroup ↥M) [E.Normal]
    (hN : (GLBPrimeCore 3 M).subgroupOf M ≤ E)
    (hKN : L.subgroupOf M ⊓ E = (GLBPrimeCore 3 M).subgroupOf M)
    (hY : AutInOK ((L.subgroupOf M).map (QuotientGroup.mk' E))) :
    haveI : (starImg M L).Normal := normal_starImg hlay.2.2.1
    AutImageOK (starImg M L) := by
  have hNs : (starImg M L).Normal := normal_starImg hlay.2.2.1
  let φ := quotMapEquiv (L.subgroupOf M) _ _ hN hKN
  have hπ : Function.Surjective (quotMapHom _ _ hN) := by
    intro w
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective E w
    exact ⟨QuotientGroup.mk' _ m, rfl⟩
  have hYn : ((L.subgroupOf M).map (QuotientGroup.mk' E)).Normal :=
    Subgroup.Normal.map hlay.2.2.1 _ (QuotientGroup.mk'_surjective _)
  have hA := map_autImage_eq_autIn (starImg M L) _ (quotMapHom _ _ hN) hπ φ (fun n => rfl)
  have hI : (innSub ↥(starImg M L)).map (mulAutTransport φ).toMonoidHom =
      innSub ↥((L.subgroupOf M).map (QuotientGroup.mk' E)) :=
    innSub_map_transport φ
  have hrel : (innSub ↥((L.subgroupOf M).map (QuotientGroup.mk' E))).relIndex
      (autIn ((L.subgroupOf M).map (QuotientGroup.mk' E))) =
      (innSub ↥(starImg M L)).relIndex (autImage (starImg M L)) := by
    rw [← hI, ← hA]
    exact Subgroup.relIndex_map_map_of_injective _ _ (mulAutTransport φ).injective
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrel]
    exact hY.1
  · intro hA6 h2
    obtain ⟨eA⟩ := hA6
    obtain ⟨e⟩ := hY.2.1 ⟨φ.symm.trans eA⟩ (by rw [hrel]; exact h2)
    have eB : ↥(autImage (starImg M L)) ≃*
        ↥(autIn ((L.subgroupOf M).map (QuotientGroup.mk' E))) :=
      subgroupEquivOfMap (mulAutTransport φ) _ _ hA
    exact ⟨eB.trans e⟩
  · intro hS
    rw [← hrel]
    exact hY.2.2 (statedPSL_of_equiv φ hS)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
