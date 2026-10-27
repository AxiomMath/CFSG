module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointRoot
public import CFSG.StronglyEmbedded.BenderNormalSeries

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem original_local_hull_involutionCore_eq_top
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (u : G) :
    involutionCore (localInvolutionPointHull z u) = ⊤ := by
  let L := localInvolutionPointHull z u
  apply top_unique
  intro x _hx
  refine Subgroup.closure_induction
    (p := fun y hy => (⟨y, hy⟩ : L) ∈ involutionCore L)
    ?_ ?_ ?_ ?_ x.property
  · intro y hy
    apply Subgroup.subset_closure
    have hyorder : orderOf y = 2 :=
      order_two_of_mem_pointClass h.distinguished_order hy.1
    exact IsInvolution.subtype
      ⟨(orderOf_eq_prime_iff.mp hyorder).2, (orderOf_eq_prime_iff.mp hyorder).1⟩
      (Subgroup.subset_closure hy)
  · exact (involutionCore L).one_mem
  · intro a b _ha _hb hca hcb
    exact (involutionCore L).mul_mem hca hcb
  · intro a _ha hca
    exact (involutionCore L).inv_mem hca

theorem whole_involution_core_native_model_and_borel
    (P : Subgroup G) (hP : fusionStronglyEmbedded P)
    (hrank : TwoRankAtLeastTwo G) (hcore : involutionCore G = ⊤) :
    IsSimpleBenderGroup (G ⧸ CFSG.oddCore G) ∧
      CFSG.oddCore G ≤ P ∧
      IsBorelSubgroup (P.map (QuotientGroup.mk' (CFSG.oddCore G))) := by
  have hSE := theorem_SE P hP.to_native
  rcases hSE with hlow | hmodel
  · exact (hlow (twoRankAtLeastTwo_involutionCore_iff.mpr hrank)).elim
  · let C : Subgroup G := involutionCore G
    let e : C ≃* G := (MulEquiv.subgroupCongr hcore).trans Subgroup.topEquiv
    have he : e.toMonoidHom = C.subtype := by
      ext x
      rfl
    have hOmap : (twoPrimeCore C).map e.toMonoidHom = CFSG.oddCore G := by
      rw [oddCore_eq_twoPrimeCore]
      simpa only [twoPrimeCore] using pPrimeCore_map_iso 2 e
    let q := QuotientGroup.congr (twoPrimeCore C) (CFSG.oddCore G) e hOmap
    let PC : Subgroup C := (P ⊓ C).subgroupOf C
    have hPCmap : PC.map e.toMonoidHom = P := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact hc.1
      · intro hx
        have hxC : x ∈ C := by
          change x ∈ involutionCore G
          rw [hcore]
          exact Subgroup.mem_top x
        exact ⟨⟨x, hxC⟩, ⟨hx, hxC⟩, rfl⟩
    have hqcomp : q.toMonoidHom.comp (QuotientGroup.mk' (twoPrimeCore C)) =
        (QuotientGroup.mk' (CFSG.oddCore G)).comp e.toMonoidHom := by
      ext c
      exact QuotientGroup.congr_mk' (twoPrimeCore C) (CFSG.oddCore G) e hOmap c
    have hBmap :
        (PC.map (QuotientGroup.mk' (twoPrimeCore C))).map q.toMonoidHom =
          P.map (QuotientGroup.mk' (CFSG.oddCore G)) := by
      rw [Subgroup.map_map, hqcomp, ← Subgroup.map_map, hPCmap]
    have hB : IsBorelSubgroup (PC.map (QuotientGroup.mk' (twoPrimeCore C))) :=
      hmodel.2.2
    have hO : CFSG.oddCore G ≤ P := by
      rw [← hOmap, he]
      exact hmodel.2.1.trans inf_le_left
    exact ⟨hmodel.1.map_mulEquiv q, hO, hBmap ▸ hB.map_mulEquiv q⟩

theorem original_local_hull_native_model_and_borel
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    IsSimpleBenderGroup (L ⧸ CFSG.oddCore L) ∧
      CFSG.oddCore L ≤ H.subgroupOf L ∧
      IsBorelSubgroup ((H.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore L))) := by
  exact whole_involution_core_native_model_and_borel
    (H.subgroupOf (localInvolutionPointHull z u))
    (h.local_embedding u hu huz hescape)
    (native_rank_two_of_two_le_twoRank hrank)
    (original_local_hull_involutionCore_eq_top h u)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
