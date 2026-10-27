module


public import CFSG.LargeExtraspecial.BridgeNat
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimeCoreNaturality.PrimeCoreNaturality
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerNaturality.LayerNaturality
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosureNaturality.WeakClosureNaturality
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.FrobeniusProductNaturality.FrobeniusProductNaturality

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBMap

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem clauseB_map (e : MulAut G) {M P : Subgroup G} {p : ℕ} (h : rankThreeClauseB M P p) :
    rankThreeClauseB (M.map e.toMonoidHom) (P.map e.toMonoidHom) p := by
  obtain ⟨h5, hsol, P₀, hP₀P, hcard, hclosed, ⟨hpr, m, hm, ⟨iso⟩⟩, hnle, hfrob, hY⟩ := h
  have hcent := CFSG.RankThreeCoreUniqueness.Helpers.centralizer_map_automorphism
    (P₀ : Subgroup G) e
  have hlay : rankThreeLayer (Subgroup.centralizer ((P₀.map e.toMonoidHom : Subgroup G) : Set G)) =
      (rankThreeLayer (Subgroup.centralizer (P₀ : Set G))).map e.toMonoidHom := by
    rw [← hcent, CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerNaturality.map_layer]
  refine ⟨h5, ?_, P₀.map e.toMonoidHom, Subgroup.map_mono hP₀P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hsol
    exact solvable_of_surjective
      (f := (M.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (M.equivMapOfInjective e.toMonoidHom e.injective).surjective
  · rw [Subgroup.card_map_of_injective e.injective]; exact hcard
  · exact CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosureNaturality.map_weaklyClosed e hclosed
  · refine ⟨hpr, m, hm, ⟨?_⟩⟩
    rw [hlay]
    exact ((rankThreeLayer (Subgroup.centralizer (P₀ : Set G))).equivMapOfInjective
      e.toMonoidHom e.injective).symm.trans iso
  · rw [hlay]
    intro hle
    exact hnle ((Subgroup.map_le_map_iff_of_injective e.injective).1 hle)
  · rw [hlay, CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimeCoreNaturality.map_primeCore,
      CFSG.LargeExtraspecial.Bridge.pCoreOf_map 2 e M,
      ← CFSG.RankThreeCoreUniqueness.Helpers.centralizer_map_automorphism]
    exact CFSG.LocalAnalysis.RankThreeUC.ProofSupport.FrobeniusProductNaturality.map_product e hfrob
  · intro Y hYP hYc hYne
    have hsy : (Y.map e.symm.toMonoidHom).map e.toMonoidHom = Y := by
      rw [Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by ext x; simp
      rw [this, Subgroup.map_id]
    have h1 : Y.map e.symm.toMonoidHom ≤ P := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hYP
      rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G by
        ext x; simp, Subgroup.map_id] at this
    have h2 : Nat.card (Y.map e.symm.toMonoidHom) = p := by
      rw [Subgroup.card_map_of_injective e.symm.injective]; exact hYc
    have h3 : Y.map e.symm.toMonoidHom ≠ P₀ := by
      intro hh
      apply hYne
      rw [← hsy, hh]
    have h4 := hY _ h1 h2 h3
    have h5 := Subgroup.map_mono (f := e.toMonoidHom) h4
    rwa [Subgroup.map_equiv_normalizer_eq, hsy] at h5

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBMap
