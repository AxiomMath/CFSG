module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlusConj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlusCentral
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlusInv
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlusGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGDispatch
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem kgConcl_coordinatePlus {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (p : ℕ) :
    KGConcl (matrixProjectiveDerived (coordinateQuadPlus n F)) p := by
  refine kgConcl_of_conj_le p (matrixProjectiveImage (coordinateQuadPlus n F)) ?_ ?_
  · intro S hS
    rcases Nat.lt_or_ge n 5 with h4 | h5
    · obtain rfl : n = 4 := by omega
      exact CFSG.ComponentClassification.RankTwoHypIIOrthogonal.exists_conj_le_image_plus_four
        hf hF S hS
    · refine ⟨1, ?_⟩
      rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus F n h5]
      exact le_top
  · intro S B hSE hS2 hnc hSI hB
    have hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht =>
      commute_of_mem_image hn hf hF hSE hSI hs ht
    obtain ⟨g₁, g₂, hg₁S, hg₂S, hg₁1, hg₂1, hσ1, hσσ, hTQ, hTT, hg₂r, hAQ, hAA', hAT'⟩ :=
      exists_field_and_linear_involution hn hf hF hSE hSI hS2 hcomm hnc
    refine ⟨matrixProjectiveConjugationHom (coordinateQuadPlus n F) g₁,
      matrixProjectiveConjugationHom (coordinateQuadPlus n F) g₂, hg₁S, hg₂S, hg₁1, hg₂1,
      fun τ hτ => hcomm τ hτ _ hg₁S, fun τ hτ => hcomm τ hτ _ hg₂S,
      fun τ hτ => commute_of_mem_normalizer hn hf hF hSE hSI hnc (hB hτ) hg₁S,
      fun τ hτ => commute_of_mem_normalizer hn hf hF hSE hSI hnc (hB hτ) hg₂S, ?_⟩
    let T : (Fin (2 * n) → F) →ₛₗ[(g₁.val.right : F →+* F)] (Fin (2 * n) → F) :=
      { toFun := coordinateSemilinearMap g₁.val
        map_add' := map_add (coordinateSemilinearMap g₁.val)
        map_smul' := coordinateSemilinearMap_smul g₁.val }
    set A := matrixLinearIso g₂.val.left
    have hA2 : ∀ v, coordinateSemilinearMap g₂.val v = A v := fun v => by
      rw [coordinateSemilinearMap_apply, hg₂r]
      rfl
    have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n F) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        rw [← hA2]
        exact hAQ v
    have hAA : A * A = 1 := LinearEquiv.ext fun v => by
      rw [LinearEquiv.mul_apply, ← hA2, ← hA2]
      exact hAA' v
    have hAT : ∀ v, A (T v) = T (A v) := fun v => by
      rw [← hA2, ← hA2]
      exact hAT' v
    have hreg := regular_coordinateQuadPlus n F (by omega)
    refine eq_top_of_fix_semilinear_linear hn hreg.1
      (commutator_coordinateQuadPlus n F (by omega)).symm hσσ hσ1 (T := T) hTT hTQ hAO hAA hAT
      (fun X hX => ?_) (fun X hX => ?_)
    · refine Subgroup.subset_closure (Set.mem_union_left _ ?_)
      exact matrixProjectiveConjugationHom_apply_eq_of_commute g₁ X fun v => (hX v).symm
    · refine Subgroup.subset_closure (Set.mem_union_right _ ?_)
      refine matrixProjectiveConjugationHom_apply_eq_of_commute g₂ X fun v => ?_
      rw [hA2, hA2]
      exact (DFunLike.congr_fun hX v).symm

theorem kgConclPOmegaPlus_holds : FongKGG.KGConclPOmegaPlus := by
  intro K _ _ n f hn h p
  obtain ⟨⟨-, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  exact FongOut.kgConcl_of_mulEquiv (coordinatePlusWitnessEquiv F e)
    (kgConcl_coordinatePlus hn hf hF p)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus
