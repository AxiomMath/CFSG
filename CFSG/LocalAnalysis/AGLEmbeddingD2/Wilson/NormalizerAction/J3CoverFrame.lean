module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3E27

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table CFSG.Blueprint Subgroup

theorem zw_mem_rels : zw ∈ j3CoverRels := by
  simp [zw, j3CoverRels]

theorem j3_frame_card
    (hchk : GammaWordFacts)
    {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (hZ3 : Nat.card (center X) = 3) (e : X ⧸ center X ≃* NativeSporadic.J3)
    {F : Subgroup X} (hF : IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))))
    (hZF : center X ≤ F)
    (hF81 : Nat.card F = 81) :
    ∃ k : Fin 6 → X, J3Pkg k ∧ F = F0 k ∧
      (∀ y ∈ normalizer (F : Set X), y ∈ Subgroup.closure (Set.range k)) ∧
      Nat.card (Subgroup.closure (Set.range k)) = 5832 := by
  obtain ⟨k0, hrel, hker0, hcard0, hmap0, hcardH0, hzc, φ, hinj, hφ⟩ :=
    j3_cover_setup hX hZ3 e
  obtain ⟨heq, hmv⟩ := eq_ne_of_gammaWordFacts hchk k0 φ hinj hφ
  have hpkg : J3Pkg k0 :=
    ⟨heq, hmv, hzc zw zw_mem_rels⟩
  have hker : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  have hH : Nat.card ((Subgroup.closure (Set.range k0)).map (QuotientGroup.mk' (center X))) =
      1944 := by
    rw [hmap0]; exact hcardH0
  obtain ⟨t, hFt, hnorm⟩ := cover_core (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) hker hZ3
    (fun A A' hA hA' h27 h27' => j3_e27_conj e hA hA' h27 h27')
    (fun A hA h27 => j3_e27_card_normalizer e hA h27) hpkg hker0 hH hF hZF hF81
  refine ⟨_, hpkg.conj t, hFt, hnorm, ?_⟩
  have hcl : Subgroup.closure (Set.range fun i => t * k0 i * t⁻¹) =
      (Subgroup.closure (Set.range k0)).map (MulAut.conj t).toMonoidHom := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    congr 2
  rw [hcl, Subgroup.card_map_of_injective (MulAut.conj t).injective, hcard0]

theorem j3_frame
    (hchk : GammaWordFacts)
    {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (hZ3 : Nat.card (center X) = 3) (e : X ⧸ center X ≃* NativeSporadic.J3)
    {F : Subgroup X} (hF : IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))))
    (hZF : center X ≤ F)
    (hF81 : Nat.card F = 81) :
    ∃ k : Fin 6 → X, J3Pkg k ∧ F = F0 k ∧
      ∀ y ∈ normalizer (F : Set X), y ∈ Subgroup.closure (Set.range k) := by
  obtain ⟨k, hk, hFk, hnorm, -⟩ := j3_frame_card hchk hX hZ3 e hF hZF hF81
  exact ⟨k, hk, hFk, hnorm⟩

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
