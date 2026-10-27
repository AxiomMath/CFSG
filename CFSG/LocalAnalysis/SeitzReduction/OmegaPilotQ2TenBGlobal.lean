module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBField
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldCTGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Gen

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem iSup_perfectCore_centralizer_plusAnisoTorus_eq_top_of_three_le {m f : ℕ} (hm : 3 ≤ m)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ι : K →+* F) (hFf : Nat.card F = 2 ^ f)
    (hF : 4 ≤ Nat.card F) :
    ⨆ y : matrixProjectiveDerived (coordinateQuadPlus (m + 2) K),
      perfectCore (centralizer (((((plusAnisoTorus m hirr).map
        (plusAnisoProjEquiv m hirr).toMonoidHom).map (MulAut.conj y).toMonoidHom).map
        (fieldEmbed ι (m + 2) (by omega)) :
          Subgroup (matrixProjectiveDerived (coordinateQuadPlus (m + 2) F))) :
        Set (matrixProjectiveDerived (coordinateQuadPlus (m + 2) F)))) = ⊤ := by
  refine iSup_perfectCore_centralizer_eq_top (by omega) hFf hF _ fun j => ?_
  by_cases hj : 2 ≤ j.val
  · refine ⟨1, rationalNode_le_centralizer_of_le_suppBar _ j (P := lowPlanes m) ?_ ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_plusNodeSet] at hx
      rw [mem_lowPlanes] at hx'
      omega
    · rw [map_conj_one_eq]
      exact (map_mono (map_plusAnisoTorus_le_suppBar hirr)).trans
        (map_fieldEmbed_suppBar_le ι _ _)
  · refine ⟨projHom _ ⟨plusSwapLin K m hm, plusSwapLin_mem_orthDerived hm⟩,
      rationalNode_le_centralizer_of_le_suppBar _ j (P := midPlanes m) ?_ ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_plusNodeSet] at hx
      rw [mem_midPlanes] at hx'
      omega
    · exact (map_mono (map_conj_plusAnisoTorus_le_suppBar hm hirr)).trans
        (map_fieldEmbed_suppBar_le ι _ _)

end Gen

section Plus

@[expose] def OmegaPlusTwoTenFieldGlobalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoPerp (K := K) 3 b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))))).Normal →
        ∀ (htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoTorus 3 hirr) : Set G))
          (Kc : Subgroup (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G) ⧸ oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G)))),
          IsComponent Kc →
          OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoTorus 3 hirr) : Set G))) ⟨t, htX⟩)
            (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoPerp (K := K) 3 b c)).subgroupOf
                (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G))))) Kc 4 1 →
          Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoTorus 3 hirr) : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc →
          LieModel Kc .POmegaPlus 4 2 2 →
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
            Nonempty (anisoNeighbourJoin L (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr)) ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) F))

theorem omegaPlusTwoTenFieldLieInput_of_global (hglob : OmegaPlusTwoTenFieldGlobalInput) :
    OmegaPlusTwoTenFieldLieInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  obtain ⟨F', _, _, _, hF'4, ⟨ψ'⟩⟩ :=
    hglob G L hset K b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF4 : Nat.card F = 4 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι (f := 1) (by rw [hK2, pow_one]) hσ
      hfix]
    norm_num
  obtain ⟨χ⟩ := nonempty_plusModel_mulEquiv_of_card_eq (F := F) (F' := F')
    (by rw [hF'4, hF4]) (n := 3 + 2) (by omega)
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hXL := UnitaryPilot.modelToG_le (e.trans (plusAnisoProjEquiv 3 hirr).symm)
    (plusAnisoTorus 3 hirr)
  refine false_of_plusFieldGlobal hset (by norm_num) e ht hKt ι hσ hfix
    (mem_normalizer_anisoNeighbourJoin hXL htC) (ψ'.trans χ) (fun Φ hΦ => ?_)
  rw [modelToG_trans_symm]
  exact range_le_anisoNeighbourJoin e (fieldEmbed ι (3 + 2) (by omega)) _
    (iSup_perfectCore_centralizer_plusAnisoTorus_eq_top_of_three_le (f := 2) le_rfl hirr ι
      (by rw [hF4]; norm_num) (by omega)) hΦ

end Plus

end CFSG.SeitzReduction.OmegaPilot
