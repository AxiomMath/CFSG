module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenRNodes
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBGlobalMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBGlobal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

@[expose] def OmegaMinusTwoTenFieldFrameGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))).Normal →
        ∀ (htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))
          (Kc : Subgroup (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) :
              Set G) ⧸ oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G)))),
          IsComponent Kc →
          OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))) Kc 4 1 →
          Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G)))
                ⟨t, htX⟩)).toMonoidHom = Kc →
          LieModel Kc .POmegaPlus 4 2 2 →
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
            Q2FrameDataGen L (modelToG e (anisoTorus (K := K) (by norm_num) b c)) 3 F

theorem omegaMinusTwoTenFieldGlobalInput_of_frameGen (h : OmegaMinusTwoTenFieldFrameGenInput) :
    OmegaMinusTwoTenFieldGlobalInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  obtain ⟨F, _, _, _, hF4, hD⟩ :=
    h G L hset K b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF4,
    nonempty_anisoNeighbourJoin_mulEquiv_of_ctData (f := 2) (by norm_num) (by norm_num)
      (by rw [hF4]; norm_num) (by omega) (anisoCTData_of_q2FrameDataGen_of_three_le le_rfl hF4 hD)⟩

@[expose] def OmegaPlusTwoTenFieldFrameGenInput : Prop :=
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
            Q2FrameDataGen L (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr)) 3 F

theorem omegaPlusTwoTenFieldGlobalInput_of_frameGen (h : OmegaPlusTwoTenFieldFrameGenInput) :
    OmegaPlusTwoTenFieldGlobalInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  obtain ⟨F, _, _, _, hF4, hD⟩ :=
    h G L hset K b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF4,
    nonempty_anisoNeighbourJoin_mulEquiv_of_ctData (f := 2) (by norm_num) (by norm_num)
      (by rw [hF4]; norm_num) (by omega) (anisoCTData_of_q2FrameDataGen_of_three_le le_rfl hF4 hD)⟩

end CFSG.SeitzReduction.OmegaPilot
