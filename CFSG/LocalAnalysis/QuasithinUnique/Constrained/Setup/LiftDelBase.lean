module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingComponents

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

theorem delBaseProp : DelBaseProp := by
  intro G _ _ R M V n F _ r Lc ctx hcore
  have hS := ctx.setting
  have hred := hS.reduced
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hred.2.1)
  have hV2 : IsPGroup 2 ↥V := fun g => ⟨1, Subtype.ext (by simpa using hred.2.2.1.2 g g.2)⟩
  have hJS : thompsonJ (baum R) = thompsonJ R :=
    B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum R) inf_le_left
  have hLSn : (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R).Normal := hcore.normal
  have hQ0n : (pCoreOf 2 (⊤ : Subgroup G)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hQnorm : (⊤ : Subgroup G) ≤
      Subgroup.normalizer (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
      (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)
    rwa [Subgroup.normalizer_eq_top_iff.mpr hLSn] at h1
  have hQ0 : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 le_top
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2 hQnorm)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hQle : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤
      baum R ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hcore.CS_eq]
    exact le_inf hQ0 (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hQge : baum R ⊓ Subgroup.centralizer (V : Set G) ≤
      pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) := by
    rw [hcore.CS_eq]
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup G)).to_le inf_le_left)
    exact (inferInstance :
      (pCoreOf 2 (⊤ : Subgroup G) ⊓ (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)).Normal).subgroupOf _
  refine ⟨⟨C1GN.characteristic_baum R, hJS, by rw [hJS], C1GN.baum_baum R, ?_,
    hQle.trans inf_le_left, ?_⟩, le_antisymm hQle hQge⟩
  · exact EscapingComponents.charTwo_of_isSubnormal ctx.charTwo le_top
      (Subgroup.Normal.isSubnormal (hLSn.subgroupOf _))
  · exact CFSG.LieType.BorelTits.le_pCoreOf 2 (hcore.V_le_S.trans le_sup_right)
      (hVn.subgroupOf _) hV2

end CFSG.QuasithinUnique.Setup.Lift
