module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.ShapeK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem pCore_K_eq_of_tableX {z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀) :
    CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z)) = CFSG.Open.pCoreOf 2 (Gxy p z ⊓ derivedOf (Gx p)) := by
  have h1 := hT.pCore_derived.1
  have h2 := hT.pCore_derived.2
  calc CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z))
      = (CFSG.Open.pCoreOf 2 (derivedOf (Gx x))).map (Gx p).subtype :=
        pCoreOf_derivedOf_Gxy_eq_map hx
    _ = (CFSG.Open.pCoreOf 2 (commutator ↥(Gx p) ⊓ Gx x)).map (Gx p).subtype := by
        rw [h1, h2]
    _ = CFSG.Open.pCoreOf 2 ((commutator ↥(Gx p) ⊓ Gx x).map (Gx p).subtype) :=
        (pCoreOf_map_of_injective (Subgroup.subtype_injective (Gx p))
          (commutator ↥(Gx p) ⊓ Gx x)).symm
    _ = CFSG.Open.pCoreOf 2 (Gxy p z ⊓ derivedOf (Gx p)) := by
        rw [Gxy_inf_derivedOf_Gx_eq_map hx]

theorem pCore_derived_of_tableX {z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀)
    (hR : CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z) :
    CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z)) = derivedOf (Gxy p z) ⊓ Qz z := by
  calc CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z))
      = (CFSG.Open.pCoreOf 2 (derivedOf (Gx x))).map (Gx p).subtype :=
        pCoreOf_derivedOf_Gxy_eq_map hx
    _ = (derivedOf (Gx x) ⊓ CFSG.Open.pCoreOf 2 (Gx x)).map (Gx p).subtype := by
        rw [hT.pCore_derived.1]
    _ = (derivedOf (Gx x)).map (Gx p).subtype ⊓
          (CFSG.Open.pCoreOf 2 (Gx x)).map (Gx p).subtype :=
        Subgroup.map_inf_eq (derivedOf (Gx x)) (CFSG.Open.pCoreOf 2 (Gx x))
          (Gx p).subtype (Subgroup.subtype_injective (Gx p))
    _ = derivedOf (Gxy p z) ⊓ CFSG.Open.pCoreOf 2 (Gxy p z) := by
        rw [← derivedOf_Gxy_eq_map hx, ← pCoreOf_Gxy_eq_map hx]
    _ = derivedOf (Gxy p z) ⊓ (Gxy p z ⊓ Qz z) := by rw [hR]
    _ = derivedOf (Gxy p z) ⊓ Qz z := by
        rw [← inf_assoc, inf_of_le_left (derivedOf_le (Gxy p z))]

theorem center_of_tableX {z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀) :
    centerOf (derivedOf (Gxy p z)) = centerOf (CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z))) ∧
      Nonempty (↥(centerOf (derivedOf (Gxy p z))) ≃* Z 2 × Z 4) := by
  constructor
  · rw [centerOf_derivedOf_Gxy_eq_map hx, centerOf_pCoreOf_derivedOf_Gxy_eq_map hx]
    exact congrArg (Subgroup.map (Gx p).subtype) hT.center_derived.1
  · obtain ⟨φ⟩ := hT.center_derived.2
    exact ⟨(MulEquiv.subgroupCongr (centerOf_derivedOf_Gxy_eq_map hx)).trans
      ((Subgroup.equivMapOfInjective (centerOf (derivedOf (Gx x))) (Gx p).subtype
        (Subgroup.subtype_injective (Gx p))).symm.trans φ)⟩

theorem shape_O2_of_tableX {z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀) :
    IsShapeZ2Z4StarExtra ↥(CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z))) := by
  have heq : (CFSG.Open.pCoreOf 2 (commutator ↥(Gx p) ⊓ Gx x)).map (Gx p).subtype =
      CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z)) := by
    rw [← pCoreOf_map_of_injective (Subgroup.subtype_injective (Gx p))
      (commutator ↥(Gx p) ⊓ Gx x)]
    rw [← Gxy_inf_derivedOf_Gx_eq_map hx]
    rw [← pCore_K_eq_of_tableX hx hT]
  have hmap : IsShapeZ2Z4StarExtra
      ↥((CFSG.Open.pCoreOf 2 (commutator ↥(Gx p) ⊓ Gx x)).map (Gx p).subtype) :=
    IsShapeZ2Z4StarExtra.map (f := (Gx p).subtype) (Subgroup.subtype_injective (Gx p))
      (isShapeZ2Z4StarExtra_pCoreOf hT.shape_K)
  rwa [heq] at hmap

end CFSG.EvenSporadicStandard.HNRecog.Section3
