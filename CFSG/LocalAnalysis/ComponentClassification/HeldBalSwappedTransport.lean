module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondence

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

theorem conjugate_map_subtype {X : Type*} [Group X] (D : Subgroup X) (M : Subgroup D) (a : D) :
    conjugate (M.map D.subtype) (a : X) = (conjugate M a).map D.subtype := by
  have hcomp : (MulAut.conj (a : X)⁻¹).toMonoidHom.comp D.subtype =
      D.subtype.comp (MulAut.conj (a⁻¹ : D)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

theorem gsFixedLayer_map_subtype {X : Type} [Group X] [Finite X] (D : Subgroup X) {a : X}
    (ha : a ∈ D) (A B : Subgroup D) {K : Subgroup X} (hKD : K ≤ D)
    (h : gsFixedLayer (A ⊔ B) (⟨a, ha⟩ : D) = K.subgroupOf D) :
    gsFixedLayer (A.map D.subtype ⊔ B.map D.subtype) a = K := by
  have hK'D : (A ⊔ B).map D.subtype ≤ D := Subgroup.map_subtype_le _
  have hsub : ((A ⊔ B).map D.subtype).subgroupOf D = A ⊔ B := by
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  have hcorr :=
    CFSG.ComponentClassification.UnbalancingLocal.Correspondence.gsFixedLayer_subgroupOf
      (G := X) hK'D ha
  have hcorr' : (gsFixedLayer ((A ⊔ B).map D.subtype) a).subgroupOf D = K.subgroupOf D := by
    rw [hcorr, hsub, h]
  rw [← Subgroup.map_sup A B D.subtype]
  have hgl : gsFixedLayer ((A ⊔ B).map D.subtype) a ≤ D :=
    (gsFixedLayer_le_inf _ a).trans (inf_le_left.trans hK'D)
  have hmap := congrArg (Subgroup.map D.subtype) hcorr'
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hgl, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left hKD] at hmap
  exact hmap

theorem pPrimeCore_map_subtype_eq_bot {X : Type*} [Group X] (D : Subgroup X) (M : Subgroup D)
    (h : pPrimeCore 2 ↥M = ⊥) : pPrimeCore 2 ↥(M.map D.subtype) = ⊥ := by
  have hmap := pPrimeCore_map_iso 2
    (Subgroup.equivMapOfInjective M D.subtype D.subtype_injective)
  rw [← hmap, h, Subgroup.map_bot]

end CFSG.ComponentClassification.GrSLit
