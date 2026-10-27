module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreFreeInvolutionLayer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueRelativeB (CatalogueSchreier)

theorem catalogueSchreier_iff_schreierFor :
    CatalogueSchreier ↔ SchreierFor CFSG.Assembly.InCatalog :=
  Iff.rfl

theorem outer_isSolvable_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hX : Group.IsSolvable (Outer X)) : Group.IsSolvable (Outer Y) :=
  Group.isSolvable_of_isSolvable_injective (f := (equivalence e).symm.toMonoidHom)
    (equivalence e).symm.injective

theorem outer_solvable_of_kProper_image {C : CFSG.Assembly.GroupProp} (hS : SchreierFor C)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Assembly.KProper C G) {K : Subgroup G}
    (hKtop : K ≠ ⊤) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (f : K →* X) (hf : Function.Surjective f) :
    Group.IsSolvable (Outer X) := by
  set Z : Subgroup G := f.ker.map K.subtype with hZ
  have hZeq : Z.subgroupOf K = f.ker :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective f.ker
  have : (Z.subgroupOf K).Normal := by
    rw [hZeq]
    infer_instance
  let e : K ⧸ Z.subgroupOf K ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZeq).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have : IsSimpleGroup (K ⧸ Z.subgroupOf K) := MulEquiv.isSimpleGroup e
  have hnab' : ∃ a b : K ⧸ Z.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hcat := hK K Z hKtop (Subgroup.map_subtype_le _) ‹IsSimpleGroup _› hnab'
  exact outer_isSolvable_of_mulEquiv e (hS (K ⧸ Z.subgroupOf K) hnab' hcat)

theorem kProper_component_outer_solvable {C : CFSG.Assembly.GroupProp} (hS : SchreierFor C)
    {H : Type} [Group H] [Finite H] (hK : CFSG.Assembly.KProper C H) {K : Subgroup H}
    (hKc : CFSG.IsComponent K) (hKtop : K ≠ ⊤) :
    Group.IsSolvable (Outer (K ⧸ center K)) := by
  obtain ⟨-, hsimple, hnab⟩ := hKc.1
  exact outer_solvable_of_kProper_image hS hK hKtop hnab (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _)

theorem kProper_odd_core_free_involution_component_enters_layer {C : CFSG.Assembly.GroupProp}
    (hS : SchreierFor C) {H : Type} [Group H] [Finite H] (hK : CFSG.Assembly.KProper C H)
    (hcore : CFSG.pPrimeCore 2 H = ⊥) {t : H} (ht : orderOf t = 2)
    (L : Subgroup (centralizer ({t} : Set H))) (hL : CFSG.IsComponent L) :
    L.map (centralizer ({t} : Set H)).subtype ≤ CFSG.layer H := by
  by_cases hE : CFSG.layer H = ⊤
  · rw [hE]
    exact le_top
  · refine odd_core_free_Schreier_involution_component_enters_layer hcore ht (fun K hKc => ?_)
      L hL
    have hKE : K ≤ CFSG.layer H := le_sSup hKc
    exact kProper_component_outer_solvable hS hK hKc fun h => hE (eq_top_iff.2 (h ▸ hKE))

theorem kProper_odd_core_free_involution_isComponentOf_le_layer {C : CFSG.Assembly.GroupProp}
    (hS : SchreierFor C) {H : Type} [Group H] [Finite H] (hK : CFSG.Assembly.KProper C H)
    (hcore : CFSG.pPrimeCore 2 H = ⊥) {t : H} (ht : orderOf t = 2) {J : Subgroup H}
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set H))) :
    J ≤ CFSG.layer H := by
  have h := kProper_odd_core_free_involution_component_enters_layer hS hK hcore ht
    (J.subgroupOf (centralizer ({t} : Set H)))
    ((isComponentOf_iff_isComponent_subgroupOf hJ.1).1 hJ)
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJ.1] at h

end CFSG.LocalAnalysis.ComponentInitial
