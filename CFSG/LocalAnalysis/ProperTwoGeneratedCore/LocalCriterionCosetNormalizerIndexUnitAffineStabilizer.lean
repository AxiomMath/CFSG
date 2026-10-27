module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitAffine
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalGraphFusion
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

@[expose, instance_reducible] def unitAffineAction (U : Subgroup G) :
    MulAction (unitAffineGroup U) U :=
  MulAction.compHom U (unitAffinePerm U)

@[expose, instance_reducible] def unitCoordinateAction (U : Subgroup G) (u : G) :
    MulAction (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) U :=
  MulAction.compHom U (unitCoordinatePerm U u)

theorem unitAffineHom_action (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) (x : U) :
    unitAffinePerm U (unitAffineHom U u hu hcentral n) x = unitCoordinatePerm U u n x := by
  exact congrArg (fun f => f n x) (unitAffinePerm_comp_unitAffineHom U u hu hcentral)

theorem unitTranslateEquiv_unitCoordinatePerm (U : Subgroup G) (u : G)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) (x : U) :
    unitTranslateEquiv U u (unitCoordinatePerm U u n x) =
      cosetNormalizerPerm ((fun x : G => u * x) '' (U : Set G)) n
        (unitTranslateEquiv U u x) := by
  apply Subtype.ext
  rw [unitTranslateEquiv_apply, unitCoordinatePerm_apply, cosetNormalizerPerm_apply,
    unitTranslateEquiv_apply, mul_inv_cancel_left]

theorem unitAffineAction_stabilizer_one (U : Subgroup G) :
    letI := unitAffineAction U
    MulAction.stabilizer (unitAffineGroup U) (1 : U) =
      (SemidirectProduct.inr : MulAut U →* unitAffineGroup U).range := by
  let := unitAffineAction U
  ext a
  change unitAffinePerm U a 1 = 1 ↔
    a ∈ (SemidirectProduct.inr : MulAut U →* unitAffineGroup U).range
  rw [unitAffinePerm_apply, map_one, mul_one]
  constructor
  · intro ha
    exact ⟨a.right, SemidirectProduct.ext ha.symm rfl⟩
  · rintro ⟨b, rfl⟩
    rfl

theorem unitAffineHom_stabilizer_one_comap (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    letI := unitAffineAction U
    (MulAction.stabilizer (unitAffineGroup U) (1 : U)).comap
        (unitAffineHom U u hu hcentral) =
      (Subgroup.centralizer ({u} : Set G)).subgroupOf
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) := by
  let := unitAffineAction U
  ext n
  change unitAffinePerm U (unitAffineHom U u hu hcentral n) 1 = 1 ↔
    (n : G) ∈ Subgroup.centralizer ({u} : Set G)
  rw [unitAffineHom_action, unitCoordinatePerm_one_eq_one_iff]

theorem unitAffineHom_centralizer_image (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    letI := unitAffineAction U
    ((Subgroup.centralizer ({u} : Set G)).subgroupOf
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)))).map
        (unitAffineHom U u hu hcentral) =
      (unitAffineHom U u hu hcentral).range ⊓
        MulAction.stabilizer (unitAffineGroup U) (1 : U) := by
  let := unitAffineAction U
  rw [← unitAffineHom_stabilizer_one_comap U u hu hcentral]
  ext a
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, hn⟩
  · rintro ⟨⟨n, rfl⟩, hn⟩
    exact ⟨n, hn, rfl⟩

theorem unitAffineHom_ker_le_u_centralizer (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (unitAffineHom U u hu hcentral).ker ≤
      (Subgroup.centralizer ({u} : Set G)).subgroupOf
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) := by
  rw [unitAffineHom_ker]
  exact fun _ hx => hx.1

theorem unitAffineHom_rightHom_comp (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (SemidirectProduct.rightHom : unitAffineGroup U →* MulAut U).comp
        (unitAffineHom U u hu hcentral) = unitLinearConjugation U u hu hcentral := rfl

theorem unitAffineHom_translation_range_comap (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (SemidirectProduct.inl : U →* unitAffineGroup U).range.comap
        (unitAffineHom U u hu hcentral) = (unitLinearConjugation U u hu hcentral).ker := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  rfl

theorem unitCoordinateAction_isPretransitive (U : Subgroup G) (u : G)
    (htrans : ∀ s : G, s ∈ (fun x : G => u * x) '' (U : Set G) →
      ∀ t : G, t ∈ (fun x : G => u * x) '' (U : Set G) →
      ∃ n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)),
        rightConjugateElem s (n : G) = t) :
    letI := unitCoordinateAction U u
    MulAction.IsPretransitive
      (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) U := by
  let := unitCoordinateAction U u
  constructor
  intro x y
  obtain ⟨n, hn⟩ := htrans (u * (x : G)) ⟨x, x.property, rfl⟩
    (u * (y : G)) ⟨y, y.property, rfl⟩
  refine ⟨n⁻¹, ?_⟩
  apply Subtype.ext
  change u⁻¹ * ((n : G)⁻¹ * (u * (x : G)) * ((n : G)⁻¹)⁻¹) = (y : G)
  rw [inv_inv]
  change (n : G)⁻¹ * (u * (x : G)) * (n : G) = u * (y : G) at hn
  rw [hn, inv_mul_cancel_left]

theorem unitAffineHom_range_isPretransitive (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (htrans : ∀ s : G, s ∈ (fun x : G => u * x) '' (U : Set G) →
      ∀ t : G, t ∈ (fun x : G => u * x) '' (U : Set G) →
      ∃ n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)),
        rightConjugateElem s (n : G) = t) :
    letI := unitAffineAction U
    MulAction.IsPretransitive (unitAffineHom U u hu hcentral).range U := by
  let := unitAffineAction U
  let := unitCoordinateAction U u
  have h := unitCoordinateAction_isPretransitive U u htrans
  constructor
  intro x y
  obtain ⟨n, hn⟩ := h.exists_smul_eq x y
  refine ⟨⟨unitAffineHom U u hu hcentral n, n, rfl⟩, ?_⟩
  change unitAffinePerm U (unitAffineHom U u hu hcentral n) x = y
  rw [unitAffineHom_action]
  exact hn

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
