module

public import CFSG.LieType.Chevalley.OddPinnedComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.LocalAnalysis.ComponentInitial (isQuasisimple_congr p_component_isomorphism_transport)

theorem ringChar_fixSubfield_ne_two {K : Type} [Field K] (hK : ringChar K ≠ 2) (σ : K ≃+* K) :
    ringChar (fixSubfield σ) ≠ 2 := by
  intro h
  have h0 : ((2 : ℕ) : fixSubfield σ) = 0 := by
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  apply Ring.two_ne_zero hK
  have := congrArg (fixSubfield σ).subtype h0
  rw [map_natCast, map_zero] at this
  exact_mod_cast this

theorem odd_Chevalley_coordinate_field_fixed_p_components
    (τ : Tag) (K : Type) [Field K]
    [Finite K] (hK : ringChar K ≠ 2) (σ : K ≃+* K) (p : ℕ) (hp : p.Prime)
    (L : Subgroup (entrywiseFixedGroup τ σ)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, -, -, hcomm⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have : Group.IsSolvable (entrywiseFixedGroup τ σ ⧸
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)) :=
    Group.isSolvable_of_comm hcomm
  let e : (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ) ≃*
      adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJΓ).trans
      (Subgroup.equivMapOfInjective (adjointGroup τ (fixSubfield σ)) _ hinj).symm
  have : Finite (ModGL τ (fixSubfield σ)) := finite_modGL
  refine pComponent_quasisimple_of_normal_solvable_quotient p
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)) (fun J hJ => ?_) L hL
  have hJ' := ((p_component_isomorphism_transport p hp e).1 J).1 hJ
  have hq := ((odd_pinned_Chevalley_p_components τ (fixSubfield σ)
    (ringChar_fixSubfield_ne_two hK σ)).2.2 p _ hJ').1
  exact (isQuasisimple_congr (J.equivMapOfInjective e.toMonoidHom e.injective)).2 hq

end CFSG.LieType.Chevalley
