module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Local.ChiefFactorCentralizationCentralSeries
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem IsChiefFactor.commutator_num_le_den [Group.IsSolvable G] {U V : Subgroup G}
    (h : IsChiefFactor U V) : ⁅U, U⁆ ≤ V := by
  have hU := h.normal_num
  have hV := h.normal_den
  have hle : ⁅U, U⁆ ⊔ V ≤ U := sup_le (Subgroup.commutator_le_left U U) h.le
  rcases h.eq_or_eq (Z := ⁅U, U⁆ ⊔ V) inferInstance le_sup_right hle with hz | hz
  · exact le_sup_left.trans hz.le
  · exfalso
    set φ := QuotientGroup.mk' V with hφ
    have hVb : V.map φ = ⊥ := (Subgroup.map_eq_bot_iff _).2 (by rw [hφ, QuotientGroup.ker_mk'])
    have h1 : ⁅U.map φ, U.map φ⁆ = U.map φ := by
      rw [← Subgroup.map_commutator]
      conv_rhs => rw [← hz]
      rw [Subgroup.map_sup, hVb, sup_bot_eq]
    have hne : U.map φ ≠ ⊥ := by
      intro hb
      have hUV : U ≤ V := by
        have := (Subgroup.map_eq_bot_iff _).1 hb
        rwa [hφ, QuotientGroup.ker_mk'] at this
      exact absurd hUV h.lt.not_ge
    exact absurd h1 (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne

variable [Finite G]

theorem normal_map_fittingRaw_subtype (N : Subgroup G) [N.Normal] :
    ((fittingRaw ↥N).map N.subtype).Normal :=
  ConjAct.normal_of_characteristic_of_normal

theorem map_fittingRaw_subtype_le (N : Subgroup G) :
    (fittingRaw ↥N).map N.subtype ≤ N :=
  Subgroup.map_subtype_le _

theorem le_map_fittingRaw_subtype_iff {N T : Subgroup G} (hTN : T ≤ N) :
    T ≤ (fittingRaw ↥N).map N.subtype ↔ T.subgroupOf N ≤ fittingRaw ↥N := by
  constructor
  · intro h
    have := Subgroup.comap_mono (f := N.subtype) h
    rwa [Subgroup.comap_map_eq_self_of_injective N.subtype_injective] at this
  · intro h
    have := Subgroup.map_mono (f := N.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hTN] at this

theorem le_map_fittingRaw_subtype {N T : Subgroup G} (hTN : T ≤ N)
    (hT : (T.subgroupOf N).Normal) (hnil : Group.IsNilpotent ↥T) :
    T ≤ (fittingRaw ↥N).map N.subtype := by
  have := hnil
  have hnil' : Group.IsNilpotent ↥(T.subgroupOf N) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTN).symm
  exact (le_map_fittingRaw_subtype_iff hTN).2 (le_fittingRaw_of_normal_of_isNilpotent hT hnil')

theorem le_map_fittingRaw_subtype_of_forall_isChiefFactor [Group.IsSolvable G]
    {N K : Subgroup G} [N.Normal] [K.Normal] (hKN : K ≤ N)
    (h : ∀ U V : Subgroup G, IsChiefFactor U V →
      U ≤ (fittingRaw ↥N).map N.subtype → ⁅K, U⁆ ≤ V) :
    K ≤ (fittingRaw ↥N).map N.subtype := by
  set F := (fittingRaw ↥N).map N.subtype
  by_contra hK
  obtain ⟨T, ⟨hTnorm, hTK, hTF⟩, hmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun T : Subgroup G => T.Normal ∧ T ≤ K ∧ ¬ T ≤ F)
      ⟨K, inferInstance, le_rfl, hK⟩
  have := hTnorm
  have hprop : ∀ U : Subgroup G, U.Normal → U < T → U ≤ F := fun U hU hUT => by
    by_contra hUF
    exact absurd (hmin ⟨hU, hUT.le.trans hTK, hUF⟩ hUT.le) hUT.not_ge
  have hnil : Group.IsNilpotent ↥T := by
    refine isNilpotent_of_forall_isChiefFactor T fun U V hUV hUT => ?_
    rcases eq_or_lt_of_le hUT with rfl | hlt
    · exact hUV.commutator_num_le_den
    · exact (Subgroup.commutator_mono hTK le_rfl).trans (h U V hUV (hprop U hUV.normal_num hlt))
  exact hTF (le_map_fittingRaw_subtype (hTK.trans hKN) inferInstance hnil)

theorem subgroupOf_le_fittingRaw_of_forall_isChiefFactor [Group.IsSolvable G]
    {N K : Subgroup G} [N.Normal] [K.Normal] (hKN : K ≤ N)
    (h : ∀ U V : Subgroup G, IsChiefFactor U V →
      U ≤ (fittingRaw ↥N).map N.subtype → ⁅K, U⁆ ≤ V) :
    K.subgroupOf N ≤ fittingRaw ↥N :=
  (le_map_fittingRaw_subtype_iff hKN).1 (le_map_fittingRaw_subtype_of_forall_isChiefFactor hKN h)

end

end CFSG.FeitThompson
