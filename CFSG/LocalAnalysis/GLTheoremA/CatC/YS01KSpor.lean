module

public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteB
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteM

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def KDL227SporK : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) → CFSG.Open.IsKGroup S →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → ¬ catalogIs (PSimple 3 J) (onLie (isL2 27))

section Cert

set_option linter.unusedSectionVars false


theorem isKGroup_carrier_of_iso
    {S : Type} [Group S] (hK : CFSG.Open.IsKGroup S)
    (s : TauCeti.SporadicName) (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier s) :=
  hK.of_surjective (e.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s).some.symm).toMonoidHom
    (e.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s).some.symm).surjective

theorem kdl227SporK_of_rows
    (hCo1 : KDL227Rows.KDL227SporRow .Co1)
    (hFi : KDL227Rows.KDL227SporRow .Fi24Prime) : KDL227SporK := by
  have hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable :=
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
  have hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hrow : ∀ s : TauCeti.SporadicName, s ≠ .B → s ≠ .M → KDL227Rows.KDL227SporRow s := by
    intro s hB hM
    cases s
    case Co1 => exact hCo1
    case Fi24Prime => exact hFi
    case Fi22 => exact KDL227Rows.kdl227Row_Fi22 hOut hbr
    case Fi23 => exact KDL227Rows.kdl227Row_Fi23 hOut hbr
    case Th => exact KDL227Rows.kdl227Row_Th hOut hbr
    case Suz => exact KDL227Rows.kdl227Row_Suz hOut hbr
    case Ru => exact KDL227Rows.kdl227Row_Ru hOut hbr
    case B => exact absurd rfl hB
    case M => exact absurd rfl hM
    all_goals exact KDL227Rows.kdl227Row_of_not_dvd (by
      rw [hOrd]
      norm_num [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, CFSG.Open.orderJ3,
        CFSG.Open.orderON, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderJ4])
  intro S _ _ s he hK
  by_cases hB : s = .B
  · subst hB
    obtain ⟨e⟩ := he
    exact CFSG.HardMathSupport.Dickson.BMRows.kdl227Row_B_of_kGroup
      (isKGroup_carrier_of_iso hK .B e) S ⟨e⟩
  by_cases hM : s = .M
  · subst hM
    obtain ⟨e⟩ := he
    exact CFSG.HardMathSupport.Dickson.BMRows.kdl227Row_M_of_kGroup
      (isKGroup_carrier_of_iso hK .M e) S ⟨e⟩
  exact hrow s hB hM S he

end Cert

end CFSG.LocalAnalysis.GLTheoremA
