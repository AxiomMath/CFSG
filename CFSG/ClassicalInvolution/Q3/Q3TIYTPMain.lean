module

public import CFSG.ClassicalInvolution.Q3.Q3TIYTPCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

theorem localOddThreeFree3_of_involutionOddCore_eq_bot {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) {x : G} (hx : involutionOddCore x = ⊥) : LocalOddThreeFree3 Ω x := by
  have h1 : classicalInvolutionOddCore ↥(locLayer Ω x) = ⊥ := by
    have h2 : oddCoreIn (locLayer Ω x) ≤ involutionOddCore x := oddCoreIn_centralizingLayer_le hΩ x
    rw [hx] at h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ (locLayer Ω x).subtype_injective).mp
      (le_bot_iff.mp h2)
  unfold LocalOddThreeFree3
  rw [h1, Subgroup.card_bot]
  decide

theorem twin_P1_R3_of_edge (h : TwinSetup3 K T z) (e : TwinElt K T z) {J : Subgroup G} {t : G}
    (hJ : J ∈ centralizingMembers (conjClass3 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (clsJ : IsClassicalMember3 J t) (htz : t ≠ z)
    (hα : alphaCore (Subgroup.closure ({z, t} : Set G)) = ⊥) :
    LocalOddCentral (conjClass3 K) {e.u} ∧ LocalOddThreeFree3 (conjClass3 K) e.u := by
  have hP := h.oddCore_eq_bot e hJ hJK hJT clsJ htz hα
  exact ⟨localOddCentral3_of_involutionOddCore_eq_bot h.hΩ.conjInvariant hP,
    localOddThreeFree3_of_involutionOddCore_eq_bot h.hΩ.conjInvariant hP⟩

end CFSG.ClassicalInvolution.Q3.Q3TIY
