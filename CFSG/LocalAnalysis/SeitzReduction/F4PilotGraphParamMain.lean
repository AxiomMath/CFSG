module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSpin

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)

local instance f4PilotGraphParamMainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance f4PilotGraphParamMainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Inputs

@[expose] def IsNeighbourFrame {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] (e e₁ : L ≃* adjointGroup .F4 K) : AmalgamNeighbour → Prop
  | .X => e₁ = e
  | .Y => ∃ _ : CharP K CFSG.LieType.Ree.ReeTag.F4.prime, e₁ = e.trans (graphAutF4 K).symm
  | .X' => False

end Inputs

section Main

theorem range_comp_spinEquivD4_symm {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    [CharP K 2] (ΦY : spinGroup (quadPlus 4 K) →* G) :
    (ΦY.comp (spinEquivD4 K).symm.toMonoidHom).range = ΦY.range := by
  have hs : ((spinEquivD4 K).symm.toMonoidHom).range = ⊤ :=
    MonoidHom.range_eq_top.2 (spinEquivD4 K).symm.surjective
  rw [MonoidHom.range_comp, hs, ← MonoidHom.range_eq_map]

end Main

end CFSG.SeitzReduction.F4Pilot
