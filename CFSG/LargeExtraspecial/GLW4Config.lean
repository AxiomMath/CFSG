module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.GLRConfig
public import CFSG.LargeExtraspecial.GLRFusCard
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.GLR

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem nonempty_config_of_data {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {g : G}
    (hD : Data S X A B g)
    (hX : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin S.width) (ZMod 2))) :
    Nonempty (Config S) :=
  ⟨{ Xbar := X
     At := A
     Bt := B
     four_le_width := hD.four_le
     Xbar_le := hD.le_Mbar
     relIndex_Xbar := hD.relIndex_eq
     nonempty_equiv := hX
     finrank_At := hD.pair.finrank_A
     finrank_Bt := hD.pair.finrank_B
     q_At := hD.pair.q_A
     q_Bt := hD.pair.q_B
     inf_eq := hD.pair.inf_eq
     sup_eq := hD.pair.sup_eq
     apply_At := hD.pair.apply_A
     apply_Bt := hD.pair.apply_B
     map_At := hD.map_A
     transitive := fun v hv hv0 w hw hw0 => hD.pair.exists_apply_eq_of_ne_zero hv hw hv0 hw0
     invariant := hD.pair.invariant (by have := hD.four_le; omega)
     conj_At := fun v hv hv0 => hD.conj_A hv hv0
     fusion := hD.fusion
     centralizer_A := hD.centralizer_eq
     normalizer_inf_M := hD.normalizer_inf_M
     card_normalizer := hD.card_normalizer }⟩

end CFSG.LargeExtraspecial.GLW4
