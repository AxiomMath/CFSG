module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFusionCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std

theorem not_psu42_of_outerFusion {X : Type} [Group X] [Finite X]
    {z : X} (hz2 : z * z = 1)
    (hC : Nonempty (centralizer ({z} : Set X) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)))
    (hF : OuterFusion X z) (hL : LieModel (egaLayer X) .PSU 4 2 1)
    (hz : z ∉ egaLayer X ⊔ centralizer (egaLayer X : Set X)) : False :=
  false_of_outerFusion_of_card_mulAut_lt hz2 hC hF (E := egaLayer X)
    (not_commutative_of_lieModel_psu42 hL) hz
    (by rw [(card_mulAut_of_lieModel_psu42 hL).1]; norm_num)

end CFSG.EvenSporadicStandard.M22Std
