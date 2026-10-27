module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Mathieu
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4J3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45 CFSG.GH74.GLS.IVK

theorem ivk93_j3 :
    Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .J3) := by
  refine ivk93_empty_of_small_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥j3P := e.trans j3PermEquiv
  have hord : orderOf ((e' y : ↥j3P) : Equiv.Perm (Fin 6156)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨-, hcard⟩ := j3_inner_centralizer_data _ (e' y).2 hord
  rw [GHInv.card_centralizer_eq_centralizerIn j3P e' y, hcard]
  norm_num

end CFSG.GH74.GLS.IVK.Proofs2
