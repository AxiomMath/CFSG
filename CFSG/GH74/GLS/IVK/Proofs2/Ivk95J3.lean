module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Mathieu
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4J3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45 CFSG.GH74.GLS.IVK

theorem ivk95_j3 :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .J3) := by
  refine ivk95_empty_of_perfect_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥j3P := e.trans j3PermEquiv
  have hord : orderOf ((e' y : ↥j3P) : Equiv.Perm (Fin 6156)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨hperf, hcard⟩ := j3_inner_centralizer_data _ (e' y).2 hord
  refine ⟨GHInv.isPerfect_centralizer_of_equiv j3P e' y hperf, Or.inl ?_⟩
  rw [GHInv.card_centralizer_eq_centralizerIn j3P e' y]
  exact hcard

end CFSG.GH74.GLS.IVK.Proofs2
