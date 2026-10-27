module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.Walter.J1Props.Factor

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint

theorem ivk93_j1 :
    Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  refine ivk93_empty_of_cfg fun J _ _ hJ x _ _ _ _ hc => ?_
  obtain ⟨e0⟩ := hJ
  let e : J ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
  exact (Ivk93Cfg.of_equiv e hc).false_of_abelian_sylow CFSG.Walter.J1Props.hasAbelianSylowTwo

end CFSG.GH74.GLS.IVK.Proofs2
