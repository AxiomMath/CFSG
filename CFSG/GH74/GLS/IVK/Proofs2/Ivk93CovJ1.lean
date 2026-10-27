module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovAbel
public import CFSG.Walter.J1Props.Factor

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint

theorem ivk93cov_j1 : Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ _ _ hc => ?_
  obtain ⟨e0⟩ := hJ
  let e : J ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
  exact (hc.of_equiv e).false_of_abelian_sylow CFSG.Walter.J1Props.hasAbelianSylowTwo

end CFSG.GH74.GLS.IVK.Proofs2
