module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Quasi

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint

namespace Ivk93Cfg2

variable {J : Type} [Group J] [Finite J] {x : J} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup J}

theorem false_of_quasisimple_centralizer (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂)
    (hq : CFSG.IsQuasisimple ↥(centralizer ({x} : Set J))) : False :=
  h.ne ((ivk93x_eq_centralizer_of_pComp h.comp₁ h.not_solvable₁ hq).trans
    (ivk93x_eq_centralizer_of_pComp h.comp₂ h.symm.not_solvable₁ hq).symm)

end Ivk93Cfg2

end CFSG.GH74.GLS.IVK.Proofs2
