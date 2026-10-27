module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

structure WreathCase {X : Type*} [Group X] (t : X) (Sg V K : Subgroup X) : Prop where
  shape : SwapShape t Sg V
  isComponent : CFSG.IsComponent K
  map_ne : K.map (MulAut.conj t).toMonoidHom ≠ K
  comm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥
  eq_or_eq : ∀ L : Subgroup X, CFSG.IsComponent L → L = K ∨ L = K.map (MulAut.conj t).toMonoidHom
  layer_eq : CFSG.layer X = K ⊔ K.map (MulAut.conj t).toMonoidHom
  iso : Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8))
  diag : ((⁅Sg, Sg⁆ : Subgroup X) : Set X) = {g | ∃ k ∈ K, k * (t * k * t⁻¹) = g}

end CFSG.OddStandard.AltStdSec.SwapPartner
