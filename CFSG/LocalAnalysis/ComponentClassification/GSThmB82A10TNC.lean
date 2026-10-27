module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TJStar

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

namespace Ctx

variable (c : Ctx X)

structure JstarData where
  Js : Subgroup X
  le_centralizer : Js ≤ centralizer ({c.Z.z} : Set X)
  isPComponent : IsPComponent 2 (Js.subgroupOf (centralizer ({c.Z.z} : Set X)))
  Jstar0_le : c.Jstar0 ≤ Js
  x_mem_normalizer : c.s.h.x ∈ normalizer (Js : Set X)
  m : ℕ
  seven_le : 7 ≤ m
  equiv : Nonempty (↥Js ⧸ pPrimeCore 2 ↥Js ≃* alternatingGroup (Fin m))

end Ctx

end CFSG.ComponentClassification.GSThmB.A10T
