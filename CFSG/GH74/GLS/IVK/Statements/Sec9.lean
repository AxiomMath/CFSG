module

public import CFSG.GH74.GLS.IVK.Statements.Sec4

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def IVK_9_5 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → IsKGroupNative J →
    ∀ z : J, orderOf z = 2 → ∀ (q : ℕ), Odd q → 5 < q →
      HasSL2Model ↥(Ez z) (fun r => r = q) →
      (∀ S : Sylow 2 ↥(centralizer ((Ez z : Subgroup J) : Set J)), IsCyclic ↥S) →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 J ε q

end CFSG.GH74.GLS.IVK
