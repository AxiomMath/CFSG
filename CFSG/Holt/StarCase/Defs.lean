module

public import CFSG.Holt.Induced
public import CFSG.Assembly.Defs

public section

namespace CFSG.Holt

open MulAction CFSG.Open
open scoped Pointwise

section Vocabulary

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

@[expose] def evenSubgroup [Fintype Ω] [DecidableEq Ω] : Subgroup G :=
  (alternatingGroup Ω).comap (MulAction.toPermHom G Ω)

@[expose] def ContainsAlt {Ψ : Type*} (K : Subgroup (Equiv.Perm Ψ)) : Prop :=
  ∀ (_ : Fintype Ψ) (_ : DecidableEq Ψ), alternatingGroup Ψ ≤ K

variable {G Ω}

end Vocabulary

section Star

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]

structure StarData where
  t : G
  orderOf_t : orderOf t = 2
  containsAlt_t : ContainsAlt (centralizerImage Ω (Subgroup.zpowers t))
  card_le : ∀ x : G, orderOf x = 2 → ContainsAlt (centralizerImage Ω (Subgroup.zpowers x)) →
    Nat.card (fixSet Ω (Subgroup.zpowers x)) ≤ Nat.card (fixSet Ω (Subgroup.zpowers t))
  nine_le : 9 ≤ Nat.card (fixSet Ω (Subgroup.zpowers t))
  even_or_top : Nat.card (fixSet Ω (Subgroup.zpowers t)) = 9 →
    t ∈ evenSubgroup G Ω ∨ centralizerImage Ω (Subgroup.zpowers t) = ⊤
  pt : Fin 5 ↪ Ω
  pt_mem : ∀ i, pt i ∈ fixSet Ω (Subgroup.zpowers t)

namespace StarData

variable {G Ω} (D : StarData G Ω)

@[expose] def p1 : Ω := D.pt 0

@[expose] def p2 : Ω := D.pt 1

@[expose] def p3 : Ω := D.pt 2

@[expose] def p4 : Ω := D.pt 3

@[expose] def p5 : Ω := D.pt 4

@[expose] def P123 : Set Ω := {D.p1, D.p2, D.p3}

@[expose] def P1234 : Set Ω := {D.p1, D.p2, D.p3, D.p4}

@[expose] def Γ : Set Ω := orbit (fixingSubgroup G D.P123) D.p4

@[expose] def Δ : Set Ω := orbit (fixingSubgroup G D.P1234) D.p5

end StarData

end Star

end CFSG.Holt
