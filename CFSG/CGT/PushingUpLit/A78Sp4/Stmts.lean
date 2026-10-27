module

public import CFSG.CGT.PushingUpLit.A78Sp4.Data

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

variable {G : Type} [Group G]

@[expose] def Sp4Stmt410 (V V₂ Z Z₂ J : Subgroup G) : Prop :=
  ∀ u : G, UType V V₂ Z Z₂ u →
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)

@[expose] def Sp4StmtM (S J : Subgroup G) : Prop :=
  ∀ a ∈ S, a * a = 1 → ∀ g : G, g⁻¹ * a * g ∈ J → a ∈ J

@[expose] def Sp4Stmt412 (T J : Subgroup G) : Prop := T = J

end CFSG.CGT.PushingUpLit.A78Sp4
