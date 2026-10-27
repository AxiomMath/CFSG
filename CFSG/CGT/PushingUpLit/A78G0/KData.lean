module

public import CFSG.CGT.PushingUpLit.A78.Sp4Local
public import CFSG.CGT.PushingUpLit.A78G0.Data

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit.A78

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}

structure KData (_h : G0Core G L₁ L₂ V W Z Z₂ e) (K A : Subgroup G) : Prop where
  le_L : K ≤ L₁
  inf_V : K ⊓ V = ⊥
  sup_V : V ⊔ K = L₁
  A_le : A ≤ K
  A_card : Nat.card A = 2 ^ e
  A_mem : A ∈ zClass Z

end CFSG.CGT.PushingUpLit.A78G0
