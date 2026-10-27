module

public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

structure Y6Cfg {G : Type} [Group G] (A C0 V : Subgroup G) (a₁ b₁ a₂ b₂ z t u : G) : Prop where
  hA : A = closure {a₁, b₁, a₂, b₂}
  hC0 : C0 = closure {u, t}
  hV : V = zpowers u
  rel : Y6ARel a₁ b₁ a₂ b₂ z
  z_ne : z ≠ 1
  card_A : Nat.card ↥A = 32
  t_ord : orderOf t = 2
  u_ord : orderOf u = 4
  u_sq : u ^ 2 = z
  t_inv : t * u * t⁻¹ = u⁻¹
  t_cent : ∀ a ∈ A, a * t = t * a
  u_cent : ∀ a ∈ A, a * u = u * a

end CFSG.OddStandard.HigherRank.YamadaG23
