module

public import CFSG.Combinatorics.HexagonStabilizerFaithfulSupport

public section

open CFSG.Combinatorics.CubicBipartiteMoore

namespace CFSG.Combinatorics.HexagonStabilizerFaithful

theorem hexagon_point_stabilizer_opposite_layer_action_is_faithful {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 126)
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3) (col : G.Coloring Bool)
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (w : {v : V // col v = false}) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    let O : Set {v : V // col v = false} := {x | Γ.dist w x = 3}
    (∀ f : G ≃g G, f ∈ partAut G col ↔
      f '' {v | col v = false} = {v | col v = false} ∧
        f '' {v | col v = true} = {v | col v = true}) ∧
      (∀ (g : MulAction.stabilizer (partAut G col) (w : V)) (x : O),
        ((oppositeRestriction G col w g x : {v : V // col v = false}) : V) =
          ((g : partAut G col) : G ≃g G) x) ∧
      Function.Injective (oppositeRestriction G col w) ∧
      ∀ {X : Type*} (Ξ : SimpleGraph X), Nonempty (Γ.induce O ≃g Ξ) →
        Nat.card (MulAction.stabilizer (partAut G col) (w : V)) ≤ Nat.card (Ξ ≃g Ξ) := by
  intro Γ O
  have hinj := oppositeRestriction_injective G col hcard hconn hdeg hcyc w
  refine ⟨mem_partAut_iff_image, oppositeRestriction_apply G col w, hinj, fun {X} Ξ ⟨e⟩ => ?_⟩
  have hfin : Finite (Γ.induce O ≃g Γ.induce O) :=
    Finite.of_injective _ RelIso.toEquiv_injective
  calc Nat.card (MulAction.stabilizer (partAut G col) (w : V)) ≤
        Nat.card (Γ.induce O ≃g Γ.induce O) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (Ξ ≃g Ξ) :=
      Nat.card_congr
        { toFun := fun f => (e.symm.trans f).trans e
          invFun := fun f => (e.trans f).trans e.symm
          left_inv := fun f => RelIso.ext fun x => by simp
          right_inv := fun f => RelIso.ext fun x => by simp }

end CFSG.Combinatorics.HexagonStabilizerFaithful
