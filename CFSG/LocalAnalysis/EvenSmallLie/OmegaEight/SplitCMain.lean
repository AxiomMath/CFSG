module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUnique
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCBridge

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

namespace Setting

variable {ε : Eps} {t : G} {L H₀ U Q P S₀ : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}

theorem Zset_cases_of_embedding_plus
    [Finite G]
    (hS : Setting ε t L H₀ U Q P S₀ a ψ p) (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (j : S₀ →* Equiv.Perm (Fin 360))
    (hj : Function.Injective j) (hjA : ∀ s, j s ∈ OmegaEight.autT) (hcard : Nat.card S₀ = 8192) :
    (∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) ∨ ∀ v, v ∈ Zset t Q ψ :=
  hS.Zset_cases_plus hG hnab (nonempty_mulEquiv_sylowT_plus j hj hjA hcard).some

theorem Zset_cases_of_embedding_minus
    [Finite G]
    (hS : Setting ε t L H₀ U Q P S₀ a ψ p) (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (j : S₀ →* Equiv.Perm (Fin 136))
    (hj : Function.Injective j) (hjA : ∀ s, j s ∈ OmegaEightMinus.autT)
    (hcard : Nat.card S₀ = 8192) :
    (∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) ∨ ∀ v, v ∈ Zset t Q ψ :=
  hS.Zset_cases_minus hG hnab (nonempty_mulEquiv_sylowT_minus j hj hjA hcard).some

end Setting

end CFSG.EvenSmallLie.OmegaEight.SplitC
