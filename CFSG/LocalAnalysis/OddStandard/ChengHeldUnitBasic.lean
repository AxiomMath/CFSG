module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2UniqW

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.rep_of_kinds_unitary (c : Chart4 d α) (hk : c.kinds = {Kind.unitary}) :
    c.rep Kind.field = none ∧ c.rep Kind.graph = none ∧ ∃ y, c.rep Kind.unitary = some y := by
  have h := Set.ext_iff.1 hk
  have hf := h Kind.field
  have hg := h Kind.graph
  have hu := h Kind.unitary
  simp only [Chart4.kinds, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hf hg hu
  refine ⟨?_, ?_, ?_⟩
  · simpa using hf
  · simpa using hg
  · exact Option.isSome_iff_exists.1 (hu.2 trivial)

theorem Chart4.cover_unitary (c : Chart4 d α) (hk : c.kinds = {Kind.unitary}) {y : G}
    (hy : c.rep Kind.unitary = some y) {x : G} (hx : x ∈ d.X) (hxQS : x ∉ d.QS) :
    ∃ u ∈ d.QS, x = u * y := by
  obtain ⟨hf, hg, -⟩ := c.rep_of_kinds_unitary hk
  obtain ⟨k, y₀, hrep, u, hu, rfl⟩ := c.cover x hx hxQS
  cases k with
  | field => rw [hf] at hrep; exact absurd hrep (by simp)
  | graph => rw [hg] at hrep; exact absurd hrep (by simp)
  | unitary =>
    rw [hy] at hrep
    obtain rfl : y = y₀ := Option.some.inj hrep
    exact ⟨u, hu, rfl⟩

theorem Chart4.act_mul_Q (c : Chart4 d α) (k : Kind) {y x : G} (hx : x ∈ d.Q)
    (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi (y * x) := by
  have ht := c.t_mem.2
  obtain ⟨hpi, htau, hmu, hlam, hze, hxi⟩ := c.mem
  have key : ∀ {a b : G}, b ∈ d.S → cj a y = b → cj a (y * x) = b := fun hb h => by
    rw [← ChartShape.cj_cj, h]
    exact ChartShape.cj_of_commute (d.comm_Q_S hx hb)
  cases k <;> unfold Kind.Act at hact ⊢ <;> split_ifs at hact ⊢ <;>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hact <;>
    refine ⟨key ?_ h1, key ?_ h2, key ?_ h3, key ?_ h4, key ?_ h5, key ?_ h6, key ?_ h7⟩ <;>
    repeat' first | apply mul_mem | apply inv_mem | apply pow_mem | assumption

end CFSG.OddStandard.ChengHeld
