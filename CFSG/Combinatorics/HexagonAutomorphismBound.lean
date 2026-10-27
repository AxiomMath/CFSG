module

public import CFSG.Combinatorics.AperiodicDualPeriodic
public import CFSG.Combinatorics.PeriodicOppositeRecognition

public section

open CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonStabilizerFaithful CFSG.Combinatorics.AperiodicOppositeComponents
  CFSG.Combinatorics.HexagonAlternatingOctagons CFSG.Combinatorics.PeriodicOppositeRecognition

namespace CFSG.Combinatorics.HexagonAutomorphismBound

theorem partAut_dualCol {V : Type*} {G : SimpleGraph V} (col : G.Coloring Bool) :
    partAut G (dualCol col) = partAut G col := by
  ext f
  rw [mem_partAut, mem_partAut]
  simp only [dualCol_apply, Bool.not_inj_iff]

theorem order_two_generalized_hexagon_automorphism_bound {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 126)
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3) (col : G.Coloring Bool)
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length) :
    (∀ f : G ≃g G, f ∈ partAut G col ↔
      f '' {v | col v = false} = {v | col v = false} ∧
        f '' {v | col v = true} = {v | col v = true}) ∧
      Nat.card (partAut G col) ≤ 12096 := by
  refine ⟨mem_partAut_iff_image, ?_⟩
  have H : MooreHyp G := ⟨hcard, hconn, hdeg, hcyc⟩
  obtain ⟨w⟩ : Nonempty {v : V // col v = false} := by
    obtain ⟨v₀⟩ := hconn.nonempty
    cases h : col v₀
    · exact ⟨⟨v₀, h⟩⟩
    · obtain ⟨m, hm, -⟩ := exists_adj_ne hdeg v₀ v₀
      exact ⟨⟨m, col_eq_false_of_adj col h hm.symm⟩⟩
  obtain ⟨ℓ, p, z, q, c, ε, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩ := exists_frameData H col w
  by_cases hper : ∃ x : Fin 6 → {v : V // col v = false},
      (Function.Injective x ∧ (∀ n, x n ∈ {y | (pointGraph G col).dist w y = 3}) ∧
        ∀ n, (pointGraph G col).Adj (x n) (x (n + 1))) ∧
      ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∀ n, c (x n) (x (n + 1)) = ![i, j, k, i, j, k] n
  ·
    exact (periodic_point_opposite_graph_recognition_and_automorphism_bound G H col w ℓ hℓ hwℓ p
      hpℓ hpw hp z q c ε hdata hper).2.2.2.2.2
  ·
    obtain ⟨r, hr⟩ := exists_colour_moving G H col w ℓ hℓ hwℓ p hpℓ hpw hp z q c ε hdata
    have hu : dualCol col (ℓ 0) = false := by
      rw [dualCol_apply, col_eq_true_of_adj col w.2 (hwℓ 0)]
      rfl
    obtain ⟨⟨ℓ', p', z', q', c', ε', hℓ', huℓ', hpℓ', hpu', hp', hdata'⟩, hdual⟩ :=
      lines_through_an_aperiodic_point_are_dual_periodic G H col w ℓ hℓ hwℓ p hpℓ hpw hp z q c ε
        hdata r (fun i x hx => (hr i x hx).1) hper ⟨ℓ 0, hu⟩ (hwℓ 0)
    rw [← partAut_dualCol]
    exact (periodic_point_opposite_graph_recognition_and_automorphism_bound G H (dualCol col)
      ⟨ℓ 0, hu⟩ ℓ' hℓ' huℓ' p' hpℓ' hpu' hp' z' q' c' ε' hdata'
      (hdual ℓ' hℓ' huℓ' p' hpℓ' hpu' hp' z' q' c' ε' hdata')).2.2.2.2.2

end CFSG.Combinatorics.HexagonAutomorphismBound
