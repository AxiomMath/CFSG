module

public import CFSG.Combinatorics.AperiodicSixteenRecognitionSupport

public section

namespace CFSG.Combinatorics.AperiodicSixteenGraph

theorem aperiodic_involution_relations_recognize_sixteen_graph {Ω : Type*} (r : Fin 3 → Ω → Ω)
    (hinv : ∀ i x, r i (r i x) = x) (hfix : ∀ i x, r i x ≠ x)
    (hdist : ∀ x, Function.Injective fun i => r i x) (hconn : (colourGraph r).Connected)
    (hcyc : ∀ x (p : (colourGraph r).Walk x x), p.IsCycle →
      p.length ≠ 3 ∧ p.length ≠ 4 ∧ p.length ≠ 5)
    (hrel : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, r k (r j (r i x)) = r i (r k (r j x))) :
    (∀ ω₀ : Ω, ∃! φ : K ≃ Ω, φ o = ω₀ ∧ ∀ g i, φ (g * s i) = r i (φ g)) ∧
      (∀ φ : K ≃ Ω, (∀ g i, φ (g * s i) = r i (φ g)) →
        ∀ g h, T.Adj g h ↔ (colourGraph r).Adj (φ g) (φ h)) ∧
      Finite Ω ∧ Nat.card Ω = 16 := by
  have hcyc' : ∀ x (p : (colourGraph r).Walk x x), p.IsCycle → p.length ≠ 3 ∧ p.length ≠ 4 :=
    fun x p hp => ⟨(hcyc x p hp).1, (hcyc x p hp).2.1⟩
  have hφ := existsUnique_colour_equiv hinv hfix hdist hconn hcyc' hrel
  obtain ⟨ω₀⟩ := hconn.nonempty
  obtain ⟨φ, -, -⟩ := hφ ω₀
  refine ⟨hφ, fun ψ hψ => adj_iff_of_colour hinv hfix ψ hψ, Finite.of_equiv K φ, ?_⟩
  rw [← Nat.card_congr φ, Nat.card_eq_fintype_card, K.card]

end CFSG.Combinatorics.AperiodicSixteenGraph
