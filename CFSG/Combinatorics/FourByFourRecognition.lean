module

public import CFSG.Combinatorics.FourByFourRecognitionSupport
public import CFSG.Combinatorics.FourByFourPeriodicGraphCycles

public section

namespace CFSG.Combinatorics.FourByFourPeriodicGraph

theorem periodic_three_involution_relations_recognize_four_by_four_graph {Ω : Type*}
    (r : Fin 3 → Ω → Ω) (hinv : ∀ i x, r i (r i x) = x) (hfix : ∀ i x, r i x ≠ x)
    (hdist : ∀ x, Function.Injective fun i => r i x)
    (hconn : (AperiodicSixteenGraph.colourGraph r).Connected)
    (hcyc : ∀ x (p : (AperiodicSixteenGraph.colourGraph r).Walk x x), p.IsCycle →
      p.length ≠ 3 ∧ p.length ≠ 4)
    (hrel₁ : ∀ x, r 2 (r 1 (r 0 (r 2 (r 1 (r 0 x))))) = x)
    (hrel₂ : ∀ x, r 1 (r 0 (r 1 (r 0 (r 1 (r 0 (r 1 (r 0 x))))))) = x)
    (hrel₃ : ∀ x, r 2 (r 0 (r 2 (r 0 (r 2 (r 0 (r 2 (r 0 x))))))) = x) :
    (∀ ω₀ : Ω, ∃! φ : Vertex ≃ Ω, φ o = ω₀ ∧ IsColouredIso (fun i x y => y = r i x) φ) ∧
      (∀ φ : Vertex ≃ Ω, IsColouredIso (fun i x y => y = r i x) φ ↔
        ∀ p i, φ (nbr p i) = r i (φ p)) ∧
      (∀ φ : Vertex ≃ Ω, IsColouredIso (fun i x y => y = r i x) φ →
        ∀ p q, P4.Adj p q ↔ (AperiodicSixteenGraph.colourGraph r).Adj (φ p) (φ q)) ∧
      Finite Ω ∧ Nat.card Ω = 32 ∧
      Nat.card (AperiodicSixteenGraph.colourGraph r ≃g AperiodicSixteenGraph.colourGraph r) ≤
        192 := by
  set Γ := AperiodicSixteenGraph.colourGraph r with hΓ
  have hiff : ∀ φ : Vertex ≃ Ω, IsColouredIso (fun i x y => y = r i x) φ ↔
      ∀ p i, φ (nbr p i) = r i (φ p) := by
    intro φ
    constructor
    · intro h p i
      exact (h i p (nbr p i)).mp ((colourAdj_iff_eq_nbr i p (nbr p i)).mpr rfl)
    · intro h i p q
      rw [colourAdj_iff_eq_nbr]
      constructor
      · rintro rfl
        exact h p i
      · intro hq
        exact φ.injective (hq.trans (h p i).symm)
  have hadj : ∀ φ : Vertex ≃ Ω, IsColouredIso (fun i x y => y = r i x) φ →
      ∀ p q, P4.Adj p q ↔ Γ.Adj (φ p) (φ q) := by
    intro φ hφ p q
    have hφ' := (hiff φ).mp hφ
    rw [hΓ, AperiodicSixteenGraph.colourGraph_adj hinv, adj_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨fun h => hfix i (φ p) ((hφ' p i).symm.trans h.symm), i, hφ' p i⟩
    · rintro ⟨-, i, hi⟩
      exact ⟨i, φ.injective (hi.trans (hφ' p i).symm)⟩
  have hex : ∀ ω₀ : Ω, ∃! φ : Vertex ≃ Ω, φ o = ω₀ ∧ IsColouredIso (fun i x y => y = r i x) φ := by
    intro ω₀
    obtain ⟨φ, ⟨hφo, hφ⟩, huniq⟩ :=
      existsUnique_colour_equiv hinv hfix hdist hconn hcyc hrel₁ hrel₂ hrel₃ ω₀
    exact ⟨φ, ⟨hφo, (hiff φ).mpr hφ⟩, fun ψ ⟨hψo, hψ⟩ => huniq ψ ⟨hψo, (hiff ψ).mp hψ⟩⟩
  obtain ⟨ω₀⟩ := hconn.nonempty
  obtain ⟨φ, ⟨-, hφ⟩, -⟩ := hex ω₀
  let e : P4 ≃g Γ := ⟨φ, fun {p q} => (hadj φ hφ p q).symm⟩
  have hcard : Nat.card (Γ ≃g Γ) = Nat.card (P4 ≃g P4) :=
    Nat.card_congr
      { toFun := fun f => (e.trans f).trans e.symm
        invFun := fun g => (e.symm.trans g).trans e
        left_inv := fun f => RelIso.ext fun x => by simp
        right_inv := fun g => RelIso.ext fun x => by simp }
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hAut⟩ :=
    four_by_four_periodic_cubic_graph_local_cycles_and_automorphism_bound
  refine ⟨hex, hiff, hadj, Finite.of_equiv Vertex φ, ?_, hcard ▸ hAut⟩
  rw [← Nat.card_congr φ, Nat.card_eq_fintype_card, card_vertex]

end CFSG.Combinatorics.FourByFourPeriodicGraph
