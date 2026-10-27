module

public import Certificates.Certificate450270

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three


theorem Q_connected : (Δ.induce (Δ.commonNeighbors x0 y2)).Preconnected :=
  Certificates.certificate450270

theorem P_witness {y : Ω} (hy : Δ.dist x0 y = 2) (hadj : Δ.Adj y2 y) :
    ∃ c, Δ.Adj x0 c ∧ Δ.Adj c y2 ∧ Δ.Adj c y :=
  Certificates.certificate450270.P_witness hy hadj

theorem A3_connected_a : (Δ.induce {c | Δ.Adj y3a c ∧ Δ.dist x0 c = 2}).Preconnected :=
  Certificates.certificate450270.A3_connected_a

theorem A3_connected_b : (Δ.induce {c | Δ.Adj y3b c ∧ Δ.dist x0 c = 2}).Preconnected :=
  Certificates.certificate450270.A3_connected_b

theorem Hp_witness_a {y : Ω} (hy : Δ.dist x0 y = 3) (hadj : Δ.Adj y3a y) :
    ∃ h, Δ.dist x0 h = 2 ∧ Δ.Adj h y3a ∧ Δ.Adj h y :=
  Certificates.certificate450270.Hp_witness_a hy hadj

theorem Hp_witness_b {y : Ω} (hy : Δ.dist x0 y = 3) (hadj : Δ.Adj y3b y) :
    ∃ h, Δ.dist x0 h = 2 ∧ Δ.Adj h y3b ∧ Δ.Adj h y :=
  Certificates.certificate450270.Hp_witness_b hy hadj

theorem H4_connected : (Δ.induce {c | Δ.Adj x0 c}).Preconnected :=
  Certificates.certificate450270.H4_connected

theorem dist_x0_eq_three_of_adj_y4a {y : Ω} (hadj : Δ.Adj y4a y) : Δ.dist x0 y = 3 :=
  Certificates.certificate450270.dist_x0_eq_three_of_adj_y4a hadj

theorem dist_x0_eq_three_of_adj_y4b {y : Ω} (hadj : Δ.Adj y4b y) : Δ.dist x0 y = 3 :=
  Certificates.certificate450270.dist_x0_eq_three_of_adj_y4b hadj

theorem A4_connected_of_adj {i : Fin 7} (hi : ∀ y, Δ.Adj (repPt i) y → Δ.dist x0 y = 3) :
    (Δ.induce {c | Δ.Adj (repPt i) c ∧ Δ.dist x0 c = 3}).Preconnected := by
  have e : {c | Δ.Adj (repPt i) c ∧ Δ.dist x0 c = 3} =
      (repElt i • ·) '' {c | Δ.Adj x0 c} := by
    ext c
    constructor
    · rintro ⟨h1, -⟩
      refine ⟨(repElt i)⁻¹ • c, ?_, smul_inv_smul _ c⟩
      change Δ.Adj x0 ((repElt i)⁻¹ • c)
      rw [← Δ_adj_smul (repElt i), repElt_smul_x0, smul_inv_smul]
      exact h1
    · rintro ⟨c', hc', rfl⟩
      have h1 : Δ.Adj (repPt i) (repElt i • c') := by
        rw [← repElt_smul_x0 i]
        exact (Δ_adj_smul _ _ _).2 hc'
      exact ⟨h1, hi _ h1⟩
  rw [e]
  exact preconnected_induce_image Δ_adj_smul _ H4_connected

theorem A4_connected_a : (Δ.induce {c | Δ.Adj y4a c ∧ Δ.dist x0 c = 3}).Preconnected :=
  A4_connected_of_adj (i := 5) fun _ h => dist_x0_eq_three_of_adj_y4a h

theorem A4_connected_b : (Δ.induce {c | Δ.Adj y4b c ∧ Δ.dist x0 c = 3}).Preconnected :=
  A4_connected_of_adj (i := 6) fun _ h => dist_x0_eq_three_of_adj_y4b h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

end
