module

public import CFSG.LieType.Chevalley.E6GraphMonomialToral

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem E6_geometric_graph_involution_two_representatives
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    {x : ModGL TwistTag.E6.tag k} (hx : x ∈ adjointGroup TwistTag.E6.tag k)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    ∃ g ∈ adjointGroup TwistTag.E6.tag k,
      g * (x * diagramMap TwistTag.E6 k) * g⁻¹ = diagramMap TwistTag.E6 k ∨
        g * (x * diagramMap TwistTag.E6 k) * g⁻¹ =
          rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k := by
  set P := diagramMap TwistTag.E6 k with hP
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  have hconj2 : ∀ g y : ModGL TwistTag.E6.tag k, y ^ 2 = 1 → (g * y * g⁻¹) ^ 2 = 1 :=
    fun g y hy => by
      rw [sq] at hy ⊢
      calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hy]; group
  obtain ⟨u, hu, n, hn, hun⟩ :=
    E6_graph_involution_finite_extension_monomial_reduction hp2 k halg hx hx2
  have hnP : (n * P) ^ 2 = 1 := by
    rw [← hun]
    exact hconj2 _ _ hx2
  obtain ⟨v, hv, a, hva, -⟩ := E6_graph_monomial_involution_toral_conjugacy k hk hn hnP
  have haP : (rootDiagUnit TwistTag.E6.tag a * P) ^ 2 = 1 := by
    rw [← hva]
    exact hconj2 _ _ hnP
  obtain ⟨z, hz, hza⟩ := E6_toral_graph_involution_two_representatives k a haP
  have e : z * v * u * (x * P) * (z * v * u)⁻¹ =
      z * (rootDiagUnit TwistTag.E6.tag a * P) * z⁻¹ := by
    calc z * v * u * (x * P) * (z * v * u)⁻¹ = z * (v * (u * (x * P) * u⁻¹) * v⁻¹) * z⁻¹ := by
          group
      _ = _ := by rw [hun, hva]
  refine ⟨z * v * u, mul_mem (mul_mem hz hv) hu, ?_⟩
  rw [e]
  exact hza

end CFSG.LieType.Chevalley
