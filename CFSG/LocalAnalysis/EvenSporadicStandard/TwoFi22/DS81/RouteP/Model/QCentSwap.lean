module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.TPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Graph

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem mul_ne_mul_of_smul_x0_eq_x1
    (hP0 : {y : Ω | Δ.Adj x0 y ∧ t13 • y = y}.ncard = 3511)
    (hP1 : {y : Ω | Δ.Adj x0 y ∧ t13 • (tauElt • y) = tauElt • y}.ncard = 695)
    {g : Q3} (h0 : g • x0 = x1) : g * t13 ≠ t13 * g := by
  intro hc
  set h : Q3 := tauElt⁻¹ * g with hh
  have hx0 : h • x0 = x0 := by
    rw [hh, mul_smul, h0, inv_smul_eq_iff]
    exact tauElt_smul_x0.symm
  have hmaps : ∀ y ∈ {y : Ω | Δ.Adj x0 y ∧ t13 • y = y},
      h • y ∈ {y : Ω | Δ.Adj x0 y ∧ t13 • (tauElt • y) = tauElt • y} := by
    intro y hy
    refine ⟨?_, ?_⟩
    · have h' := (Δ_adj_smul h x0 y).2 hy.1
      rwa [hx0] at h'
    · have hgy : tauElt • (h • y) = g • y := by
        rw [hh, mul_smul, smul_inv_smul]
      rw [hgy]
      calc t13 • (g • y) = (t13 * g) • y := (mul_smul t13 g y).symm
        _ = (g * t13) • y := by rw [← hc]
        _ = g • (t13 • y) := mul_smul g t13 y
        _ = g • y := by rw [hy.2]
  have hinj : Set.InjOn (fun y : Ω => h • y)
      {y : Ω | Δ.Adj x0 y ∧ t13 • y = y} :=
    (MulAction.injective h).injOn
  have hle : {y : Ω | Δ.Adj x0 y ∧ t13 • y = y}.ncard ≤
      {y : Ω | Δ.Adj x0 y ∧ t13 • (tauElt • y) = tauElt • y}.ncard :=
    Set.ncard_le_ncard_of_injOn (fun y : Ω => h • y) hmaps hinj (Set.toFinite _)
  rw [hP0, hP1] at hle
  omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
