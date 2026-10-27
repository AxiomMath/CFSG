module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.QCentFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.QCentOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.QCentSwap

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem Ze_inf_centralizer_t13 :
    Ze ⊓ Subgroup.centralizer ({t13} : Set Q3) = Q0 := by
  have hKL : Ze ⊓ Subgroup.centralizer ({t13} : Set Q3) ≤ L0 := by
    intro g hg
    obtain ⟨hgZ, hgC⟩ := Subgroup.mem_inf.1 hg
    have hcomm : g * t13 = t13 * g := (Subgroup.mem_centralizer_iff.1 hgC t13 rfl).symm
    have hx0 : g • x0 = x0 := by
      rcases mem_Ze_iff.1 hgZ with h | h
      · exact h.1
      · exact absurd hcomm
          (mul_ne_mul_of_smul_x0_eq_x1 ncard_fixed_gamma ncard_fixed_gamma_tau h.1)
    rw [← Ze_inf_stabilizer]
    exact Subgroup.mem_inf.2 ⟨hgZ, MulAction.mem_stabilizer_iff.2 hx0⟩
  have hQK : Q0 ≤ Ze ⊓ Subgroup.centralizer ({t13} : Set Q3) := by
    intro r hr
    refine Subgroup.mem_inf.2 ⟨L0_le_Ze (Q0_le_L0 hr), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (mul_comm_t13_of_mem_Q0 hr).symm
  have ht2 : t13 • x2 = x2 := by
    simpa [planePt_two] using E0_smul_planePt t13_mem_E0 2
  have hcover : ∀ k ∈ Ze ⊓ Subgroup.centralizer ({t13} : Set Q3),
      k • x2 = x2 ∨ k • x2 ∈ MulAction.orbit qcentW qcentRootPt := by
    intro k hk
    obtain ⟨-, hkC⟩ := Subgroup.mem_inf.1 hk
    have hcomm : k * t13 = t13 * k := (Subgroup.mem_centralizer_iff.1 hkC t13 rfl).symm
    obtain ⟨hkZp, hk1⟩ := mem_L0_iff.1 (hKL hk)
    have hk0 : k • x0 = x0 := Zp_smul_x0 hkZp
    have ha0 : Δ.Adj x0 (k • x2) := by
      have h := (Δ_adj_smul k x0 x2).2 Δ_adj_x0_x2
      rwa [hk0] at h
    have ha1 : Δ.Adj x1 (k • x2) := by
      have h := (Δ_adj_smul k x1 x2).2 Δ_adj_x1_x2
      rwa [hk1] at h
    have hta : t13 • (k • x2) = k • x2 := by
      calc t13 • (k • x2) = (t13 * k) • x2 := (mul_smul _ _ _).symm
        _ = (k * t13) • x2 := by rw [hcomm]
        _ = k • (t13 • x2) := mul_smul _ _ _
        _ = k • x2 := by rw [ht2]
    exact eq_x2_or_mem_orbit_qcentW ha0 ha1 hta
  refine le_antisymm (fun g hg => ?_) hQK
  exact mem_Q0_iff.2 ⟨hKL hg, smul_x2_eq_of_cover hQK hKL qcentW_le_Q0 card_orbit_qcentW
    notMem_orbit_qcentW hcover g hg⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
