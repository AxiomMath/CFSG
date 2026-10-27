module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Cocode

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem mem_Ze_iff_mem_Bhat
    (n : ↥Zq) : (n : Q3) ∈ Ze ↔ n ∈ cocodeExtension_Zq.Bhat (tauM24 0) (tauM24 1) :=
  (mem_Ze_iff_π n).trans cocodeExtension_Zq.mem_Bhat_iff.symm

theorem conj_mem_L0_of_mem_Ze
    {c k : Q3} (hc : c ∈ Ze) (hk : k ∈ L0) : c * k * c⁻¹ ∈ L0 := by
  obtain ⟨hk0, hk1⟩ := mem_L0_iff.1 hk
  rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff] at hk0
  rw [mem_Ze_iff] at hc
  rw [mem_L0_iff, Zp_eq_stabilizer, MulAction.mem_stabilizer_iff]
  rcases hc with ⟨hc0, hc1⟩ | ⟨hc0, hc1⟩
  · have hc0' : c⁻¹ • x0 = x0 := by rw [inv_smul_eq_iff]; exact hc0.symm
    have hc1' : c⁻¹ • x1 = x1 := by rw [inv_smul_eq_iff]; exact hc1.symm
    constructor
    · rw [mul_smul, mul_smul, hc0', hk0, hc0]
    · rw [mul_smul, mul_smul, hc1', hk1, hc1]
  · have hc0' : c⁻¹ • x0 = x1 := by rw [inv_smul_eq_iff]; exact hc1.symm
    have hc1' : c⁻¹ • x1 = x0 := by rw [inv_smul_eq_iff]; exact hc0.symm
    constructor
    · rw [mul_smul, mul_smul, hc0', hk1, hc1]
    · rw [mul_smul, mul_smul, hc1', hk0, hc0]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
