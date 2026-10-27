module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F10
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F11.Factor
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F11

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem f10_conj
    (γ : ↥(L0 ⊓ Zq) ≃* ↥(L0 ⊓ Zq)) :
    ∃ c ∈ Zq, c ∈ Ze ∧ ∀ b : ↥(L0 ⊓ Zq), ((γ b : ↥(L0 ⊓ Zq)) : Q3) = c * (b : Q3) * c⁻¹ := by
  obtain ⟨c, hcT, hc⟩ := exists_conj_of_aut_inf
    (K := cocodeExtension_Zq.Bduad (tauM24 0) (tauM24 1))
    (T := cocodeExtension_Zq.Bhat (tauM24 0) (tauM24 1)) B0_subgroupOf_Zq_eq_Bduad
    (fun γ' => cocodeExtension_Zq.exists_conj_of_aut_Bduad tauM24_zero_ne_one γ') γ
  exact ⟨(c : Q3), c.2, (mem_Ze_iff_mem_Bhat c).2 hcT, hc⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
