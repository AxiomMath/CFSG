module

public import CFSG.ClassicalInvolution.Q3.TL4Res2FDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent
public import CFSG.ClassicalInvolution.Q3.TL4Sep2FB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem thm4Res2F'_of_exitModelR {n : ℕ} (hT : PhilipHall.Frame.Thm1RTwinLiftSetBelow n)
    (hB : TightBelow n) (h4 : Uniform.Thm4BelowU 3 1 n) (hE : ExitModelR n) :
    Thm4Res2F' 3 n := by
  intro G _ _ hG J L hm hgen hno L₀ hL₀ hn hlay hfit hZ hC hmem
  have hc : Res2FConfigR J L L₀ := ⟨hm, hgen, hno, hL₀, hn, hlay, hfit, hZ, hC, hmem⟩
  set Δ := CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L with hΔ
  have hodd : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
    intro K hK z hz
    by_contra hne
    exact hE G hG J L L₀ hc K hK z hz (Or.inl hne)
  have h2 : ∀ K ∈ Δ, IsPGroup 2 K := fun K hK => by
    obtain ⟨z, hz⟩ := (hm.hyp.hyp.omega1 K hK).1
    exact PhilipHall.Frame.isPGroup_of_oddCent hm.hyp.hyp hK hz (hodd K hK z hz)
      (hm.hyp.twoGroup K hK)
  have hq8 : ∀ K ∈ Δ, Nonempty (↥K ≃* QuaternionGroup 2) := fun K hK => by
    have hKS : IsSylow2In K K := ⟨le_rfl, h2 K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    exact hm.hyp.quat K hK K hKS
  have hl : PhilipHall.Frame.HasLifts Δ := by
    intro K hK
    obtain ⟨z, hz⟩ := (hm.hyp.hyp.omega1 K hK).1
    rcases PhilipHall.Frame.Thm4Twin.F2.exists_lift_or_exit hT hB hG hm.hyp.odd hm.hyp.hyp h2
      hq8 hm.hyp.aEmpty hno hK hz with ⟨L', hL'⟩ | ⟨W, hKW, hWs, hWg, hex⟩
    · exact ⟨L', z, hL'⟩
    · exact (hE G hG J L L₀ hc K hK z hz (Or.inr ⟨W, hKW, hWs, hWg, hex⟩)).elim
  have hex : PhilipHall.Frame.ExactSylow Δ :=
    PhilipHall.Frame.ExactSylow.of_oddCoreIn_eq_bot fun K hK _ u h => hodd K hK u h.inv
  exact hm.notComm (PhilipHall.Frame.commutes_of_thm4U_exact h4 hG hm.hyp.odd hm.hyp.hyp h2 hl
    hex hm.hyp.aEmpty hm.memJ hm.memL hm.notConj)

end CFSG.ClassicalInvolution.Q3.TL4
