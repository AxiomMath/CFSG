module

public import CFSG.ClassicalInvolution.Q3.TL4WylE
public import CFSG.ClassicalInvolution.Q3.TL4E4CoverNbrs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem secIdE4Frame_proved :
    SecIdE4Frame := by
  intro Y _ _ R S t hd hc hO2 hZ hM B₁ hB₁ B₂ hB₂ hB₂K
  refine ⟨fun B hB v hv => secIdE4LinkCent_proved Y R S t hd hc hO2 hZ hM B hB v hv, ?_⟩
  have hO := secIdE4OddCent_proved Y R S t hd hc hO2 hZ hM
  have h2R := hd.isPGroup_of_oddCent hO
  have hcore := tightCore_eq_self_of_isPGroup h2R
  have hq : Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) := by
    obtain ⟨eS⟩ := hc.1
    have hS : (S : Subgroup R) = ⊤ := (S.is_maximal' (h2R.to_subgroup ⊤) le_top).symm
    exact ⟨((MulEquiv.subgroupCongr hcore).trans
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hS.symm))).trans eS⟩
  have htw : ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      L = tightCore R := fun L hL => by
    rw [hd.twinSet_eq] at hL
    exact hL
  obtain ⟨h1, h3, -⟩ := e4CoverNbrs_proved Y (Subgroup.center Y) (tightCore R) t
    (Vtx.isPGroup_center_of_oddFree hc.2.2) le_rfl hd.hypOmegaGen hq hd.isUniqueInvolution_core
    (Vtx.not_mem_center_of_not_tightInO2 hd.order hO2) htw hM
  rcases hM with hPSp | hO8
  · exfalso
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (h1 hPSp)
    have e1 : B₁ = a := by
      have := hB₁
      rw [ha] at this
      exact this
    have e2 : B₂ = a := by
      have := hB₂K
      rw [ha] at this
      exact this
    exact hB₂.2.1 (e2.trans e1.symm)
  · exact h3 hO8

end CFSG.ClassicalInvolution.Q3.TL4
