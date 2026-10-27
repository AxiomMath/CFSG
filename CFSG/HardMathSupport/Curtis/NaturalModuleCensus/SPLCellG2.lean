module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellFam
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.LieType.SeitzGeneration.ExcPlaneG2

public section

open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti

namespace CFSG.HardMathSupport.Curtis.Coordinator


theorem rankLE2_cat_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hq : q.p = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : RankLE2 p (Cat ⟨LieTypeIndex.G2 q, hv⟩) := by
  have hpq : p ≠ q.p := by rw [hq]; exact hp2
  have h35 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega
  rcases h35 with rfl | h5
  · exact CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv hpq
  · obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hK]
      exact not_dvd_card_of_ne hp hpq
    exact RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_adjointGroup_G2 K hp h5 hpK)

theorem splLieInnerCellFam_G2 : SPLLieInnerCellFam IsIdxG2 := by
  intro S _ _ d hd hF ⟨e⟩ p r hp hp2 hr hr1 hr2
  obtain ⟨q, hdq⟩ := hF
  obtain ⟨idx, hv⟩ := d
  obtain rfl : idx = .G2 q := hdq
  have hq : q.p = 2 := hd
  have hR := rankLE2_cat_G2 q hv hq hp hp2
  refine SPLCellFor.of_mulEquiv e fun Ē ζ γ hE hcard _ _ _ _ _ _ _ => ?_
  have h := hR Ē hE
  rw [hcard] at h
  exact absurd h (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

end CFSG.HardMathSupport.Curtis.Coordinator
