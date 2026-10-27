module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeNID
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeThreeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

section TD4Main

theorem l154OmegaTD4_excRee : L154OmegaTD4 l154ExcRee := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hc hQ hxp hyp hxy hInnx hF hJ hJy
  rintro ⟨rfl, hT⟩
  by_cases hcm : CentMod 3 S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).2 ⟨rfl, hT⟩
  exact l154_false_of_ree_td4 hSn hqS hSp hc hQ hxp hyp hxy hInnx hF hJ hJy hcm hT

theorem l154TD4On_excRee : L154TD4On l154ExcRee :=
  l154TD4On_of_omegaTD4 l154OmegaTD4_excRee

end TD4Main

section NIDMain

theorem l154OmegaNID_excRee (h3 : L154ReeThreeRes) : L154OmegaNID l154ExcRee := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hc hQ hxp hyp hxy hInnx hF hJ hJy
  refine ⟨hJy, fun hInnJ => ?_⟩
  by_cases hcm : CentMod p S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).1.2 hInnJ
  have hp3 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  rcases hp3 with rfl | hp5
  · exact l154_false_of_ree_innDiag_three h3 hSn hqS hSp hc hQ hxp hyp hxy hInnx hF hJ hJy hcm
      hInnJ
  · exact l154_false_of_ree_innDiag_ge5 hp hp5 hSn hqS hSp hc hQ hxp hyp hxy hInnx hF hJ hJy hcm
      hInnJ

theorem l154OmegaNID_excRee_holds : L154OmegaNID l154ExcRee :=
  l154OmegaNID_excRee l154ReeThreeRes_holds

theorem l154NIDOn_excRee_holds : L154NIDOn l154ExcRee :=
  l154NIDOn_of_omegaNID l154OmegaNID_excRee_holds

end NIDMain

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
