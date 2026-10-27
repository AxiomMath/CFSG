module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcAutReduction
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcAltSix
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcU33
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcTits
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsU33

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 in
theorem gomiChevExcInvolution_holds :
    GomiChevExcInvolution := by
  refine gomiChevExcInvolution_of_gomiExcAutFixed fun K _ _ hK => ?_
  rcases hK with ⟨_, f, hL⟩ | ⟨⟨e⟩⟩ | hU
  · have hR : CFSG.Blueprint.ReeTitsModel K .Tits 2 f := by
      rcases hL with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
      · exact absurd hcl (by decide)
      · exact absurd hce (by decide)
      · exact hree
      · exact absurd hsz (by decide)
    obtain ⟨e⟩ := titsModelEquiv K 2 f hR
    exact GomiExcAutFixed.of_mulEquiv e.symm gomiExcAutFixed_titsD
  · exact GomiExcAutFixed.of_mulEquiv e.symm gomiExcAutFixed_alt6
  · obtain ⟨e⟩ := nonempty_mulEquiv_u33G_of_statedClassicalModel hU
    have : Finite U33G := u33Pres_finite_card_le.1
    exact GomiExcAutFixed.of_mulEquiv e.symm gomiExcAutFixed_u33G

end CFSG.GroupTheory
