module

public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeF4
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.RankThree.PartOne.SEITZQ3.Main

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.CTP


theorem seitzExcAnisotropicReeF4Three_holds : SeitzExcAnisotropicReeF4Three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, ⟨m, hdm⟩, hp3, -, -⟩
  simp only at hdm hp3 hin
  subst hdm hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, _, _, _, hm1, hX, hsimple, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have : Finite (Cat ⟨.reeF4 m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hel : IsElementaryAbelian 3 ↥E := isElementaryAbelian_of_isElemAbelian hE
  rw [planeGen_iff_closure_fixUnion]
  refine closure_fixUnion_eq_top_of_inner_equiv
    (exists_noncommuting_of_isElementaryAbelian_aut hel hc) e ?_ E hc
    (fun φ hφ => (hin hφ).imp fun g hg => hg.symm)
  intro E₁ hE₁ hE₁c
  exact CFSG.RankThree.PartOne.SEITZQ3.reeGamma_closure_cenGen_eq_top_three hm1 hX E₁
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx) hE₁c

end CFSG.LieType.SeitzGeneration
