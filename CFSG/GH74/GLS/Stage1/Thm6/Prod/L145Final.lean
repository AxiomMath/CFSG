module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Wrap
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14 CFSG.GH74.GLS.Stage2.Local

theorem lemma14_5_thm (h144 : Lemma14_4) : Lemma14_5 := by
  intro G _ _ hStd x T V S a b y o u hu hnz
  rcases involution_conj_z_or_x h144 hStd o hu with hz | hx
  · exact absurd hz hnz
  · obtain ⟨g, hg⟩ := isConj_iff.1 hx
    rw [← hg]
    exact L145.m12NonCentral_conj CFSG.GorensteinWalter.gorensteinWalter o g

end CFSG.GH74.GLS.Stage1.Thm6.Prod
