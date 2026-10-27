module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddLinearTwo
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddUnitary
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddOrthogonal
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddSymplectic
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddExceptional

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem fixedRootSelector_oddLieType :
    FixedRootSelector fun D _ => OddLieType D := by
  rintro D _ _ hDs ⟨t, m, p, f, -, hp2, hadm, hD⟩ n hn K _ _ hK α hα S hSα hSn hSK hr
  by_cases htc : t ∈ classicalTags
  · cases t
    case PSL =>
      obtain ⟨-, -, hm2, -, -⟩ := hadm
      rcases Nat.lt_or_ge m 3 with hm | hm
      · obtain rfl : m = 2 := by omega
        exact fixedRootSelector_oddLinearTwo D hDs ⟨p, f, hp2, hD⟩ n hn K hK α hα S hSα hSn hSK hr
      · exact fixedRootSelector_oddHigherLinear_lieModel D hDs ⟨m, p, f, hp2, hm, hD⟩ n hn K hK α
          hα S hSα hSn hSK hr
    case PSU =>
      exact fixedRootSelector_oddUnitary_lieModel D hDs ⟨m, p, f, hp2, hD⟩ n hn K hK α hα S hSα
        hSn hSK hr
    case PSp =>
      exact fixedRootSelector_oddSymplectic_lieModel D hDs ⟨m, p, f, hp2, hD⟩ n hn K hK α hα S hSα
        hSn hSK hr
    case POmegaOdd =>
      exact fixedRootSelector_oddOrthogonal_lieModel D hDs ⟨.POmegaOdd, m, p, f, Or.inl rfl, hp2, hD⟩
        n hn K hK α hα S hSα hSn hSK hr
    case POmegaPlus =>
      exact fixedRootSelector_oddOrthogonal_lieModel D hDs
        ⟨.POmegaPlus, m, p, f, Or.inr (Or.inl rfl), hp2, hD⟩ n hn K hK α hα S hSα hSn hSK hr
    case POmegaMinus =>
      exact fixedRootSelector_oddOrthogonal_lieModel D hDs
        ⟨.POmegaMinus, m, p, f, Or.inr (Or.inr rfl), hp2, hD⟩ n hn K hK α hα S hSα hSn hSK hr
    all_goals exact absurd htc (by decide)
  · exact fixedRootSelector_oddExceptional D hDs ⟨t, m, p, f, htc, hp2, hD⟩ n hn K hK α hα S hSα
      hSn hSK hr

end CFSG.LocalAnalysis.EvenBN.GMSK
