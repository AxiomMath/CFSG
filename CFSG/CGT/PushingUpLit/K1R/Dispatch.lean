module

public import CFSG.CGT.PushingUpLit.K1R.Reduce
public import CFSG.CGT.PushingUpLit.K1R.Even
public import CFSG.CGT.PushingUpLit.K1R.Exceptional
public import CFSG.CGT.PushingUpLit.K1R.Alternating
public import CFSG.CGT.PushingUpLit.K1R.OddLinear
public import CFSG.CGT.PushingUpLit.K1R.OddUnitary
public import CFSG.CGT.PushingUpLit.K1R.OddSymplectic
public import CFSG.CGT.PushingUpLit.K1R.OddOrthogonal
public import CFSG.CGT.PushingUpLit.K1R.SporSmall
public import CFSG.CGT.PushingUpLit.K1R.SporLarge
public import CFSG.CGT.PushingUpLit.K1R.SporSpecial
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatDispatch

public section

namespace CFSG.CGT.PushingUpLit.K1R

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.EvenBN.GMSK

theorem innerKernelSelector_sporadic :
    InnerKernelSelector fun D _ => NativeSporadic.SporadicRep D := by
  intro D _ _ hD ⟨s, hs⟩ n hn K _ _ hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  cases s with
  | M11 => exact m11_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | M12 => exact m12_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | M22 => exact m22_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | M23 => exact m23_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | M24 => exact m24_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | J1 => exact j1_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | J2 => exact j2_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | J3 => exact j3_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | J4 => exact j4_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | HS => exact hs_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | McL => exact mcl_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | He => exact he_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Ru => exact ru_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Suz => exact suz_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | ONan => exact on_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Co1 => exact co1_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Co2 => exact co2_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Co3 => exact co3_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Fi22 => exact fi22_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Fi23 => exact fi23_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Fi24Prime => exact fi24prime_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | HN => exact hn_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Ly => exact ly_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | Th => exact th_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | B => exact b_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  | M => exact m_innerKernel D hD hs n hn K hK α hα hin S hSα hSn hSK hnf Q hQ hQp

theorem innerKernelSelector_oddLieType :
    InnerKernelSelector fun D _ => OddLieType D := by
  rintro D _ _ hD ⟨t, m, p, f, -, hp2, hadm, hM⟩ n hn K _ _ hK α hα hin S hSα hSn hSK hnf Q hQ
    hQp
  by_cases htc : t ∈ classicalTags
  · cases t
    case PSL =>
      obtain ⟨-, -, hm2, -, -⟩ := hadm
      rcases Nat.lt_or_ge m 3 with hm | hm
      · obtain rfl : m = 2 := by omega
        exact innerKernelSelector_oddLinearTwo D hD ⟨p, f, hp2, hM⟩ n hn K hK α hα hin S hSα hSn
          hSK hnf Q hQ hQp
      · exact innerKernelSelector_oddHigherLinear D hD ⟨m, p, f, hp2, hm, hM⟩ n hn K hK α hα hin S
          hSα hSn hSK hnf Q hQ hQp
    case PSU =>
      exact innerKernelSelector_oddUnitary D hD ⟨m, p, f, hp2, hM⟩ n hn K hK α hα hin S hSα hSn
        hSK hnf Q hQ hQp
    case PSp =>
      exact innerKernelSelector_oddSymplectic D hD ⟨m, p, f, hp2, hM⟩ n hn K hK α hα hin S hSα hSn
        hSK hnf Q hQ hQp
    case POmegaOdd =>
      exact innerKernelSelector_oddOrthogonal D hD ⟨.POmegaOdd, m, p, f, Or.inl rfl, hp2, hM⟩ n hn
        K hK α hα hin S hSα hSn hSK hnf Q hQ hQp
    case POmegaPlus =>
      exact innerKernelSelector_oddOrthogonal D hD
        ⟨.POmegaPlus, m, p, f, Or.inr (Or.inl rfl), hp2, hM⟩ n hn K hK α hα hin S hSα hSn hSK hnf
        Q hQ hQp
    case POmegaMinus =>
      exact innerKernelSelector_oddOrthogonal D hD
        ⟨.POmegaMinus, m, p, f, Or.inr (Or.inr rfl), hp2, hM⟩ n hn K hK α hα hin S hSα hSn hSK hnf
        Q hQ hQp
    all_goals exact absurd htc (by decide)
  · exact innerKernelSelector_oddExceptional D hD ⟨t, m, p, f, htc, hp2, hM⟩ n hn K hK α hα hin S
      hSα hSn hSK hnf Q hQ hQp

theorem innerKernelSelector_catalog :
    InnerKernelSelector fun D _ => Catalog D := by
  intro D _ _ hD hcat n hn K _ _ hK α hα hin S hSα hSn ⟨φ⟩ hnf Q hQ hQp
  rcases (Milestones.ct_catalog_nonabelian_type_partition D (exists_mul_ne_of_sl2 φ)).1 hcat with
    h | h | h | h
  · exact innerKernelSelector_alternating D hD h n hn K hK α hα hin S hSα hSn ⟨φ⟩ hnf Q hQ hQp
  · exact innerKernelSelector_oddLieType D hD h n hn K hK α hα hin S hSα hSn ⟨φ⟩ hnf Q hQ hQp
  · exact innerKernelSelector_evenLieType D hD h n hn K hK α hα hin S hSα hSn ⟨φ⟩ hnf Q hQ hQp
  · exact innerKernelSelector_sporadic D hD h n hn K hK α hα hin S hSα hSn ⟨φ⟩ hnf Q hQ hQp

theorem stdKernelTwo_holds :
    CFSG.CGT.PushingUpLit.CGT6K1.StdKernelTwo :=
  stdKernelTwo_of_selector innerKernelSelector_catalog

end CFSG.CGT.PushingUpLit.K1R
