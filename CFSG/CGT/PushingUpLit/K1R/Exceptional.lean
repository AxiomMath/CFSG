module

public import CFSG.CGT.PushingUpLit.K1R.Defs
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddExceptional
public import CFSG.CGT.PushingUpLit.CGT6K1.InnerG2

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.EvenBN.GMSK


theorem innerKernelSelector_oddExceptional :
    InnerKernelSelector fun D _ => ∃ (t : StatedLieTag) (m p f : ℕ), t ∉ classicalTags ∧
      p ≠ 2 ∧ LieModel D t m p f := by
  refine InnerKernelSelector.of_false ?_
  rintro D _ _ hDs ⟨t, m, p, f, htc, hp2, hD⟩ n hn K _ _ hK α hα hin S hSα hSn hSK -
  cases t
  case G2 =>
    exact CFSG.CGT.PushingUpLit.CGT6K1.inner_G2_fixed_root_exclusion hD hp2 hn K hK α hα hin S
      hSα hSn hSK
  case trialityD4 => exact triality_fixed_root_exclusion hD hn K hK α hα S hSα hSn hSK
  case twistedB2 =>
    rcases hD with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hSz⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact hp2 hSz.1
  all_goals first
    | exact absurd htc (by decide)
    | exact odd_residual_exceptional_fixed_root_exclusion (by decide) hD hp2 hn K hK α hα S hSα
        hSn hSK
    | exact ree_tits_fixed_root_exclusion hDs (by decide) hD hn K hK α hα S hSα hSn hSK

end CFSG.CGT.PushingUpLit.K1R
