module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDispatch
public import CFSG.ClassicalInvolution.Q3.TA3SOLRee
public import CFSG.ClassicalInvolution.Q3.TA3SOLG2D4
public import CFSG.ClassicalInvolution.Q3.TA3SOLMember3
public import CFSG.GH74.Generic.S1.Exo.Q3HNoQ8L2

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem noDatumL2 : NoDatumL2 := by
  intro X _ _ p f hp2 h ⟨R, S, t, hD⟩
  obtain ⟨φ, hφ, -, -⟩ := datum_exists_q8 hD
  exact GH74.Generic.S1.Exo.no_q8_of_psl2_model h.1.1 hp2 h φ hφ

theorem smallOddLieTightMemberS_of_packages (hL3U3 : NoDatumL3U3) (hSp4 : NoDatumSp4)
    (hL4U4 : NoDatumL4U4) (hL5U5 : NoDatumL5U5) : SmallOddLieTightMemberS :=
  smallOddLieTightMemberS_of_parts noDatumL2 noDatumRee noDatumG2D4 member3Three hL3U3 hSp4 hL4U4
    hL5U5

end CFSG.ClassicalInvolution.Q3.TA3
