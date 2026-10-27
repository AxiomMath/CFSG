module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.ClassicalInvolution.SmallCases.SectionalFourBranch

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint.NativeSporadic

theorem noNonsolvableClassical_Ly : NoNonsolvableClassical (Carrier .Ly) :=
  LyProof.noNonsolvableClassical_Ly_centralizer

theorem noNonsolvableClassical_of_sporadic_models {G : Type} [Group G]
    (h : IsSporadic G .M12 ∨ IsSporadic G .M22 ∨ IsSporadic G .M23 ∨ IsSporadic G .J1 ∨
      IsSporadic G .J2 ∨ IsSporadic G .J3 ∨ IsSporadic G .McL ∨ IsSporadic G .Ly) :
    NoNonsolvableClassical G :=
  noNonsolvableClassical_of_gh74_models noNonsolvableClassical_Ly h

theorem citSectionalFour_of_gh74_models (hGH : GH74SectionalModels) :
    CFSG.ClassicalInvolution.CITSectionalFour :=
  citSectionalFour_of_gh74 noNonsolvableClassical_Ly hGH

end CFSG.ClassicalInvolution
