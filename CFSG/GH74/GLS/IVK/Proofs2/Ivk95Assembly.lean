module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Alt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Sp4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Exc
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Bender
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Abel
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Mathieu
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95M12
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95J2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95J3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95L3U3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95FamL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95FamL34
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95FamL4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95FamL5
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95FamMcL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95FamLy
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Ly
public import CFSG.GH74.Generic.BarSubnormal
public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.GH74.Generic.S1.KL3Red
public import CFSG.GH74.Generic.S1.TFrame
public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S1.TLeafBar
public import CFSG.GH74.Generic.S45.LEvSporFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.RankThree.PartOne.KS.Plane

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

theorem ivk95Leaves_of_unitary
    (hu4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
      Ivk95Empty (fun X _ => LieModel X .PSU 4 p f))
    (hu5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
      Ivk95Empty (fun X _ => LieModel X .PSU 5 p f)) : Ivk95Leaves := by
  exact
    { alt := ivk95_alt
      m11 := ivk95_m11
      m12 := ivk95_m12
      m22 := ivk95_m22
      m23 := ivk95_m23
      j1 := ivk95_j1
      j2 := ivk95_j2
      j3 := ivk95_j3
      mcl := ivk95_mcl
      ly := ivk95_ly
      l2 := ivk95_l2
      l3 := ivk95_l3
      u3 := ivk95_u3
      sp4 := ivk95_sp4
      g2 := ivk95_g2
      d4 := ivk95_d4
      l4 := ivk95_l4
      u4 := hu4
      l5 := ivk95_l5
      u5 := hu5
      ree := ivk95_ree
      l28 := ivk95_l28
      l216 := ivk95_l216
      l34 := ivk95_l34
      u34 := ivk95_u34
      sz8 := ivk95_sz8 }

end CFSG.GH74.GLS.IVK.Proofs2
