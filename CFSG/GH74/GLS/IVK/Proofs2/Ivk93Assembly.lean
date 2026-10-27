module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Alt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Sp4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Exc
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Bender
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Ree
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Mathieu
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93J1
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93J2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93J3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L34
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93McL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Ly
public import CFSG.GH74.GLS.SP.Consistency
public import CFSG.GH74.GLS.SP.Generic
public import CFSG.GH74.GLS.Stage2.Final.ModelIVKGen
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMain
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.Generic.BarSubnormal
public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.GH74.Generic.S1.KL3Red
public import CFSG.GH74.Generic.S1.TFrame
public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S1.TLeafBar
public import CFSG.GH74.Generic.S45.LEvSporFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.RankThree.PartOne.KS.Plane

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

theorem ivk93Leaves_of_four
    (hl4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
      Ivk93Eq (fun X _ => LieModel X .PSL 4 p f) (p ^ f))
    (hu4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
      Ivk93Eq (fun X _ => LieModel X .PSU 4 p f) (p ^ f))
    (hl5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
      Ivk93Empty (fun X _ => LieModel X .PSL 5 p f))
    (hu5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
      Ivk93Empty (fun X _ => LieModel X .PSU 5 p f)) : Ivk93Leaves := by
  exact
    { alt := ivk93_alt
      m11 := ivk93_m11
      m12 := ivk93_m12
      m22 := ivk93_m22
      m23 := ivk93_m23
      j1 := ivk93_j1
      j2 := ivk93_j2
      j3 := ivk93_j3
      mcl := ivk93_mcl
      ly := ivk93_ly
      l2 := ivk93_l2
      l3 := ivk93_l3
      u3 := ivk93_u3
      sp4 := ivk93_sp4
      g2 := ivk93_g2
      d4 := ivk93_d4
      l4 := hl4
      u4 := hu4
      l5 := hl5
      u5 := hu5
      ree := ivk93_ree
      l28 := ivk93_l28
      l216 := ivk93_l216
      l34 := ivk93_l34
      u34 := ivk93_u34
      sz8 := ivk93_sz8 }

end CFSG.GH74.GLS.IVK.Proofs2
