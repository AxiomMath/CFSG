
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WClassSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassFacts
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

local notation "𝒞" => CFSG.Sporadic.SmallOddCore.conjClass

theorem notMem_of_memT_false {S : Set (Equiv.Perm (Fin 1408))} {E : Array Table}
    (hE : IsEnumSet 1408 E S) {x : Table} {g : Equiv.Perm (Fin 1408)} (hx : Rep 1408 x g)
    (h : memT 1408 E x = false) : g ∉ S := fun hg => by
  have := (hE.memT_iff hx).2 hg
  rw [h] at this
  exact Bool.false_ne_true this

theorem ne_of_tblEq_false {x y : Table} {g g' : Equiv.Perm (Fin 1408)}
    (hx : Rep 1408 x g) (hy : Rep 1408 y g') (h : tblEq 1408 x y = false) : g ≠ g' :=
  fun hg => by
    have := (tblEq_iff_eq hx hy).2 hg
    rw [h] at this
    exact Bool.false_ne_true this

section Cert

end Cert

end CFSG.EvenSporadicStandard.HNRecog
