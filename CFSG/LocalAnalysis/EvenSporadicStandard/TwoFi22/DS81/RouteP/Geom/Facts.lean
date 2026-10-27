module

public import Certificates.Certificate450230
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Elements

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native

structure GeomFacts (gs objs ms : Array Table) (trees : Array CFSG.Perm.Native.Tree)
    (lab : Table) (words : Array (List Int)) (atree : CFSG.Perm.Native.Tree) : Prop where
  words_size : words.size = 7
  trees_ok : zpTreesOK gs trees = true
  lab_ok : labOK gs trees lab = true
  dist_ok : distOK lab (repTabs ms words) trees[1]!.pts = true
  s1_ok : s1OK objs trees atree = true

theorem GeomFacts.of_geomOKAt {gs objs ms : Array Table} {trees : Array CFSG.Perm.Native.Tree}
    {lab : Table} {words : Array (List Int)} {atree : CFSG.Perm.Native.Tree}
    (h : geomOKAt gs objs ms trees lab words atree = true) :
    GeomFacts gs objs ms trees lab words atree := by
  unfold geomOKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem geomOK_eq_true : geomOK () = true :=
  Certificates.certificate450230

@[irreducible] def gTrees : Array CFSG.Perm.Native.Tree := geomTrees (genTabs ())

@[irreducible] def gLab : Table := geomLab gTrees

@[irreducible] def gWords : Array (List Int) := geomWords (mTabs ())

@[irreducible] def gA1Tree : CFSG.Perm.Native.Tree :=
  CFSG.Perm.Native.treeBFS degree 99705 objTabs geomA1Letters

theorem geomFacts :
    GeomFacts (genTabs ()) objTabs (mTabs ()) gTrees gLab gWords gA1Tree := by
  unfold gA1Tree gWords gLab gTrees
  exact GeomFacts.of_geomOKAt geomOK_eq_true

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
