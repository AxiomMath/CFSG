module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscT7K5
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32
public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

namespace AlphaFr.E2

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem linkGen_of_mul_mem_center {v : Y} (h : t * v ∈ Subgroup.center Y) :
    Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.centralizer ({v} : Set Y) ⊔
      Subgroup.centralizer ({t * v} : Set Y) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  refine Subgroup.mem_sup_right ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_center_iff.mp h y

end AlphaFr.E2

end CFSG.ClassicalInvolution.Q3.TL4
