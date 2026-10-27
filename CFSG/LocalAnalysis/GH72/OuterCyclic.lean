module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Certificates.Data.A5

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.GorensteinWalter (HasDihedralSylowTwo PSL2 PGL2)

theorem outer_alternatingGroup_seven_mul_self (x : Outer (alternatingGroup (Fin 7))) :
    x * x = 1 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨s, rfl⟩ := hbij.2 σ
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  have hc : s * s ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Int.units_mul_self]
  refine ⟨⟨_, hc⟩, ?_⟩
  rw [← MulAut.conjNormal_val (h := ⟨_, hc⟩)]
  simp only [map_mul]

end CFSG.GH72
