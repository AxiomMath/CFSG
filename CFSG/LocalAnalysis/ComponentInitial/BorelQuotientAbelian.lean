module

public import CFSG.GroupTheory.NormalizerQuotientOddCover
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
import CFSG.Quasithin.SteinbergBIEvenLinearThreeThreeSylowAction
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open TauCeti.Subgroup (normalizerQuotient)
open scoped commutatorElement

theorem isMulCommutative_normalizerQuotient_projUnitriangular {n : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hn : 1 ≤ n) :
    IsMulCommutative
      (normalizerQuotient
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular n K)) := by
  have hN : Subgroup.normalizer
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular n K :
        Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUpperTriangular n K :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.normalizer_projUnitriangular
      (K := K) (n := n) 2
  refine CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_borel hN ?_
  intro x hx y hy
  obtain ⟨bx, hbx, hxb⟩ := Subgroup.mem_map.mp hx
  obtain ⟨cy, hcy, hyc⟩ := Subgroup.mem_map.mp hy
  have hcomm : ⁅bx, cy⁆ ∈
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n K := by
    have h := CFSG.Quasithin.SteinbergBI.commutator_mem_unitriangular hbx hcy
    simpa [commutatorElement_def] using h
  have hmem : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K ⁅bx, cy⁆ ∈
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular n K :=
    Subgroup.mem_map.mpr ⟨⁅bx, cy⁆, hcomm, rfl⟩
  have hcoe : ⁅x, y⁆ = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K ⁅bx, cy⁆ := by
    rw [← hxb, ← hyc]
    rw [← map_commutatorElement (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K) bx cy]
  rwa [hcoe]

theorem isMulCommutative_normalizerQuotient_hypProjUnitriangular {p f : ℕ} {K : Type}
    [Field K] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K) {r ε : ℕ}
    (hr : 1 ≤ r) (hε : ε ≤ 1) :
    IsMulCommutative
      (normalizerQuotient (CFSG.ClassicalGroups.UnitaryFlag.hypProjUnitriangular h r ε)) := by
  have hN : Subgroup.normalizer
      (CFSG.ClassicalGroups.UnitaryFlag.hypProjUnitriangular h r ε :
        Set (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h r ε)) =
      CFSG.ClassicalGroups.UnitaryFlag.hypProjBorel h r ε :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypProjUnitriangular h hr hε
  refine CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_borel hN ?_
  intro x hx y hy
  obtain ⟨bx, hbx, hxb⟩ := Subgroup.mem_map.mp hx
  obtain ⟨cy, hcy, hyc⟩ := Subgroup.mem_map.mp hy
  have hcomm : ⁅bx, cy⁆ ∈
      CFSG.ClassicalGroups.UnitaryFlag.hypUnitriangular h r ε :=
    CFSG.GroupTheory.commutator_mem_of_diag_ker
      (CFSG.ClassicalGroups.UnitaryFlag.hypDiagHom h r ε hε)
      (CFSG.ClassicalGroups.UnitaryFlag.ker_hypDiagHom hε) hbx hcy
  have hmem : CFSG.ClassicalGroups.UnitaryFlag.hypProj h r ε ⁅bx, cy⁆ ∈
      CFSG.ClassicalGroups.UnitaryFlag.hypProjUnitriangular h r ε :=
    Subgroup.mem_map.mpr ⟨⁅bx, cy⁆, hcomm, rfl⟩
  have hcoe : ⁅x, y⁆ =
      CFSG.ClassicalGroups.UnitaryFlag.hypProj h r ε ⁅bx, cy⁆ := by
    rw [← hxb, ← hyc]
    rw [← map_commutatorElement (CFSG.ClassicalGroups.UnitaryFlag.hypProj h r ε) bx cy]
  rwa [hcoe]

end CFSG.LocalAnalysis.ComponentInitial
