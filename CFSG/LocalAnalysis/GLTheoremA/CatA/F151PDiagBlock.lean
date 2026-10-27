module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

private theorem fixSubgroup_conj_eq_centralizer {R : Type} [Group R] (x : R) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set R) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

theorem diagOfBlock_holds :
    DiagOfBlock := by
  intro R _ _ p hp hp2 hlayer hchev hB
  intro x y hx hxp hyp hcomm J hJ hN
  have hfix : fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set R) :=
    fixSubgroup_conj_eq_centralizer x
  have hJfix : J ≤ fixSubgroup (MulAut.conj x) := by
    rw [hfix]
    exact hJ.1
  have hJperf : ⁅J, J⁆ = J :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle : J ≤ GLALayer (fixSubgroup (MulAut.conj x)) :=
    hlayer x hx hxp J hJfix hJperf
  have hJcompFix : GLAPComponent p (fixSubgroup (MulAut.conj x)) J := by
    rw [hfix]
    exact hJ
  obtain ⟨hJcompO, -⟩ := glaPComponent_isComponent_of_le_layer hJcompFix hJle
  have hJcomp : CFSG.Assembly.IsComponentOf J (fixSubgroup (MulAut.conj x)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open J _).2 hJcompO
  have hq : CFSG.IsQuasisimple (PQuot p J) := by
    rw [← CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native]
    exact CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hchevJ : IsChevSimple 2 (PSimple p J) := hchev x hx hxp J hJ
  rcases hB x y hxp hyp hcomm hx J hJcomp hN with ⟨hcat, hmem⟩ | ⟨hcat, hmem⟩ | hmem
  · exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_linear
      p J y hN hp hq hcat hmem
  · exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_unitary
      p J y hN hp hq hcat hmem
  · exact CFSG.LocalAnalysis.GLTheoremA.MI.inner_innDiag_holds hp hJ hchevJ hN
      ((CFSG.LocalAnalysis.GLTheoremA.MI.indAut_mem_inner_iff hp hJ hN).1 hmem)


end CFSG.LocalAnalysis.GLTheoremA.F151

end
