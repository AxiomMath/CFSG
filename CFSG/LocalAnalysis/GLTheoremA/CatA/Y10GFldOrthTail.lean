module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

namespace FOB

theorem eq_of_component {T : Type} [Group T] [Finite T] {C J I : Subgroup T} {p : ℕ}
    (hJC : J ≤ C) [(J.subgroupOf C).Normal] (hsolv : Group.IsSolvable (↥C ⧸ J.subgroupOf C))
    (hJs : IsSimpleGroup ↥J) (hI : GLAPComponent p C I) : I = J := by
  have hIJ : I ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hJC
      hsolv hI.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hI)
  have hsn : CFSG.Open.IsSubnormal I J :=
    CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_le_of_le hI.2.1 hIJ hJC
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn hJs with h0 | h0
  · exact absurd h0 (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hI)
  · exact h0

end FOB

theorem pComponent_quotCenter_equiv {S : Type} [Group S] [Finite S] {K : Type} [Field K]
    [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
    {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ} (SS : SubfieldSetup k Q₀ Q σ p)
    (ψ : S ≃* matrixProjectiveDerived Q) {α : MulAut S}
    (hψ : MulAut.congr ψ α = fieldAutT Q σ SS.hQσ) {J : Subgroup S}
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* matrixProjectiveDerived Q₀) := by
  haveI : Finite (matrixProjectiveDerived Q) := Finite.of_equiv S ψ.toEquiv
  have hN : fixSubgroup (fieldAutT Q σ SS.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t =>
      CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup.trans (fieldAutT_apply_iff SS t)
  have hJ' : GLAPComponent p (subfieldFixedGroup k Q₀ Q) (J.map ψ.toMonoidHom) := by
    rw [← hN, ← hψ, ← Y10F.fixSubgroup_map_congr]
    exact (Y10F.glaPComponent_map_iff SS.hp ψ.injective).mpr hJ
  have hd : 0 < d := three_le_of_totallySingular k SS.hT₀
  haveI : IsSimpleGroup (matrixProjectiveDerived Q₀) :=
    (matrix_simple_nonabelian hd SS.hnd₀ SS.hT₀).1
  haveI := subfieldDerivedImage_normal k SS.hext
  have hsolv : Group.IsSolvable (↥(subfieldFixedGroup k Q₀ Q) ⧸
      (subfieldDerivedImage k SS.hext).subgroupOf (subfieldFixedGroup k Q₀ Q)) := by
    haveI := (fixedGroup_quotient_isPGroup k SS.hext SS.hnd₀ SS.hT₀).isNilpotent
    infer_instance
  have hEq : J.map ψ.toMonoidHom = subfieldDerivedImage k SS.hext :=
    FOB.eq_of_component (subfieldDerivedImage_le k SS.hext) hsolv
      (inclEquiv k SS.hext hd).symm.isSimpleGroup hJ'
  let e : ↥J ≃* matrixProjectiveDerived Q₀ :=
    ((Subgroup.equivMapOfInjective J ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hEq)).trans (inclEquiv k SS.hext hd).symm
  haveI : IsSimpleGroup ↥J := e.isSimpleGroup
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  exact Y10GInnLinFld.nonempty_quotCenter_equiv e

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth
