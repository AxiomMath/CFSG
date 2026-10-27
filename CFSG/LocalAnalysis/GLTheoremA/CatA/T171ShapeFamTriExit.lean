module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Model
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)


theorem innDiagOn_of_triModel
    (hC : TriCompClassical) (hA : TriCompAction)
    {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
    (hS : Setup p L J A d b) (hM : TriModelData p L J d b) :
    InnDiagOn p (Subgroup.zpowers b) J := by
  obtain ⟨f, K, hKf, hKfin, σ, θ, x, w, hdata, hxind, hwind, hxp, hx1, hxw, hcomp⟩ := hM
  letI := hKf
  letI := hKfin
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  let J' : Subgroup (TriGrp K σ) := (J.subgroupOf L).map (piCenterQuot θ)
  have hwstab : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut J' :=
    conj_mem_subgroupStabAut hS hbN θ hwind
  obtain ⟨t, ν, g, ht, hν, hmodel⟩ :=
    hC f K σ hdata p hS.prime hS.odd x hxp hx1 J' hcomp
  have hact := hA f K σ hdata p hS.prime hS.odd x w hxp hx1 hxw J' hcomp hwstab
  obtain ⟨e, he⟩ := exists_indAut_eq_centerQuotient hS θ w hwind hwstab
  have hmem : MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e).1
      (he ▸ hact)
  have hmodel' : StatedClassicalModel (PSimple p J) t ν 2 g :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmodel
  have hLM : CFSG.Blueprint.LieModel (PSimple p J) t ν 2 g :=
    Or.inl ⟨by rcases ht with rfl | rfl <;> decide, hmodel'⟩
  have hqJ : CFSG.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open
      (isQuasisimple_pQuot_of_glaPComponent hS.prime hS.pcomp)
  exact innDiagOn_of_lieModel hS.b_norm hqJ hLM
    (by rintro ⟨h1, -⟩; rcases ht with rfl | rfl <;> exact absurd h1 (by decide))
    (by rcases ht with rfl | rfl <;> decide) hmem

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
