module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmCases
import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
import CFSG.HardMathSupport.Dickson.BMRows.CensusShape
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeIndAutInv
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockProofFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockResidual
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.RankThree.Classical2 CFSG.SeitzReduction.OmegaPilot
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def OrthComponentBlockAnalysisMinus : Prop :=
  ∀ {m n p : ℕ} {K : Type} [Field K] [Finite K] (b₀ c₀ : K),
    Nat.card K = 2 ^ n → 4 ≤ m → (∀ s : K, s ^ 2 + b₀ * s + c₀ ≠ 0) → p.Prime → p ≠ 2 →
    ∀ (x y : ProjOrthDerived (quadMinus m K b₀ c₀)), x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ≠ 1 →
    ∀ J : Subgroup (ProjOrthDerived (quadMinus m K b₀ c₀)),
      CFSG.Assembly.IsComponentOf J
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) →
      (hN : y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived (quadMinus m K b₀ c₀)))) →
      (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
          CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ∈
            innAutDerived (PSimple p J)) ∨
        (catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) ∧
          CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ∈
            innAutDerived (PSimple p J)) ∨
        CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

theorem orthCompMatrixAnalysisMinus_of (hD : ComponentDescentIndAut)
    (hU : UnitaryBlockInnAutDerived) (hM : OrthComponentBlockAnalysisMinus) :
    OrthCompMatrixAnalysisMinus := by
  intro G _ _ p L J A d b m n K _ _ b₀ c₀ x y θ hS hKcard hm4 hbc hx hy hxp hyp hxy hbz hbJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hKcard
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hx1 : x ≠ 1 := by
    rintro rfl
    have hx' : LargeEvenInduces θ (conjRel d)
        (1 : MulAut (ProjOrthDerived (quadMinus m K b₀ c₀))) := by
      simpa using hx
    have hcen : d ∈ Subgroup.centralizer (L : Set G) :=
      centralizes_of_conjRel_center hdN
        (exists_center_of_largeEvenInduces_one hdN hx') ⟨hS.qs.1⟩
    have hdinf : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hcen⟩
    rw [hS.faithful] at hdinf
    exact hS.d_ne (Subgroup.mem_bot.mp hdinf)
  set Jbar : Subgroup (ProjOrthDerived (quadMinus m K b₀ c₀)) :=
    (J.subgroupOf L).map (piCenterQuot θ) with hJbar
  have hcompJbar : CFSG.Assembly.IsComponentOf Jbar
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) :=
    componentDescent_component θ hdN (φ := MulAut.conj x) hx
      ((CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1)
  have hN : y ∈ Subgroup.normalizer (Jbar : Set (ProjOrthDerived (quadMinus m K b₀ c₀))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : Jbar.map (MulAut.conj y) ≤ Jbar := by
      rintro z ⟨w, hw, rfl⟩
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hw
      have hlJ : (l : G) ∈ J := Subgroup.mem_subgroupOf.mp hl
      have hconjJ : b⁻¹ * (l : G) * b ∈ J := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ hS.b_norm) (l : G)).mp hlJ
        simpa using h
      have hconjL : b⁻¹ * (l : G) * b ∈ L := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ hbN) (l : G)).mp l.2
        simpa using h
      refine Subgroup.mem_map.mpr ⟨⟨b⁻¹ * (l : G) * b, hconjL⟩,
        Subgroup.mem_subgroupOf.mpr hconjJ, ?_⟩
      exact (hy l ⟨b⁻¹ * (l : G) * b, hconjL⟩ rfl).symm
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective
      (f := (MulAut.conj y : ProjOrthDerived (quadMinus m K b₀ c₀) →*
        ProjOrthDerived (quadMinus m K b₀ c₀))) (MulAut.conj y).injective]
  obtain ⟨e, he⟩ := hD (p := p) (L := L) (J := J) (A := A) (d := d) (b := b)
    (R := ProjOrthDerived (quadMinus m K b₀ c₀)) θ y hS hy hN
  obtain ⟨htype, hmem⟩ | ⟨htype, hmem⟩ | hinner :=
    hM b₀ c₀ hKcard hm4 hbc hS.prime hS.odd x y hxp hyp hxy hx1 Jbar hcompJbar hN
  · left
    refine ⟨CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ e.symm htype, ?_⟩
    have hmem' : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar y⁻¹
        (Subgroup.inv_mem _ hN) ∈ innAutDerived (PSimple p Jbar) := by
      rw [indAut_inv (p := p) (L := Jbar) (g := y) hN]
      exact Subgroup.inv_mem _ hmem
    rw [← he] at hmem'
    exact (mem_innAutDerived_congr e).mp hmem'
  · right; left
    refine ⟨CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ e.symm htype, ?_⟩
    have hmem' : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar y⁻¹
        (Subgroup.inv_mem _ hN) ∈ innAutDerived (PSimple p Jbar) := by
      rw [indAut_inv (p := p) (L := Jbar) (g := y) hN]
      exact Subgroup.inv_mem _ hmem
    rw [← he] at hmem'
    exact (mem_innAutDerived_congr e).mp hmem'
  · right; right
    have hmem' : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar y⁻¹
        (Subgroup.inv_mem _ hN) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p Jbar) := by
      rw [indAut_inv (p := p) (L := Jbar) (g := y) hN]
      exact Subgroup.inv_mem _ hinner
    have hinner' : MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b
        hS.b_norm) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p Jbar) := by
      rw [he]
      exact hmem'
    have hinnerJ : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J) :=
      (congr_mem_inner_iff e _).mp hinner'
    exact (CFSG.LocalAnalysis.GLTheoremA.MI.indAut_mem_inner_iff hS.prime hS.pcomp
      hS.b_norm).mp hinnerJ

theorem orthComponentBlockAnalysisMinus_of_generic
    (hgen : ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b₀ c₀ : K), 4 ≤ m →
      (∀ s : K, s ^ 2 + b₀ * s + c₀ ≠ 0) →
      OrthComponentBlockAnalysis (quadMinus m K b₀ c₀)) :
    OrthComponentBlockAnalysisMinus := by
  intro m n p K _ _ b₀ c₀ hKcard hm4 hbc hp hp2 x y hxp hyp hxy hx1 J hcomp hN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hKcard
  have hm1' : 0 < m - 1 := by omega
  have hQ : (QuadraticMap.polarBilin (quadMinus m K b₀ c₀)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hbc
  have hQne : ∃ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      quadMinus m K b₀ c₀ v ≠ 0 := by
    by_contra h
    push Not at h
    have hv : (Pi.single (Sum.inl ⟨0, hm1'⟩) (1 : K) :
        Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ≠ 0 := by
      intro h0
      have := congrFun h0 (Sum.inl ⟨0, hm1'⟩)
      simpa using this
    refine hv (hQ.1 _ fun w => ?_)
    simp [QuadraticMap.polar, h]
  set sigma := CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv hQne with hsigma
  set xt := sigma x with hxtdef
  set yt := sigma y with hytdef
  let xtL : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := xt.1
  let ytL : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := yt.1
  have hpiY : piOrth (quadMinus m K b₀ c₀) yt = y := piOrth_orthProjEquiv hQne y
  have hxt1 : xt ≠ 1 := by
    intro h
    have h' : sigma x = 1 := h
    exact hx1 (sigma.injective (by rw [h', map_one]))
  have hxtp : xt ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hytp : yt ^ p = 1 := by rw [← map_pow, hyp, map_one]
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hpl : p ≠ ringChar K := by rw [hring]; exact hp2
  have hxtord : orderOf xt = p := orderOf_eq_prime hxtp hxt1
  have hxodd : OddOrderIsometry (quadMinus m K b₀ c₀) p xtL :=
    oddOrderIsometry_of_orthDerived hp hpl hQ xt hxtord
  have hcomm : xt * yt = yt * xt := by
    have h := congrArg sigma hxy
    simpa using h
  have hcommL : xtL * ytL = ytL * xtL := by
    simpa [xtL, ytL] using congrArg (fun e : ↥(orthDerived (quadMinus m K b₀ c₀)) => e.1) hcomm
  have hyc : ytL ∈ isometryCentralizer (quadMinus m K b₀ c₀) xtL := by
    refine mem_isometryCentralizer.mpr ⟨?_, ?_⟩
    · intro v
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup yt.2) v
    · intro v
      have h := congrArg (fun e : ↥(orthDerived (quadMinus m K b₀ c₀)) => e.1 v) hcomm
      simpa [xtL, ytL, LinearEquiv.mul_apply] using h.symm
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      CFSG.RankThree.PartOne.KCOrthogonal.centralizerImage (quadMinus m K b₀ c₀) xtL :=
    fixSubgroup_conj_eq_centralizerImage hQne x
  have hcomp' : CFSG.Assembly.IsComponentOf J
      (CFSG.RankThree.PartOne.KCOrthogonal.centralizerImage (quadMinus m K b₀ c₀) xtL) := by
    rw [← hfix]
    exact hcomp
  have hN' : piOrth (quadMinus m K b₀ c₀) yt ∈
      Subgroup.normalizer (J : Set (ProjOrthDerived (quadMinus m K b₀ c₀))) := by
    rw [hpiY]
    exact hN
  unfold OrthComponentBlockAnalysis at hgen
  have hres := hgen m K b₀ c₀ hm4 hbc hp hp2 xt yt hxodd hyc hytp hxt1 J hcomp' hN'
  have heq : MI.indAut p J (piOrth (quadMinus m K b₀ c₀) yt) hN' = MI.indAut p J y hN :=
    CFSG.LocalAnalysis.GLTheoremA.T156.indAut_congr hpiY hN' hN
  rw [heq] at hres
  exact hres

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
