module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockResidual
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
import CFSG.HardMathSupport.Dickson.BMRows.CensusShape
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeIndAutInv
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
open CFSG.ComponentClassification.PresentationLocal
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def SympComponentBlockAnalysis : Prop :=
  ∀ {m n p : ℕ} {K : Type} [Field K] [Finite K],
    Nat.card K = 2 ^ n → 2 ≤ m → p.Prime → p ≠ 2 →
    ∀ (x y : StatedSp m K), x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ≠ 1 →
    ∀ J : Subgroup (StatedProj (StatedSp m K)),
      CFSG.Assembly.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x))) →
      (hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))) →
      (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
          CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J (proj m K y) hN ∈
            innAutDerived (PSimple p J)) ∨
        (catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) ∧
          CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J (proj m K y) hN ∈
            innAutDerived (PSimple p J)) ∨
        CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J (proj m K y) hN ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

theorem sympCompMatrixAnalysis_of (hD : SympComponentDescent)
    (hU : UnitaryBlockInnAutDerived) (hM : SympComponentBlockAnalysis) :
    SympCompMatrixAnalysis := by
  intro G _ _ p L J A d b m n K _ _ x y θ hS hKcard hm2 hx hy hxp hyp hxy hbz hbJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hKcard
  haveI : NeZero m := ⟨by omega⟩
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hx1 : x ≠ 1 := by
    rintro rfl
    have hx0 : LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d)
        (MulAut.conj (proj m K (1 : StatedSp m K))) := hx
    have hx' : LargeEvenInduces θ (conjRel d)
        (1 : MulAut (StatedProj (StatedSp m K))) := by
      have h : LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) 1 := by
        simpa using hx0
      exact h
    have hcen : d ∈ Subgroup.centralizer (L : Set G) :=
      centralizes_of_conjRel_center hdN
        (exists_center_of_largeEvenInduces_one hdN hx') ⟨hS.qs.1⟩
    have hdinf : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hcen⟩
    rw [hS.faithful] at hdinf
    exact hS.d_ne (Subgroup.mem_bot.mp hdinf)
  set Jbar : Subgroup (StatedProj (StatedSp m K)) :=
    (J.subgroupOf L).map (piCenterQuot θ) with hJbar
  have hcompJbar : CFSG.Assembly.IsComponentOf Jbar
      (fixSubgroup (MulAut.conj (proj m K x))) := by
    have h := componentDescent_component θ hdN (φ := MulAut.conj (proj m K x))
      hx
      ((CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1)
    exact h
  have hN : proj m K y ∈ Subgroup.normalizer (Jbar : Set (StatedProj (StatedSp m K))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : Jbar.map (MulAut.conj (proj m K y)) ≤ Jbar := by
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
      (f := (MulAut.conj (proj m K y) : StatedProj (StatedSp m K) →*
        StatedProj (StatedSp m K))) (MulAut.conj (proj m K y)).injective]
  obtain ⟨e, he⟩ := hD (p := p) (L := L) (J := J) (A := A) (d := d) (b := b) (m := m)
    (n := n) (K := K) (x := x) (y := y) θ hS hx hy hN
  obtain ⟨htype, hmem⟩ | ⟨htype, hmem⟩ | hinner :=
    hM hKcard hm2 hS.prime hS.odd x y hxp hyp hxy hx1 Jbar hcompJbar hN
  · left
    refine ⟨CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ e.symm htype, ?_⟩
    have hmem' : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar (proj m K y)⁻¹
        (Subgroup.inv_mem _ hN) ∈ innAutDerived (PSimple p Jbar) := by
      rw [indAut_inv (p := p) (L := Jbar) (g := proj m K y) hN]
      exact Subgroup.inv_mem _ hmem
    rw [← he] at hmem'
    exact (mem_innAutDerived_congr e).mp hmem'
  · right; left
    refine ⟨CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ e.symm htype, ?_⟩
    have hmem' : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar (proj m K y)⁻¹
        (Subgroup.inv_mem _ hN) ∈ innAutDerived (PSimple p Jbar) := by
      rw [indAut_inv (p := p) (L := Jbar) (g := proj m K y) hN]
      exact Subgroup.inv_mem _ hmem
    rw [← he] at hmem'
    exact (mem_innAutDerived_congr e).mp hmem'
  · right; right
    have hmem' : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar (proj m K y)⁻¹
        (Subgroup.inv_mem _ hN) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p Jbar) := by
      rw [indAut_inv (p := p) (L := Jbar) (g := proj m K y) hN]
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

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
