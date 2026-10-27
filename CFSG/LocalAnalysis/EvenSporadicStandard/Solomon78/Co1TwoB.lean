module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1TwoBInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOnePerfectMat
public import Certificates.Certificate25170
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Closing
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneA
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneC
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Co1Block.TwoBCent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.TwoCo1.HypOne
open scoped commutatorElement

local notation "RowsT" => CFSG.Sporadic.Co1Schreier.Native.Rows
local notation "rmul" => CFSG.Sporadic.Co1Schreier.Native.mul
local notation "rone" => CFSG.Sporadic.Co1Schreier.Native.one
local notation "raR" => CFSG.Sporadic.Co1Schreier.Native.aR

theorem twoBCommOf_flag {D₃ : List RowsT × List RowsT × Bool}
    (h : twoBCommOf D₃ = true) : D₃.2.2 = true := by
  simp only [twoBCommOf, Bool.and_eq_true] at h
  exact h.1.1.1

theorem commute_of_rows {D₃ : List RowsT × List RowsT × Bool}
    {DG : List GL24} (hrep : List.Forall₂ MRep D₃.1 DG) (k : ℕ)
    (hk : rmul (D₃.1.getD k rone) raR =
      rmul raR (D₃.1.getD k rone)) :
    DG.getD k 1 * A₁ = A₁ * DG.getD k 1 := by
  have hx := getD_rep hrep MRep.one k
  exact MRep.eq_of_eq (hx.mul rep_A₁) (rep_A₁.mul hx) hk

theorem commutator_of_rows
    {D₃ : List RowsT × List RowsT × Bool} {DG : List GL24}
    (hrep : List.Forall₂ MRep D₃.1 DG) (i j : ℕ)
    (h : rmul (D₃.1.getD i rone) (D₃.1.getD j rone) =
      rmul raR (rmul (D₃.1.getD j rone) (D₃.1.getD i rone))) :
    DG.getD i 1 * DG.getD j 1 = A₁ * (DG.getD j 1 * DG.getD i 1) := by
  have hx := getD_rep hrep MRep.one i
  have hy := getD_rep hrep MRep.one j
  exact MRep.eq_of_eq (hx.mul hy) (rep_A₁.mul (hy.mul hx)) h

theorem twoBCommOf_x
    {D₃ : List RowsT × List RowsT × Bool}
    {DG : List GL24} (hrep : List.Forall₂ MRep D₃.1 DG) (h : twoBCommOf D₃ = true) :
    DG.getD 4 1 * A₁ = A₁ * DG.getD 4 1 := by
  simp only [twoBCommOf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hxc⟩, hyc⟩, hxy⟩ := h
  exact commute_of_rows hrep 4 hxc

theorem twoBCommOf_y
    {D₃ : List RowsT × List RowsT × Bool}
    {DG : List GL24} (hrep : List.Forall₂ MRep D₃.1 DG) (h : twoBCommOf D₃ = true) :
    DG.getD 5 1 * A₁ = A₁ * DG.getD 5 1 := by
  simp only [twoBCommOf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hxc⟩, hyc⟩, hxy⟩ := h
  exact commute_of_rows hrep 5 hyc

theorem twoBCommOf_xy
    {D₃ : List RowsT × List RowsT × Bool}
    {DG : List GL24} (hrep : List.Forall₂ MRep D₃.1 DG) (h : twoBCommOf D₃ = true) :
    DG.getD 4 1 * DG.getD 5 1 = A₁ * (DG.getD 5 1 * DG.getD 4 1) := by
  simp only [twoBCommOf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hxc⟩, hyc⟩, hxy⟩ := h
  exact commutator_of_rows hrep 4 5 hxy

theorem comm_pair_of_entries {DG : List GL24} (hDG : ∀ g ∈ DG, g ∈ GA) {a : GA}
    (ha : (a : GL24) = A₁)
    (e1 : DG.getD 4 1 * A₁ = A₁ * DG.getD 4 1) (e2 : DG.getD 5 1 * A₁ = A₁ * DG.getD 5 1)
    (e3 : DG.getD 4 1 * DG.getD 5 1 = A₁ * (DG.getD 5 1 * DG.getD 4 1)) :
    ∃ x y : GA, x * a = a * x ∧ y * a = a * y ∧ x * y = a * y * x := by
  refine ⟨⟨DG.getD 4 1, getD_mem_of_forall hDG 4⟩, ⟨DG.getD 5 1, getD_mem_of_forall hDG 5⟩,
    Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, ha]
    exact e1
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, ha]
    exact e2
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, ha, mul_assoc]
    exact e3

theorem exists_comm_pair_twoB :
    ∃ x y : GA, x * a₁ = a₁ * x ∧ y * a₁ = a₁ * y ∧ x * y = a₁ * y * x := by
  have h := Certificates.certificate25170
  simp only [twoBCommCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hD1, hD2⟩, hOf⟩ := h
  have hrepB := rep_brayElts (bidx := twoBBray) rep_A₁ hD1
  have hBG : ∀ g ∈ brayEltsG A₁ twoBD1 twoBBray, g ∈ GA := brayElts_mem_GA A₁_mem
  have hrepD2 := dag_rep hrepB sylD2B hD2
  have hD2G : ∀ g ∈ dagG (brayEltsG A₁ twoBD1 twoBBray) sylD2B, g ∈ GA := dagG_mem hBG sylD2B
  have hrepS := rep_pickRows hrepD2 sylIdxB
  have hSG : ∀ g ∈ sylIdxB.map (fun j => (dagG (brayEltsG A₁ twoBD1 twoBBray) sylD2B).getD j 1),
      g ∈ GA := by
    intro g hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact getD_mem_of_forall hD2G j
  have hrepD3 := dag_rep hrepS [twoBCommWX, twoBCommWY] (twoBCommOf_flag hOf)
  exact comm_pair_of_entries (dagG_mem hSG [twoBCommWX, twoBCommWY]) coe_a₁
    (twoBCommOf_x hrepD3 hOf) (twoBCommOf_y hrepD3 hOf) (twoBCommOf_xy hrepD3 hOf)

theorem mem_commutator_of_comm_pair {a : GA}
    (h : ∃ x y : GA, x * a = a * x ∧ y * a = a * y ∧ x * y = a * y * x) :
    a ∈ ⁅Subgroup.centralizer ({a} : Set GA), Subgroup.centralizer ({a} : Set GA)⁆ := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  have hxC : x ∈ Subgroup.centralizer ({a} : Set GA) :=
    Subgroup.mem_centralizer_singleton_iff.2 hx
  have hyC : y ∈ Subgroup.centralizer ({a} : Set GA) :=
    Subgroup.mem_centralizer_singleton_iff.2 hy
  have h := Subgroup.commutator_mem_commutator hxC hyC
  have e : ⁅x, y⁆ = a := by
    rw [commutatorElement_def]
    calc x * y * x⁻¹ * y⁻¹ = a * y * x * x⁻¹ * y⁻¹ := by rw [hxy]
      _ = a := by group
  rwa [e] at h

theorem a₁_mem_commutator :
    a₁ ∈ ⁅Subgroup.centralizer ({a₁} : Set GA), Subgroup.centralizer ({a₁} : Set GA)⁆ :=
  mem_commutator_of_comm_pair exists_comm_pair_twoB

end CFSG.EvenSporadicStandard.Solomon78
