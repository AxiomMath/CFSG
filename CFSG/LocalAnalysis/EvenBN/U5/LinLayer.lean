module

public import CFSG.LocalAnalysis.EvenBN.U5.LinRadicalsGen
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightD
public import CFSG.LocalAnalysis.EvenBN.U5.LinParts

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

section Layer

variable (hl : d.LinCtx)
include hl

theorem lin_layer_facts :
    IsSimpleGroup (CFSG.layer (d.s38dH ⧸ d.s38dO)) ∧
      LieModel (CFSG.layer (d.s38dH ⧸ d.s38dO)) .PSL 3 2 (2 * f) ∧
      (d.M₂.subgroupOf d.s38dH).map d.s38dθ = CFSG.layer (d.s38dH ⧸ d.s38dO) := by
  obtain ⟨hout, hM⟩ := hl.hyp.sec3_3_two hl.gms
  have hs : IsSimpleGroup (CFSG.layer (d.s38dH ⧸ d.s38dO)) := hl.caseA
  exact ⟨hs, (hout.2 hs).1, hM⟩

theorem lin_layer_nonabelian :
    ∃ x y : (CFSG.layer (d.s38dH ⧸ d.s38dO)), x * y ≠ y * x := by
  obtain ⟨hout, -⟩ := hl.hyp.sec3_3_two hl.gms
  obtain ⟨⟨-, -, -, hnc, -, halt, -⟩, -⟩ := hout
  rcases halt.or with hA | hB
  · have := hA.2.1
    rw [hnc] at this
    exact this
  · obtain ⟨D₁, D₂, -, -, -, -, hn₁, -, -, hsup, -⟩ := hB
    obtain ⟨x, y, hxy⟩ := hn₁
    have hD₁ : D₁ ≤ CFSG.layer (d.s38dH ⧸ d.s38dO) := by
      rw [← hnc]
      exact le_sup_left.trans hsup.le
    exact ⟨⟨(x : _), hD₁ x.2⟩, ⟨(y : _), hD₁ y.2⟩, fun e => hxy (Subtype.ext
      (congrArg (fun z : ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) => (z : d.s38dH ⧸ d.s38dO)) e))⟩

theorem lin_M₂_le_H : d.M₂ ≤ d.s38dH := s38d_M₂_le_H d

theorem lin_theta_mem_layer (m : d.M₂) :
    d.s38dθ ⟨(m : G), lin_M₂_le_H hl m.2⟩ ∈ CFSG.layer (d.s38dH ⧸ d.s38dO) := by
  rw [← (lin_layer_facts hl).2.2]
  exact mem_map_of_mem _ (mem_subgroupOf.2 m.2)

@[expose] def linπ : ↥d.M₂ →* ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) :=
  (d.s38dθ.comp (Subgroup.inclusion (lin_M₂_le_H hl))).codRestrict _ (lin_theta_mem_layer hl)

theorem lin_π_surjective : Function.Surjective (linπ hl) := by
  rintro ⟨y, hy⟩
  rw [← (lin_layer_facts hl).2.2] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨(x : G), mem_subgroupOf.1 hx⟩, rfl⟩

theorem lin_π_ker_odd : Odd (Nat.card (linπ hl).ker) := by
  have hO : Odd (Nat.card d.s38dO) := GMSK.odd_card_standardComponentOddCore _
  let ψ : (linπ hl).ker →* d.s38dO :=
    { toFun := fun m => ⟨⟨(m.1 : G), lin_M₂_le_H hl m.1.2⟩, by
        have := m.2
        rw [MonoidHom.mem_ker] at this
        have h2 := congrArg Subtype.val this
        exact (QuotientGroup.eq_one_iff _).1 h2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective ψ := by
    intro a b hab
    have h2 : ((a : d.M₂) : G) = ((b : d.M₂) : G) :=
      congrArg (fun z : d.s38dO => (((z : d.s38dH)) : G)) hab
    exact Subtype.ext (Subtype.ext h2)
  exact Odd.of_dvd_nat hO (Subgroup.card_dvd_of_injective ψ hinj)

theorem lin_exists_radicals_of_isSylowOf_M₂ {R : Subgroup G} (hR : IsSylowOf 2 R d.M₂) :
    ∃ R₁ R₂ : Subgroup G, LinearThree.Radicals R R₁ R₂ ((2 ^ f) ^ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := by have := hl.hyp.two_le; omega
  have hRle : R ≤ d.M₂ := hR.le
  have hR' : IsSylowOf 2 (R.subgroupOf d.M₂) (⊤ : Subgroup ↥d.M₂) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hR.isPGroup.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hR).2.2
  obtain ⟨R₁, R₂, hrad⟩ := LinCase.radicals_of_surjective_odd_ker hf (lin_layer_facts hl).2.1
    (linπ hl) (lin_π_surjective hl) (lin_π_ker_odd hl) hR'
  have := hrad.map d.M₂.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRle] at this
  exact ⟨_, _, this⟩

end Layer

end Data

end CFSG.LocalAnalysis.EvenBN.U5
