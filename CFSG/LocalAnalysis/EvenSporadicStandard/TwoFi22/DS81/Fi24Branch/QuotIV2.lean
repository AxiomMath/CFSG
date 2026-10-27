module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotIV1
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotYComp
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42Rep
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Descent

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C] {c : CInv C} {t : C} {R J K O Y : Subgroup C}
  {L1 : Subgroup c.Qt}

theorem quot_cond_bar (hC : CCore c) (hR : RData c R) (hJ : JData c t R J)
    (hK : KDataC c t R J K O Y) (hF : U42Facts) (hcat : CatSections C)
    (hSch : CatalogOuterSolvable) (h : UniqueComp c R L1) :
    ∃ (X : Type) (_ : Group X) (π : ↥(L1 ⊓ c.bar J) →* X), Function.Surjective π ∧
      π.ker = (c.bar R).subgroupOf (L1 ⊓ c.bar J) ∧
      (IsU42Two X ∨ CFSG.Open.StatedClassicalModel X .PSU 4 2 1) := by
  obtain ⟨X, hXgrp, πJ, hπJs, hπJk, hX⟩ := hJ.quot
  letI : Group X := hXgrp
  let H : Subgroup c.Qt := L1 ⊓ c.bar J
  let N : Subgroup C := L1.comap c.qmap
  let H₁ : Subgroup C := J ⊓ N
  have hL1n : L1.Normal := L1_normal h
  let f : ↥H₁ →* ↥H :=
    (c.qmap.comp H₁.subtype).codRestrict H (fun x => by
      obtain ⟨hxJ, hxN⟩ := Subgroup.mem_inf.mp x.2
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_comap.mp hxN, Subgroup.mem_map.mpr ⟨x, hxJ, rfl⟩⟩)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨hyL1, hyJ⟩ := Subgroup.mem_inf.mp y.2
    obtain ⟨j, hjJ, hj_eq⟩ := Subgroup.mem_map.mp hyJ
    refine ⟨⟨j, Subgroup.mem_inf.mpr ⟨hjJ, Subgroup.mem_comap.mpr ?_⟩⟩, ?_⟩
    · rw [hj_eq]; exact hyL1
    · apply Subtype.ext
      exact hj_eq
  let g : ↥H₁ →* X := πJ.comp (Subgroup.inclusion (inf_le_left : H₁ ≤ J))
  have hker_le : f.ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hzx : (x : C) ∈ zpowers c.z := by
      apply c.qmap_eq_one_iff.mp
      have hval : (f x : c.Qt) = 1 := congrArg Subtype.val hx
      exact hval
    have hxR : (x : C) ∈ R := (Subgroup.zpowers_le.mpr hR.z_mem) hzx
    show πJ (Subgroup.inclusion (inf_le_left : H₁ ≤ J) x) = 1
    have hmem : Subgroup.inclusion (inf_le_left : H₁ ≤ J) x ∈ πJ.ker := by
      rw [hπJk, Subgroup.mem_subgroupOf]
      exact hxR
    exact MonoidHom.mem_ker.mp hmem
  obtain ⟨hh, hhf, hhk⟩ := exists_descent f hfsurj g hker_le
  let T : Subgroup X := hh.range
  let π : ↥H →* ↥T := hh.rangeRestrict
  have hπsurj : Function.Surjective π := hh.rangeRestrict_surjective
  have hTrange : T = g.range := by
    apply le_antisymm
    · intro z hz
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hz
      obtain ⟨x, rfl⟩ := hfsurj y
      exact MonoidHom.mem_range.mpr ⟨x, (hhf x).symm.trans hy⟩
    · intro z hz
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hz
      exact MonoidHom.mem_range.mpr ⟨f x, (hhf x).trans hx⟩
  have hTnormal : T.Normal := by
    rw [hTrange]
    refine ⟨fun n hn a => ?_⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hn
    obtain ⟨j, rfl⟩ := hπJs a
    have hyH1 : (j : C) * (x : C) * (j : C)⁻¹ ∈ H₁ := by
      obtain ⟨hxJ, hxN⟩ := Subgroup.mem_inf.mp x.2
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact J.mul_mem (J.mul_mem j.2 hxJ) (J.inv_mem j.2)
      · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
        exact hL1n.conj_mem (c.qmap (x : C)) (Subgroup.mem_comap.mp hxN) (c.qmap (j : C))
    let y : ↥H₁ := ⟨(j : C) * (x : C) * (j : C)⁻¹, hyH1⟩
    refine MonoidHom.mem_range.mpr ⟨y, ?_⟩
    have hincl : Subgroup.inclusion (inf_le_left : H₁ ≤ J) y =
        j * Subgroup.inclusion (inf_le_left : H₁ ≤ J) x * j⁻¹ := by
      apply Subtype.ext
      rfl
    change πJ (Subgroup.inclusion (inf_le_left : H₁ ≤ J) y) =
      πJ j * πJ (Subgroup.inclusion (inf_le_left : H₁ ≤ J) x) * (πJ j)⁻¹
    rw [hincl]
    simp only [map_mul, map_inv]
  have hTne : T ≠ ⊥ := by
    intro hbot
    have hH1leR : H₁ ≤ R := by
      intro x hx
      have hxrange : g ⟨x, hx⟩ ∈ g.range := MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
      rw [← hTrange, hbot] at hxrange
      have hgx : g ⟨x, hx⟩ = 1 := Subgroup.mem_bot.mp hxrange
      have hmem : Subgroup.inclusion (inf_le_left : H₁ ≤ J) ⟨x, hx⟩ ∈ πJ.ker :=
        MonoidHom.mem_ker.mpr hgx
      rw [hπJk, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have hYleH1 : Y ≤ H₁ := by
      intro y hy
      have hyJ : y ∈ J := hK.K_le_J (hK.Y_le hy)
      have hyL1 : c.qmap y ∈ L1 := by
        have hbarY : c.bar Y ≤ L1 :=
          perfect_le_L1 hC hcat hSch h (c.bar_perfect hK.Y_perfect)
        exact hbarY (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      exact Subgroup.mem_inf.mpr ⟨hyJ, Subgroup.mem_comap.mpr hyL1⟩
    have hbarYleR : c.bar Y ≤ c.bar R := c.bar_mono (le_trans hYleH1 hH1leR)
    obtain ⟨y, hyY, r, hrR, hne⟩ := bar_Y_hlat2 hR hJ hK
    exact hne (bar_R_comm hR y (hbarYleR hyY) r hrR)
  have hker_eq : hh.ker = (c.bar R).subgroupOf H := by
    rw [hhk]
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_subgroupOf]
      rw [MonoidHom.mem_ker] at hx
      have hxR : (x : C) ∈ R := by
        have hmem : Subgroup.inclusion (inf_le_left : H₁ ≤ J) x ∈ πJ.ker :=
          MonoidHom.mem_ker.mpr hx
        rw [hπJk, Subgroup.mem_subgroupOf] at hmem
        exact hmem
      have hmemR : ((f x : ↥H) : c.Qt) ∈ c.bar R :=
        Subgroup.mem_map.mpr ⟨x, hxR, rfl⟩
      rwa [hxy] at hmemR
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨r, hrR, hr_eq⟩ := Subgroup.mem_map.mp hy
      let x : ↥H₁ := ⟨r, Subgroup.mem_inf.mpr
        ⟨hJ.R_le hrR, Subgroup.mem_comap.mpr (by rw [hr_eq]; exact (Subgroup.mem_inf.mp y.2).1)⟩⟩
      refine Subgroup.mem_map.mpr ⟨x, ?_, ?_⟩
      · rw [MonoidHom.mem_ker]
        show πJ (Subgroup.inclusion (inf_le_left : H₁ ≤ J) x) = 1
        have hmem : Subgroup.inclusion (inf_le_left : H₁ ≤ J) x ∈ πJ.ker := by
          rw [hπJk, Subgroup.mem_subgroupOf]
          exact hrR
        exact MonoidHom.mem_ker.mp hmem
      · apply Subtype.ext
        exact hr_eq
  have hπker : π.ker = (c.bar R).subgroupOf H := by
    show (hh.rangeRestrict).ker = (c.bar R).subgroupOf H
    rw [MonoidHom.ker_rangeRestrict]
    exact hker_eq
  have hmodel := isU42Two_or_model_of_normal hF hX hTnormal hTne
  exact ⟨↥T, inferInstance, π, hπsurj, hπker, hmodel⟩

theorem quot_cond (hC : CCore c) (hR : RData c R) (hJ : JData c t R J)
    (hK : KDataC c t R J K O Y) (hF : U42Facts) (hcat : CatSections C)
    (hSch : CatalogOuterSolvable) (h : UniqueComp c R L1) :
    ∃ (X : Type) (_ : Group X)
      (π : ↥(L1 ⊓ centralizer ({c.qmap t} : Set c.Qt)) →* X), Function.Surjective π ∧
      π.ker = (c.bar R).subgroupOf (L1 ⊓ centralizer ({c.qmap t} : Set c.Qt)) ∧
      (IsU42Two X ∨ CFSG.Open.StatedClassicalModel X .PSU 4 2 1) := by
  rw [centralizer_qmap_t hR hJ]
  exact quot_cond_bar hC hR hJ hK hF hcat hSch h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
