module

public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

section Components

theorem le_center_of_le_range_of_ne {ι X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) {i j : ι} (hij : j ≠ i) {A : Subgroup X}
    (hAi : A ≤ (D.hom i).range) (hAj : A ≤ (D.hom j).range) : A ≤ Subgroup.center X := by
  intro a ha
  rw [Subgroup.mem_center_iff]
  have hle : ⨆ l, (D.hom l).range ≤ Subgroup.centralizer ({a} : Set X) := by
    refine iSup_le fun l => ?_
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hli : l = i
    · subst hli
      obtain ⟨x, hx⟩ := hAj ha
      rw [← hx]
      exact (D.commute j l hij x y).symm
    · obtain ⟨x, hx⟩ := hAi ha
      rw [← hx]
      exact (D.commute i l (Ne.symm hli) x y).symm
  intro g
  have hg : g ∈ ⨆ l, (D.hom l).range := by
    rw [D.generate]
    trivial
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

theorem range_le_of_mem_of_ne_sl23 {X : Type} [Group X] {c : CompData} (hc : c.Valid)
    (hc' : c ≠ CompData.sl23) (ψ : c.G →* X) {R : Subgroup c.G} (hR : R ∈ c.fund) {r : c.G}
    (hrR : r ∈ R) (N : Subgroup X) [N.Normal] (hrN : ψ r ∈ N) (hr : ψ r ≠ 1) :
    ψ.range ≤ N := by
  have hr1 : r ≠ 1 := fun h => hr (by rw [h, map_one])
  have hnorm : (N.comap ψ).Normal := Subgroup.Normal.comap inferInstance ψ
  rcases hc with ⟨t, n, hFT, hadm, rfl⟩ | rfl | rfl
  · have hq := (ModelFacts.modelClauseZero t n 3 1 Nat.prime_three hFT hadm).1
    have hne : ¬ (t = .PSL ∧ n = 2) := by
      rintro ⟨rfl, rfl⟩
      obtain ⟨-, -, -, -, h23⟩ := id hadm
      exact h23 (by norm_num)
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq (N.comap ψ)
      with h | h
    · exfalso
      refine hr1 (Gaps.fundNoncentral 3 t n 1 hFT hadm hne R hR r hrR fun y => ?_)
      have hrc : r ∈ Subgroup.center _ := h (Subgroup.mem_comap.mpr hrN)
      have hy := Subgroup.mem_center_iff.mp hrc y
      have h1 : r * y * r⁻¹ * y⁻¹ = 1 := by
        rw [← hy]
        group
      rw [h1]
      exact Subgroup.one_mem _
    · rintro _ ⟨m, rfl⟩
      have hm : m ∈ N.comap ψ := by
        rw [h]
        trivial
      exact hm
  · exact absurd rfl hc'
  · have hs : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := isSimpleGroup_m11_kernel
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap ψ) with h | h
    · exfalso
      have hrm : r ∈ N.comap ψ := Subgroup.mem_comap.mpr hrN
      rw [h] at hrm
      exact hr1 (Subgroup.mem_bot.mp hrm)
    · rintro _ ⟨m, rfl⟩
      have hm : m ∈ N.comap ψ := by
        rw [h]
        trivial
      exact hm

end Components

section Member

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {ι : Type}

theorem locImg_le_normalClosure_of_nonA1
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {K : Subgroup G} {u : G}
    (hK : K ∈ centralizingMembers Ω {x}) (hu : IsClassicalMember3 K u) (i : ι)
    (hi : locImg Ω x K ≤ (D.hom i).range) (hnA1 : D.kind i ≠ CompData.sl23)
    (hu' : u ∈ locLayer Ω x) :
    locImg Ω x K ≤ Subgroup.normalClosure
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩} :
        Set (locQuot Ω x)) := by
  have hKY : K ≤ locLayer Ω x := le_centralizingLayer hK
  have hcl : IsClassicalMember3 (locImg Ω x K)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩) :=
    (hu.subgroupOf hKY).map_oddQuotient
  have hmem : locImg Ω x K ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨K, hK, rfl⟩
  obtain ⟨j, R, hR, hKR⟩ := D.fundamental _ hmem
  have hKj : locImg Ω x K ≤ (D.hom j).range := by
    rw [hKR]
    exact Subgroup.map_le_range _ _
  have hji : j = i := by
    by_contra hne
    exact hcl.not_le_center (le_center_of_le_range_of_ne D hne hi hKj)
  have hnA1' : D.kind j ≠ CompData.sl23 := by
    rw [hji]
    exact hnA1
  have hū : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ ∈
      R.map (D.hom j) := by
    rw [← hKR]
    exact hcl.mem
  obtain ⟨r, hrR, hr⟩ := hū
  refine hKj.trans (range_le_of_mem_of_ne_sl23 (D.valid j) hnA1' (D.hom j) hR hrR _ ?_ ?_)
  · rw [hr]
    exact Subgroup.subset_normalClosure rfl
  · rw [hr]
    exact hcl.ne_one

end Member

end CFSG.ClassicalInvolution.Q3.Q3PP
