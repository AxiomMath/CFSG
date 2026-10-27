module

public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7a

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} {c : G}

theorem isSylow2In_of_mem_RSet_le_rLayer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : c * c = 1) {R : Subgroup G} (hR : R ∈ RSet Ω)
    (hRc : R ≤ Subgroup.centralizer ({c} : Set G)) :
    ∃ K ∈ sectionMembers Ω (Subgroup.zpowers c),
      R ∈ fixedSylows (Subgroup.zpowers c) K ∧ R ≤ secMember (Subgroup.zpowers c) K := by
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR
  have hKt : K ∈ tqMembers Ω c :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hK, R, hRK, hRc⟩
  have hKs : K ∈ sectionMembers Ω (Subgroup.zpowers c) := by
    rw [sectionMembers_zpowers]; exact hKt
  have hfix : R ∈ fixedSylows (Subgroup.zpowers c) K :=
    mem_fixedSylows_zpowers_iff.mpr ⟨hRK, hRc⟩
  exact ⟨K, hKs, hfix, le_secMember hfix⟩

theorem rLayer_eq_sectionHull (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : c * c = 1) : rLayer Ω c = sectionHull Ω (Subgroup.zpowers c) := by
  apply le_antisymm
  · refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
    obtain ⟨K, hKs, -, hRle⟩ := isSylow2In_of_mem_RSet_le_rLayer hp hq hΩ hc2 hR hRc
    exact hRle.trans (le_sectionHull hKs)
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨J, hJ, rfl⟩ := hL
    refine iSup₂_le fun T hT => ?_
    have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := (mem_fixedSylows_zpowers_iff.mp hT).2
    exact le_iSup₂_of_le T (mem_RSet_of_isSylow2In hJ.1 (mem_fixedSylows_zpowers_iff.mp hT).1)
      (le_iSup_of_le hTc le_rfl)

theorem rLayer_eq_exactLayer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : c * c = 1) : rLayer Ω c = exactLayer Ω c := by
  rw [rLayer_eq_sectionHull hp hq hΩ hc2,
    sectionHull_zpowers hΩ (isPGroup_zpowers_of_sq_eq_one hc2)]

theorem mem_rLayer_iff_mem_sectionHull (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : c * c = 1) {x : G} :
    x ∈ rLayer Ω c ↔ x ∈ sectionHull Ω (Subgroup.zpowers c) := by
  rw [rLayer_eq_sectionHull hp hq hΩ hc2]

end CFSG.ClassicalInvolution.Asc77
