module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma57_of (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b)
    (hO : Asc82Outside) (tab : Asc82Tab5) : Asc82Lemma57 := by
  intro G _ _ t L S z r B A h
  have hBA : B ≤ A := by
    intro x hx
    rw [h.A_eq]
    exact Subgroup.mem_sup_right hx
  have hrA : r ∈ A := by
    rw [h.A_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers r)
  refine ⟨?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · conv_lhs => rw [h.A_eq]
      conv_lhs => rw [Subgroup.sup_eq_closure]
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact Subgroup.mem_sup_right hx
      · exact Subgroup.mem_sup_left
          (Subgroup.mem_inf.mpr ⟨hBA hx, (Subgroup.mem_inf.mp (h.B_le hx)).1⟩)
    · rw [Subgroup.sup_eq_closure, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact (Subgroup.mem_inf.mp hx).1
      · exact Subgroup.zpowers_le.mpr hrA hx
  · intro g hg
    subst hg
    have htL : t ∈ L := (h52b G t L h.toSec5Setting).1
    have htB : t ∈ B := h.B_split.1
    have hrJ : g⁻¹ * t * g ∈ CFSG.conjugate L g := by
      rw [mem_conjugate_iff]
      convert htL using 1
      group
    have hr2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [orderOf_conjugate_eq, h.involution]
    have hrC : g⁻¹ * t * g ∈ centralizer ({t} : Set G) := by
      have htCr : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
        (Subgroup.mem_inf.mp (h.B_le htB)).2
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp htCr).symm
    have hrN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
      sec4_mem_normalizer h36 h.toSec3SettingLB _ hrC
    have hrt : g⁻¹ * t * g ≠ t := by
      intro hEq
      have hnc : g⁻¹ * t * g ∉ centralizer (L : Set G) :=
        tab.kind_ne_central G L h.toSec5Setting.isOm6Z2 _ hr2 hrN (Or.inr (Or.inl h.type_r))
      exact hnc (hEq.symm ▸ sec4_t_mem_centralizer h.toSec3Setting)
    have hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic ↥P :=
      fun P hP => sec5_isCyclic_of_isSylow2Of (h52a G t L h.toSec5Setting) hP
    have hsub : twoPrimeRes (layerCent L (g⁻¹ * t * g)) ≤ CFSG.conjugate L g :=
      hO.thm2L G t L h.toSec3SettingLB hcyc
        (asc82OddInnerOm6_holds G L (Or.inl h.toSec5Setting.isOm6Z2)) (-1) g hrC hrt
        (layerCent L (g⁻¹ * t * g)) (Or.inl rfl)
    have hBE : B ⊓ layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g := by
      intro x hx
      obtain ⟨hxB, hxE⟩ := Subgroup.mem_inf.mp hx
      have hx2 : x ^ 2 = 1 := h.B_E32.1.2 x hxB
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
      obtain ⟨k, -, hk⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two (m := 1)).mp (by simpa using hdvd)
      exact hsub (Subgroup.subset_closure ⟨hxE, k, hk⟩)
    have htA : t ∈ A := hBA htB
    refine le_antisymm ?_ ?_
    · conv_lhs => rw [h.A_eq]
      conv_lhs => rw [Subgroup.sup_eq_closure]
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact Subgroup.mem_sup_left
          (Subgroup.mem_inf.mpr
            ⟨Subgroup.zpowers_le.mpr hrA hx, Subgroup.zpowers_le.mpr hrJ hx⟩)
      · have hBX : zpowers t ⊔ (B ⊓ layerCent L (g⁻¹ * t * g)) ≤
            (A ⊓ CFSG.conjugate L g) ⊔ zpowers t := by
          conv_lhs => rw [Subgroup.sup_eq_closure]
          rw [Subgroup.closure_le]
          intro y hy
          rcases hy with hy | hy
          · exact Subgroup.mem_sup_right hy
          · exact Subgroup.mem_sup_left
              (Subgroup.mem_inf.mpr ⟨hBA (Subgroup.mem_inf.mp hy).1, hBE hy⟩)
        exact hBX (h.B_split.2.2 ▸ hx)
    · rw [Subgroup.sup_eq_closure, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact (Subgroup.mem_inf.mp hx).1
      · exact Subgroup.zpowers_le.mpr htA hx

end CFSG.OddStandard.SmallF3.Omega
