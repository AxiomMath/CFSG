module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FT1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FYP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.T1_sylow (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) :
    IsSylow2Of (P ⊔ zpowers x) ⊤ := by
  by_contra hS
  obtain ⟨x', hx'N, hx'T, _hx'2, hR2⟩ :=
    sec4F_exists_normalizer_elt (P := P ⊔ zpowers x) hT.T2 hS
  have hleT : CFSG.conjugate A x' ≤ P ⊔ zpowers x := by
    intro e he
    have hx'eA : x' * e * x'⁻¹ ∈ A := (mem_conjugate_iff A x' e).mp he
    have haT : x' * e * x'⁻¹ ∈ P ⊔ zpowers x := Subgroup.mem_sup_left (hT.AP hx'eA)
    have h1 := (Subgroup.mem_set_normalizer_iff''.mp hx'N (x' * e * x'⁻¹)).mp haT
    rwa [show x'⁻¹ * (x' * e * x'⁻¹) * x' = e by group] at h1
  have hle : CFSG.conjugate A x' ≤ P := h.conjA_le_P hT hleT
  have hmain : ∃ m : G, m ∈ normalizer (A : Set G) ∧
      m ∈ (P ⊔ zpowers x) ⊔ zpowers x' ∧ m ∉ P := by
    by_cases hc : CFSG.conjugate A x' = A
    · refine ⟨x', mem_normalizer_of_conjugate_eq hc, ?_, ?_⟩
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
      · intro hx'P
        exact hx'T (Subgroup.mem_sup_left hx'P)
    · have hu : CFSG.conjugate A x' = CFSG.conjugate A x := h.conjA_unique hT hle hc
      have hmN' : x' * x⁻¹ ∈ normalizer (A : Set G) := by
        apply mem_normalizer_of_conjugate_eq
        rw [← sec4F_conjugate_conjugate A x' x⁻¹, hu,
          sec4F_conjugate_conjugate A x x⁻¹, show x * x⁻¹ = 1 by group]
        ext a
        rw [mem_conjugate_iff]
        simp
      refine ⟨x' * x⁻¹, hmN', ?_, ?_⟩
      · have hx'R : x' ∈ (P ⊔ zpowers x) ⊔ zpowers x' :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
        have hxR : x ∈ (P ⊔ zpowers x) ⊔ zpowers x' :=
          Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
        exact mul_mem hx'R (inv_mem hxR)
      · intro hmP
        apply hx'T
        have hxT1 : x ∈ P ⊔ zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
        have hmT1 : x' * x⁻¹ ∈ P ⊔ zpowers x := Subgroup.mem_sup_left hmP
        have hmem : (x' * x⁻¹) * x ∈ P ⊔ zpowers x := mul_mem hmT1 hxT1
        rwa [show (x' * x⁻¹) * x = x' by group] at hmem
  obtain ⟨m, hmN, hmR, hmP⟩ := hmain
  have hP'M : P ⊔ zpowers m ≤ normalizer (A : Set G) :=
    sup_le hT.PM (Subgroup.zpowers_le.mpr hmN)
  have hP'R : P ⊔ zpowers m ≤ (P ⊔ zpowers x) ⊔ zpowers x' :=
    sup_le (le_trans le_sup_left le_sup_left) (Subgroup.zpowers_le.mpr hmR)
  have hP'2 : IsPGroup 2 ↥(P ⊔ zpowers m) := hR2.to_le hP'R
  have hmax := hT.max (P ⊔ zpowers m) le_sup_left hP'M hP'2
  exact hmP (hmax ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers m))

end CFSG.OddStandard.SmallF3.Omega
