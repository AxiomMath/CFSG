module

public import CFSG.GF2Type.SmithTypeE.E8.Clause4

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
  CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)


variable {G : Type} [Group G] [Finite G]

theorem mem_collSpace_e7Y56_iff (u : Fin e7Data.d →₀ ZMod 2) : u ∈ collSpace e7Y56 ↔ u ∈ W0 := by
  have h := mem_collSpace_iff (1 : ↥(adjointGroup .E7 (ZMod 2))) u
  simp only [F.rep_one_apply, inv_one] at h
  exact h

section Ext

variable
  [IsSimpleGroup G]

theorem exists_conj_mem_M_not_mem_QG {S : Setting G}
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)} {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}
    (hφ : SmithE8Clauses123 S φ ψ) : ∃ x : G, IsConj S.z x ∧ x ∈ S.M ∧ x ∉ S.QG := by
  obtain ⟨b, hb⟩ : ∃ b : Fin e7Data.d, wgrade b = -1 := by decide
  obtain ⟨c₀, hc₀c, hc₀Q, hc₀w⟩ := hφ.2.2.1 e7Y56 F.e7Y56_mem_weightVec
  obtain ⟨c₁, hc₁c, hc₁Q, hc₁w⟩ := hφ.2.2.1 (Finsupp.single b 1) (F.single_mem_weightVec b)
  have hc₀z : c₀ ≠ S.z := by
    intro h
    rw [h, S.cl_z, map_zero] at hc₀w
    exact F.wt_ne_zero_core F.e7Y56_mem_weightVec hc₀w.symm
  have hc₁z : c₁ ≠ S.z := by
    intro h
    rw [h, S.cl_z, map_zero] at hc₁w
    exact F.wt_ne_zero_core (F.single_mem_weightVec b) hc₁w.symm
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hc₀c
  have hb_opp : b ≠ F.opI ⟨0, by decide⟩ := by
    intro h
    have h1 : F.e8fGrade b = -3 := by
      rw [h]
      have h2 : e7Data.wt (F.opI ⟨0, by decide⟩) = -e7Data.wt 0 := F.wt_opI ⟨0, by decide⟩
      show ![2, 3, 4, 6, 5, 4, 3] ⬝ᵥ e7Data.wt (F.opI ⟨0, by decide⟩) = -3
      rw [h2]
      decide
    have h3 : F.e8fGrade b = wgrade b := rfl
    omega
  have hff : F.ff e7Y56 (Finsupp.single b 1) = 0 := by
    rw [F.single_e7Y56, F.ff_single_single, if_neg hb_opp]
  have hcomm : c₀ * c₁ = c₁ * c₀ := by
    have h := isometry8 hφ.1 (S.cl c₀) (S.cl c₁)
    rw [hc₀w, hc₁w, hff] at h
    exact (S.polar_cl_eq_zero_iff hc₀Q hc₁Q).1 h.symm
  have hnc : c₁ ∉ S.Qa g₀ := by
    intro h
    have h1 := (hφ.2.2.2 g₀ c₁ (hg₀ ▸ hc₀Q) (hg₀ ▸ hc₀z) hc₁c hc₁Q hc₁z).1 h
    rw [hg₀, hc₀w, hc₁w] at h1
    have h2 := (mem_W0 _).1 ((mem_collSpace_e7Y56_iff _).1 h1) b (by omega)
    simp at h2
  refine ⟨g₀⁻¹ * c₁ * g₀, ?_, ?_, ?_⟩
  · obtain ⟨h₁, hh₁⟩ := isConj_iff.mp hc₁c
    exact isConj_iff.mpr ⟨g₀⁻¹ * h₁, by rw [← hh₁]; group⟩
  · rw [S.mem_M_iff]
    have e1 : g₀⁻¹ * c₁ * g₀ * S.z = g₀⁻¹ * (c₁ * c₀) * g₀ := by
      rw [← hg₀]
      group
    have e2 : S.z * (g₀⁻¹ * c₁ * g₀) = g₀⁻¹ * (c₀ * c₁) * g₀ := by
      rw [← hg₀]
      group
    rw [e1, e2, hcomm]
  · intro hx
    exact hnc ((SME.mem_Qa_iff S g₀ c₁).2 hx)

theorem smithE8Compat_of (I : Inputs10) (hAS : AschbacherSmithWideInput) : SmithE8Compat := by
  intro G _ _ _ S hw hU
  obtain ⟨φ, ψ, hφ⟩ := clauses123 I hAS S hw hU
  have h4 := smithE8Clause4_of I hw hU hφ
  refine ⟨φ, ψ, hφ, h4, fun r hr => ?_⟩
  obtain ⟨x₀, hx₀c, hx₀M, hx₀Q⟩ := exists_conj_mem_M_not_mem_QG hφ
  obtain ⟨c, hc⟩ := isConj_iff.mp ((h4 x₀ hx₀M hx₀c hx₀Q).symm.trans hr)
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm c)
  have hψm : ψ (rhoM S m) = c := by rw [hm, MulEquiv.apply_symm_apply]
  have hxM : (m : G) * x₀ * (m : G)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem m.2 hx₀M) (S.M.inv_mem m.2)
  refine ⟨(m : G) * x₀ * (m : G)⁻¹, hxM, hx₀c.trans (isConj_iff.mpr ⟨(m : G), rfl⟩), ?_, ?_⟩
  · intro hQ
    apply hx₀Q
    have h1 := S.conj_mem_QG (S.M.inv_mem m.2) hQ
    rwa [show (m : G)⁻¹ * ((m : G) * x₀ * (m : G)⁻¹) * (m : G)⁻¹⁻¹ = x₀ by group] at h1
  · have e : (⟨(m : G) * x₀ * (m : G)⁻¹, hxM⟩ : S.M) = m * ⟨x₀, hx₀M⟩ * m⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv])
    show ψ (rhoM S ⟨(m : G) * x₀ * (m : G)⁻¹, hxM⟩) = r
    rw [e]
    simp only [map_mul, map_inv]
    rw [hψm]
    exact hc

end Ext

end CFSG.GF2Type.SmithTypeE.E8
