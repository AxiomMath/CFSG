module

public import CFSG.GF2Type.SmithTypeE.E7.DivMain
public import CFSG.GF2Type.SmithTypeE.E7.Compat
public import CFSG.GF2Type.SmithTypeE.E7.TransClauses

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.DMod CFSG.SmithD6
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Compat

variable
  [IsSimpleGroup G]

theorem smithE7Clause4_of (hUW : UWInput) (I : Inputs10) (hrank : TwoRankMbar S)
    (hw : S.width = 16) (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} (hφ : SmithE7Clauses1235 S φ) :
    SmithE7Clause4 S φ := by
  obtain ⟨ψ, hΦ⟩ := exists_Phi_eq_rhoMod hO hφ
  have hcl2 : ∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = wtV i := by
    intro i hi
    obtain ⟨c, hc, hcQ, hcw⟩ := hφ.2.1 i hi
    exact ⟨c, hc, hcQ, eq_wtV_of_code32 hcw⟩
  intro x hxc hxM hxQ
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxc
  obtain ⟨v, hvc, hvQ, hvQa⟩ := smithE7E33_of_clauses hrank hw hO hφ g hxM hxQ
  obtain ⟨k, rfl⟩ := isConj_iff.mp hvc
  obtain ⟨p, hp⟩ := acts_tv_of_mem_Qa hUW I hw hO hΦ hcl2 hxM hxQ ⟨hvQ, hvQa⟩
  exact ⟨p.val, p.2, (acts_iff hxM p.2).mpr hp⟩

theorem exists_conj_mem_M_not_mem_QG {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {ψ : S.Mbar ≃* TD6}
    (hUW : UWInput) (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hane : g * S.z * g⁻¹ ≠ S.z) :
    ∃ x : G, IsConj S.z x ∧ x ∈ S.M ∧ x ∉ S.QG := by
  have hne : {j : Fin 75735 | Mid (planeOf S φ g) j}.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), ncard_mid_general hUW]
    norm_num
  obtain ⟨j, hj⟩ := hne
  obtain ⟨h, hbQ, hbne, hpl⟩ := exists_planeOf_eq I hw hO hΦ haQ hane j
  have hmid : Mid (planeOf S φ g) (planeOf S φ h) := by
    rw [hpl]
    exact hj
  have hc := (commute_not_mem_Qa_iff I hw hO hΦ haQ hane hbQ hbne).mpr hmid
  refine ⟨g⁻¹ * (h * S.z * h⁻¹) * g, ?_, ?_, ?_⟩
  · exact isConj_iff.mpr ⟨g⁻¹ * h, by group⟩
  · rw [S.mem_M_iff]
    calc g⁻¹ * (h * S.z * h⁻¹) * g * S.z = g⁻¹ * ((h * S.z * h⁻¹) * (g * S.z * g⁻¹)) * g := by
          group
      _ = g⁻¹ * ((g * S.z * g⁻¹) * (h * S.z * h⁻¹)) * g := by rw [hc.1.eq]
      _ = S.z * (g⁻¹ * (h * S.z * h⁻¹) * g) := by group
  · intro hx
    exact hc.2 ((SME.mem_Qa_iff S g _).2 hx)

theorem exists_conj_tv {ψ : S.Mbar ≃* TD6}
    (h2 : ∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
      ∃ k : Fin 365211, ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {x₀ : G} (hx₀M : x₀ ∈ S.M) (hx₀c : IsConj S.z x₀) (hx₀Q : x₀ ∉ S.QG) (k : Fin 365211) :
    ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩ := by
  obtain ⟨k₀, hk₀⟩ := h2 x₀ hx₀M hx₀c hx₀Q
  obtain ⟨g₁, hg₁, hg₁k⟩ := exists_mem_TD6_apply_eq k₀ k
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm ⟨g₁, hg₁⟩)
  have hψm : ψ (rhoM S m) = ⟨g₁, hg₁⟩ := by rw [hm, MulEquiv.apply_symm_apply]
  have hxM : (m : G) * x₀ * (m : G)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem m.2 hx₀M) (S.M.inv_mem m.2)
  refine ⟨(m : G) * x₀ * (m : G)⁻¹, hxM, ?_, ?_, ?_⟩
  · exact hx₀c.trans (isConj_iff.mpr ⟨(m : G), rfl⟩)
  · intro hQ
    apply hx₀Q
    have := S.conj_mem_QG (S.M.inv_mem m.2) hQ
    rwa [show (m : G)⁻¹ * ((m : G) * x₀ * (m : G)⁻¹) * (m : G)⁻¹⁻¹ = x₀ by group] at this
  · have e : (⟨(m : G) * x₀ * (m : G)⁻¹, hxM⟩ : S.M) = m * ⟨x₀, hx₀M⟩ * m⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv])
    show ψ (rhoM S ⟨(m : G) * x₀ * (m : G)⁻¹, hxM⟩) = _
    have hk₀' : ψ (rhoM S ⟨x₀, hx₀M⟩) = ⟨tvP k₀, tvP_mem k₀⟩ := hk₀
    rw [e]
    simp only [map_mul, map_inv]
    rw [hψm, hk₀']
    apply Subtype.ext
    have := mul_tvP_mul_inv hg₁ k₀
    rw [hg₁k] at this
    exact this

theorem smithE7Compat_of (hTI : WeaklyClosedTITransitive.{0}) (I : Inputs10)
    (hAS : AschbacherSmithWideInput)
    (hUW : UWInput)
    (hrank : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
      S.width = 16 → Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) → TwoRankMbar S) :
    SmithE7Compat := by
  intro G _ _ _ S hw hO
  obtain ⟨φ, hφ⟩ := clauses1235 hTI I hAS S hw hO
  obtain ⟨ψ, hψ⟩ := exists_isModelPhi_of_clauses hO hφ
  have hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m)) := Phi_eq_rhoMod_of_cl hψ
  have h4 := smithE7Clause4_of hUW I (hrank G S hw hO) hw hO hφ
  have h2 : ∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
      ∃ k : Fin 365211, ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩ := by
    intro x hx hxc hxQ
    obtain ⟨k, hk, hkx⟩ := h4 x hxc hx hxQ
    have hPhi : Phi S φ ⟨x, hx⟩ = tvEquiv k := (acts_iff hx hk).mp hkx
    refine ⟨⟨k, hk⟩, rhoMod_injective ?_⟩
    rw [rhoMod_tvP]
    exact (hΦ ⟨x, hx⟩).symm.trans hPhi
  refine ⟨φ, ψ, hφ, h4, hψ, h2, fun k => ?_⟩
  obtain ⟨c, hc, hcQ, hcw⟩ := hφ.2.1 0 (by norm_num)
  obtain ⟨g₀, rfl⟩ := isConj_iff.mp hc
  have hane : g₀ * S.z * g₀⁻¹ ≠ S.z := by
    intro h
    rw [h, S.cl_z, map_zero] at hcw
    have h0 : wt 0 = 1 := wtFacts.zero
    rw [h0] at hcw
    have : code32 (0 : Fin 32 → ZMod 2) = 0 := by
      rw [← decode32_zero]
      exact code32_decode32 (by norm_num)
    rw [this] at hcw
    exact absurd hcw (by norm_num)
  obtain ⟨x₀, hx₀c, hx₀M, hx₀Q⟩ := exists_conj_mem_M_not_mem_QG hUW I hw hO hΦ hcQ hane
  exact exists_conj_tv h2 hx₀M hx₀c hx₀Q k

end Compat

end CFSG.GF2Type.SmithTypeE.E7
