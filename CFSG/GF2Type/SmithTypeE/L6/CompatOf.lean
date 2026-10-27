module

public import CFSG.GF2Type.SmithTypeE.L6.TransMain
public import CFSG.GF2Type.SmithTypeE.L6.Compat
public import CFSG.GF2Type.SmithTypeE.L6.TrOrbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.LMod
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)
open CFSG.LargeExtraspecial.SMod20 (V)
open CFSG.SmithL6 (meetCard distB)
open scoped MatrixGroups

attribute [local irreducible] tvP T6 CFSG.SmithL6.tvList CFSG.SmithL6.tvCols CFSG.SmithL6.wt

variable {G : Type} [Group G] [Finite G]

section Compat

theorem meetCard_comm' {i j : ℕ} (hi : i < 1395) (hj : j < 1395) : meetCard i j = meetCard j i := by
  rw [meetCard_eq_card hi hj, meetCard_eq_card hj hi, Finset.inter_comm]

theorem exists_conj_mem_M_not_mem_QG [IsSimpleGroup G] (I : Inputs10) (S : Setting G)
    (hw : S.width = 10) {ψ : Mbar0 S ≃* T6} {φ : S.Qt ≃ₗ[ZMod 2] V} (hmod : IsModelPhi S ψ φ)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hane : g * S.z * g⁻¹ ≠ S.z) :
    ∃ x : G, IsConj S.z x ∧ x ∈ S.M ∧ x ∉ S.QG := by
  have hne : {j : Fin 1395 | meetCard (planeOf S ψ g).val j.val = 1}.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), ncard_meetCard_one (planeOf S ψ g).2]
    norm_num
  obtain ⟨j, hj⟩ := hne
  obtain ⟨h, hbQ, hbne, hpl⟩ := exists_planeOf_eq ψ hw haQ hane j
  have hj' : meetCard (planeOf S ψ g).val (planeOf S ψ h).val = 1 := by rw [hpl]; exact hj
  have hcomm := (commute_iff_not_opp I ψ hw haQ hane hbQ hbne haQ hane).2 (by
    intro ho
    have := (opp_iff_meetCard (planeOf S ψ h).2 (planeOf S ψ g).2).1 ho
    rw [meetCard_comm' (planeOf S ψ h).2 (planeOf S ψ g).2, hj'] at this
    exact absurd this (by norm_num))
  have hnQa : h * S.z * h⁻¹ ∉ S.Qa g := by
    intro hb
    have := (mem_Qa_iff_adjW I hmod hw haQ hane hbQ hbne).1 hb
    rw [adjW_iff (planeOf S ψ g).2 (planeOf S ψ h).2] at this
    have h1 : distB (planeOf S ψ g).val (planeOf S ψ h).val = 2 := by
      simp [distB, hj']
    omega
  refine ⟨g⁻¹ * (h * S.z * h⁻¹) * g, ?_, ?_, ?_⟩
  · exact isConj_iff.mpr ⟨g⁻¹ * h, by group⟩
  · rw [S.mem_M_iff]
    calc g⁻¹ * (h * S.z * h⁻¹) * g * S.z = g⁻¹ * ((h * S.z * h⁻¹) * (g * S.z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * S.z * g⁻¹) * (h * S.z * h⁻¹)) * g := by rw [hcomm]
      _ = S.z * (g⁻¹ * (h * S.z * h⁻¹) * g) := by group
  · intro hx
    exact hnQa ((SME.mem_Qa_iff S g _).2 hx)

theorem exists_tv_of_clause4 {S : Setting G} {ψ : Mbar0 S ≃* T6} {φ : S.Qt ≃ₗ[ZMod 2] V}
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩))
    (h4 : SmithL6Clause4 S φ) (y : S.M) (hxc : IsConj S.z (y : G)) (hxQ : (y : G) ∉ S.QG) :
    ∃ (k : Fin 1953) (h0 : rhoM S y ∈ Mbar0 S), ψ ⟨rhoM S y, h0⟩ = ⟨tvP k, tvP_mem k⟩ := by
  obtain ⟨k, hk, hkx⟩ := h4 (y : G) hxc y.2 hxQ
  have hPhi : Phi S φ y = tvEquiv k := (acts_iff y.2 hk).1 hkx
  obtain ⟨m₀, h0₀, hm₀⟩ := exists_rhoM_mem_Mbar0 ψ ⟨tvP ⟨k, hk⟩, tvP_mem _⟩
  have hPhi0 : Phi S φ m₀ = tvEquiv k := by
    rw [hψ m₀ h0₀, hm₀, rhoMod_tvP]
  have heq : rhoM S y = rhoM S m₀ :=
    PhiB_injective φ (by rw [PhiB_rhoM, PhiB_rhoM, hPhi, hPhi0])
  have h0 : rhoM S y ∈ Mbar0 S := heq ▸ h0₀
  refine ⟨⟨k, hk⟩, h0, ?_⟩
  exact (congrArg ψ (Subtype.ext heq)).trans hm₀

theorem compat_conj2 {S : Setting G} {ψ : Mbar0 S ≃* T6} {φ : S.Qt ≃ₗ[ZMod 2] V}
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩))
    (h4 : SmithL6Clause4 S φ) (x : G) (hx : x ∈ S.M) (hxc : IsConj S.z x) (hxQ : x ∉ S.QG) :
    ∃ (k : Fin 1953) (h0 : (⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S),
      ψ ⟨⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩ := by
  obtain ⟨k, h0, h⟩ := exists_tv_of_clause4 hψ h4 ⟨x, hx⟩ hxc hxQ
  exact ⟨k, h0, h⟩

theorem psi_rhoM_conj {S : Setting G} (ψ : Mbar0 S ≃* T6) (m y : S.M)
    (hm : rhoM S m ∈ Mbar0 S) (hy : rhoM S y ∈ Mbar0 S) (h : rhoM S (m * y * m⁻¹) ∈ Mbar0 S) :
    ψ ⟨rhoM S (m * y * m⁻¹), h⟩ = ψ ⟨rhoM S m, hm⟩ * ψ ⟨rhoM S y, hy⟩ * (ψ ⟨rhoM S m, hm⟩)⁻¹ := by
  have e : (⟨rhoM S (m * y * m⁻¹), h⟩ : Mbar0 S) =
      ⟨rhoM S m, hm⟩ * ⟨rhoM S y, hy⟩ * (⟨rhoM S m, hm⟩)⁻¹ := by
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  refine (congrArg ψ e).trans ?_
  simp only [map_mul, map_inv]

theorem rhoM_conj_mem {S : Setting G} (m y : S.M) (hy : rhoM S y ∈ Mbar0 S) :
    rhoM S (m * y * m⁻¹) ∈ Mbar0 S := by
  rw [map_mul, map_mul, map_inv]
  exact (timmesfeldFStar_normal S.Mbar).conj_mem _ hy _

theorem exists_conj_tv {S : Setting G} {ψ : Mbar0 S ≃* T6} {φ : S.Qt ≃ₗ[ZMod 2] V}
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩))
    (h4 : SmithL6Clause4 S φ) (y₀ : S.M) (hy₀c : IsConj S.z (y₀ : G))
    (hy₀Q : (y₀ : G) ∉ S.QG) (k : Fin 1953) :
    ∃ (x : S.M) (h0 : rhoM S x ∈ Mbar0 S), IsConj S.z (x : G) ∧ (x : G) ∉ S.QG ∧
      ψ ⟨rhoM S x, h0⟩ = ⟨tvP k, tvP_mem k⟩ := by
  obtain ⟨k₀, h0₀, hk₀⟩ := exists_tv_of_clause4 hψ h4 y₀ hy₀c hy₀Q
  obtain ⟨g₁, hg₁, hg₁k⟩ := exists_mem_T6_apply_eq k₀ k
  obtain ⟨m, h0m, hm⟩ := exists_rhoM_mem_Mbar0 ψ ⟨g₁, hg₁⟩
  have h0x := rhoM_conj_mem m y₀ h0₀
  have hxG : (((m * y₀ * m⁻¹ : S.M)) : G) = (m : G) * (y₀ : G) * (m : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨m * y₀ * m⁻¹, h0x, ?_, ?_, ?_⟩
  · rw [hxG]
    exact hy₀c.trans (isConj_iff.mpr ⟨(m : G), rfl⟩)
  · intro hQ
    apply hy₀Q
    rw [hxG] at hQ
    have := S.conj_mem_QG (S.M.inv_mem m.2) hQ
    rwa [show (m : G)⁻¹ * ((m : G) * (y₀ : G) * (m : G)⁻¹) * ((m : G)⁻¹)⁻¹ = (y₀ : G) by group]
      at this
  · have e1 := psi_rhoM_conj ψ m y₀ h0m h0₀ h0x
    have e2 := congrArg₂ (fun a b : T6 => a * b * a⁻¹) hm hk₀
    have e3 : (⟨g₁, hg₁⟩ : T6) * ⟨tvP k₀, tvP_mem k₀⟩ * (⟨g₁, hg₁⟩ : T6)⁻¹ =
        ⟨tvP k, tvP_mem k⟩ := by
      apply Subtype.ext
      have := mul_tvP_mul_inv hg₁ k₀
      rw [hg₁k] at this
      exact this
    exact (e1.trans e2).trans e3

theorem compat_conj3 {S : Setting G} {ψ : Mbar0 S ≃* T6} {φ : S.Qt ≃ₗ[ZMod 2] V}
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩))
    (h4 : SmithL6Clause4 S φ) {x₀ : G} (hx₀M : x₀ ∈ S.M) (hx₀c : IsConj S.z x₀)
    (hx₀Q : x₀ ∉ S.QG) (k : Fin 1953) :
    ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ∃ h0 : (⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S,
        ψ ⟨⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩ := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : S.M, (y₀ : G) = x₀ := ⟨⟨x₀, hx₀M⟩, rfl⟩
  obtain ⟨x, h0, hc, hQ, h⟩ := exists_conj_tv hψ h4 y₀ (by rw [hy₀]; exact hx₀c)
    (by rw [hy₀]; exact hx₀Q) k
  exact ⟨(x : G), x.2, hc, hQ, h0, h⟩

theorem exists_conj_of_clauses [IsSimpleGroup G] (I : Inputs10) (S : Setting G)
    (hw : S.width = 10) {ψ : Mbar0 S ≃* T6} {φ : S.Qt ≃ₗ[ZMod 2] V} (hφ : SmithL6Clauses1235 S φ)
    (hmod : IsModelPhi S ψ φ) : ∃ x : G, IsConj S.z x ∧ x ∈ S.M ∧ x ∉ S.QG := by
  obtain ⟨c, hc, hcQ, hcw⟩ := hφ.2.1 0 (by norm_num)
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hc
  have hQ : g₀ * S.z * g₀⁻¹ ∈ S.QG := by rw [hg₀]; exact hcQ
  have hane : g₀ * S.z * g₀⁻¹ ≠ S.z := by
    intro h
    rw [hg₀] at h
    rw [h, S.cl_z, map_zero] at hcw
    exact idWt_ne_zero (show (0 : ℕ) < 1395 by norm_num) (hcw.symm.trans (by decide))
  exact exists_conj_mem_M_not_mem_QG I S hw hmod hQ hane

theorem compat_conj3_of [IsSimpleGroup G] (I : Inputs10) (S : Setting G) (hw : S.width = 10)
    {ψ : Mbar0 S ≃* T6} {φ : S.Qt ≃ₗ[ZMod 2] V} (hφ : SmithL6Clauses1235 S φ)
    (hmod : IsModelPhi S ψ φ)
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩))
    (h4 : SmithL6Clause4 S φ) (k : Fin 1953) :
    ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ∃ h0 : (⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S,
        ψ ⟨⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩ := by
  obtain ⟨x₀, hx₀c, hx₀M, hx₀Q⟩ := exists_conj_of_clauses I S hw hφ hmod
  exact compat_conj3 hψ h4 hx₀M hx₀c hx₀Q k

theorem compat_of_clauses [IsSimpleGroup G] (I : Inputs10) (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {φ : S.Qt ≃ₗ[ZMod 2] V}
    (hφ : SmithL6Clauses1235 S φ) :
    ∃ ψ : Mbar0 S ≃* ↥T6, SmithL6Clause4 S φ ∧
      (∀ (c : G) (hc : c ∈ S.M)
        (h0 : (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S) (u : G), u ∈ S.QG →
          φ (S.cl (c * u * c⁻¹)) =
            rhoMod (ψ ⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0⟩) (φ (S.cl u))) ∧
      (∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
        ∃ (k : Fin 1953) (h0 : (⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S),
          ψ ⟨⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩) ∧
      (∀ k : Fin 1953, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
        ∃ h0 : (⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S,
          ψ ⟨⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩) := by
  obtain ⟨ψ, hmod, hψ⟩ := exists_isModelPhi_of_clauses_Phi I hw hU hφ
  have h4 : SmithL6Clause4 S φ := smithL6Clause4_of I involutionFacts S hw hU hφ
  exact ⟨ψ, h4, fun c hc h0 u hu => cl_conj_eq_rhoMod_of_Phi hψ c hc h0 u hu,
    compat_conj2 hψ h4, compat_conj3_of I S hw hφ hmod hψ h4⟩

theorem smithL6Compat_of (I : Inputs10) (hAS : AschbacherSmithWideInput) : SmithL6Compat := by
  intro G _ _ _ S hw hU
  obtain ⟨φ, hφ⟩ := clauses1235 I hAS S hw hU
  exact (compat_of_clauses I S hw hU hφ).elim fun ψ h =>
    ⟨φ, ψ, hφ, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem smithL6E33_of (I : Inputs10) (hAS : AschbacherSmithWideInput) : SmithL6E33 := by
  intro G _ _ _ S hw hU g hxM hxQ
  obtain ⟨φ, hφ⟩ := clauses1235 I hAS S hw hU
  exact smithL6E33_of_clauses I involutionFacts S hw hU hφ g hxM hxQ

end Compat

end CFSG.GF2Type.SmithTypeE.L6
