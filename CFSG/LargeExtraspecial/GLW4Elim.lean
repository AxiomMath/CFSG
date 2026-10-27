module

public import CFSG.LargeExtraspecial.GLW4RhoMain
public import CFSG.LargeExtraspecial.GLW4Inv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem exists_lift_sq {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar) (hss : s * s = 1) :
    ∃ σ : G, ∃ hσ : σ ∈ S.M, S.ρ ⟨σ, hσ⟩ = s ∧ (σ * σ = 1 ∨ σ * σ = S.z) := by
  obtain ⟨⟨m, hm⟩, rfl⟩ := hs
  have hsM : S.ρ ⟨m, hm⟩ ∈ S.Mbar := Config.ρ_mem_Mbar _
  have hqQ : m * m ∈ S.QG :=
    (S.ρ_eq_one_iff ⟨m * m, S.M.mul_mem hm hm⟩).mp (by rw [ρ_mul hm hm]; exact hss)
  have hfix : (S.ρ ⟨m, hm⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (m * m)) = S.cl (m * m) := by
    rw [← Config.cl_conj hm hqQ, show m * (m * m) * m⁻¹ = m * m by group]
  obtain ⟨a, ha, b, hb, hab⟩ := C.exists_eq_add (S.cl (m * m))
  have hsab : (S.ρ ⟨m, hm⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) b +
      (S.ρ ⟨m, hm⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + b := by
    rw [add_comm, ← map_add, hab, hfix]
  obtain ⟨-, hb'⟩ := C.eq_of_add_eq (C.apply_mem_At_of_not_mem hsM hsX hb) ha
    (C.apply_mem_Bt_of_not_mem hsM hsX ha) hb hsab
  obtain ⟨h, hhQ, hcl⟩ := S.exists_cl a
  have hhM := S.QG_le_M hhQ
  refine ⟨h * m, S.M.mul_mem hhM hm, ?_, ?_⟩
  · rw [ρ_mul hhM hm, (S.ρ_eq_one_iff ⟨h, hhM⟩).mpr hhQ, one_mul]
  · have hQ' : m * h * m⁻¹ ∈ S.QG := S.conj_mem_QG hm hhQ
    have hP : h * (m * h * m⁻¹) * (m * m) ∈ S.QG := S.QG.mul_mem (S.QG.mul_mem hhQ hQ') hqQ
    rw [show h * m * (h * m) = h * (m * h * m⁻¹) * (m * m) by group]
    refine (S.cl_eq_zero_iff hP).mp ?_
    rw [S.cl_mul (S.QG.mul_mem hhQ hQ') hqQ, S.cl_mul hhQ hQ', Config.cl_conj hm hhQ, hcl,
      ← hab, hb']
    exact ZModModule.add_self _

theorem false_of_config_four [IsSimpleGroup G] (C : Config S) (h4 : S.width = 4) : False := by
  by_cases hinv : ∀ y ∈ S.M, y * y = 1 → y ∈ C.X
  · have hr : finrank (ZMod 2) C.At = 4 := by rw [C.finrank_At, h4]
    let e : Basis (Fin 4) (ZMod 2) C.At := Module.finBasisOfFinrankEq (ZMod 2) C.At hr
    obtain ⟨s₁, hs₁, hs₁X, hss, hJ⟩ := exists_s₁ e
    obtain ⟨σ, hσM, hρ, hσσ⟩ := exists_lift_sq hs₁ hs₁X hss
    have hσX : σ ∉ C.X := fun h => hs₁X (hρ ▸ C.ρ_mem_Xbar h hσM)
    rcases hσσ with h1 | hz
    · exact hσX (hinv σ hσM h1)
    · exact false_of_sq_eq_z_of_inv hσM hσX hz (by rw [hρ]; exact isGoodForm_of_gram e hJ) hinv
  · obtain ⟨y, hyM, hyy, hyX⟩ : ∃ y ∈ S.M, y * y = 1 ∧ y ∉ C.X := by
      by_contra h
      exact hinv fun y hyM hyy => by_contra fun hyX => h ⟨y, hyM, hyy, hyX⟩
    by_cases halt : ∀ a, C.formOf (S.ρ ⟨y, hyM⟩) a a = 0
    · exact false_of_involution_alt h4 hyM hyX hyy halt
    · exact false_of_involution_N h4 hyM hyX hyy (by
        by_contra h
        exact halt fun a => by_contra fun ha => h ⟨a, ha⟩)

end CFSG.LargeExtraspecial.GLW4
