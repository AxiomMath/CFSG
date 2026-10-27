module

public import CFSG.LargeExtraspecial.GLRFormBeta
public import CFSG.LargeExtraspecial.GLW4Phi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}
variable {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
include hτM hτX

omit hτX in
theorem polar_conj_eq_formOf {h h' : G} (hh : h ∈ C.A) (hh' : h' ∈ C.A) :
    polar S.q (S.cl (τ * h * τ⁻¹)) (S.cl h') =
      C.formOf (S.ρ ⟨τ, hτM⟩) ⟨S.cl h', hh'.2⟩ ⟨S.cl h, hh.2⟩ := by
  rw [Config.formOf_apply, Config.cl_conj hτM (C.A_le_QG hh), polar_comm]

theorem commute_iff_formOf {h h' : G} (hh : h ∈ C.A) (hh' : h' ∈ C.A) :
    (τ * h * τ⁻¹) * h' = h' * (τ * h * τ⁻¹) ↔
      C.formOf (S.ρ ⟨τ, hτM⟩) ⟨S.cl h', hh'.2⟩ ⟨S.cl h, hh.2⟩ = 0 := by
  rw [← polar_conj_eq_formOf hτM hh hh',
    S.polar_cl_eq_zero_iff (C.B_le_QG (conj_mem_B hτM hτX hh)) (C.A_le_QG hh')]

theorem phiOf_mul_eq {h h' : G} (hh : h ∈ C.A) (hh' : h' ∈ C.A) :
    (C.formOf (S.ρ ⟨τ, hτM⟩) ⟨S.cl h', hh'.2⟩ ⟨S.cl h, hh.2⟩ = 0 →
      phiOf τ h * phiOf τ h' = phiOf τ (h * h')) ∧
    (C.formOf (S.ρ ⟨τ, hτM⟩) ⟨S.cl h', hh'.2⟩ ⟨S.cl h, hh.2⟩ = 1 →
      phiOf τ h * phiOf τ h' = phiOf τ (h * h') * S.z) := by
  refine ⟨fun h0 => phiOf_mul_of_commute ((commute_iff_formOf hτM hτX hh hh').mpr h0),
    fun h1 => ?_⟩
  have hb := conj_mem_B hτM hτX hh
  have hnc : (τ * h * τ⁻¹) * h' ≠ h' * (τ * h * τ⁻¹) := fun hc => by
    rw [(commute_iff_formOf hτM hτX hh hh').mp hc] at h1
    exact zero_ne_one h1
  rcases S.mul_comm_or (C.B_le_QG hb) (C.A_le_QG hh') with hc | hc
  · exact absurd hc hnc
  · exact phiOf_mul_of_eq_z hτM (S.QG_le_M (C.A_le_QG hh)) (S.QG_le_M (C.A_le_QG hh')) hc

theorem phiOf_mul_self_of_formOf {h : G} (hh : h ∈ C.A)
    (h0 : C.formOf (S.ρ ⟨τ, hτM⟩) ⟨S.cl h, hh.2⟩ ⟨S.cl h, hh.2⟩ = 0) :
    phiOf τ h * phiOf τ h = 1 := by
  have hc := (commute_iff_formOf hτM hτX hh hh).mpr h0
  exact phiOf_mul_self hh (conj_mem_B hτM hτX hh) hc

end CFSG.LargeExtraspecial.GLW4
