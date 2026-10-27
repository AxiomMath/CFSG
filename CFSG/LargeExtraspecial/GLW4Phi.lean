module

public import CFSG.LargeExtraspecial.GLRSplitBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup QuadraticMap CFSG.LargeExtraspecial.GLR
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

@[expose] def phiOf (τ h : G) : G := h * (τ * h * τ⁻¹)

variable {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
include hτM hτX

theorem conj_mem_B {h : G} (hh : h ∈ C.A) : τ * h * τ⁻¹ ∈ C.B :=
  C.conj_mem_B_of_not_mem_X hτM hτX hh

theorem phiOf_mem_QG {h : G} (hh : h ∈ C.A) : phiOf τ h ∈ S.QG :=
  S.QG.mul_mem (C.A_le_QG hh) (C.B_le_QG (conj_mem_B hτM hτX hh))

omit [Finite G] hτX in
theorem phiOf_mul_z {h : G} (hh : h ∈ S.M) : phiOf τ (h * S.z) = phiOf τ h := by
  have hz : τ * S.z * τ⁻¹ = S.z := by rw [S.z_comm hτM, mul_inv_cancel_right]
  have hb : τ * h * τ⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hτM hh) (S.M.inv_mem hτM)
  have hc : S.z * (τ * h * τ⁻¹) = (τ * h * τ⁻¹) * S.z := (S.z_comm hb).symm
  unfold phiOf
  calc h * S.z * (τ * (h * S.z) * τ⁻¹) = h * (S.z * (τ * h * τ⁻¹)) * (τ * S.z * τ⁻¹) := by
        group
    _ = h * (τ * h * τ⁻¹) * (S.z * S.z) := by rw [hc, hz]; group
    _ = h * (τ * h * τ⁻¹) := by rw [S.z_mul_z, mul_one]

omit [Finite G] hτM hτX in
theorem conj_phiOf {m : G} (hmτ : m * τ = τ * m) (h : G) :
    m * phiOf τ h * m⁻¹ = phiOf τ (m * h * m⁻¹) := by
  have hmτ' : m * τ⁻¹ = τ⁻¹ * m := by
    rw [show τ⁻¹ * m = τ⁻¹ * (m * τ) * τ⁻¹ by group, hmτ]; group
  unfold phiOf
  calc m * (h * (τ * h * τ⁻¹)) * m⁻¹ = m * h * m⁻¹ * ((m * τ) * h * (m⁻¹ * (m * τ⁻¹) * m⁻¹)) := by
        group
    _ = m * h * m⁻¹ * (τ * (m * h * m⁻¹) * τ⁻¹) := by rw [hmτ, hmτ']; group

omit [Finite G] hτM hτX in
theorem phiOf_mul_of_commute {h h' : G} (hc : (τ * h * τ⁻¹) * h' = h' * (τ * h * τ⁻¹)) :
    phiOf τ h * phiOf τ h' = phiOf τ (h * h') := by
  unfold phiOf
  calc h * (τ * h * τ⁻¹) * (h' * (τ * h' * τ⁻¹))
      = h * ((τ * h * τ⁻¹) * h') * (τ * h' * τ⁻¹) := by group
    _ = h * (h' * (τ * h * τ⁻¹)) * (τ * h' * τ⁻¹) := by rw [hc]
    _ = h * h' * (τ * (h * h') * τ⁻¹) := by group

omit [Finite G] hτX in
theorem phiOf_mul_of_eq_z {h h' : G} (hh : h ∈ S.M) (hh' : h' ∈ S.M)
    (hc : (τ * h * τ⁻¹) * h' = S.z * (h' * (τ * h * τ⁻¹))) :
    phiOf τ h * phiOf τ h' = phiOf τ (h * h') * S.z := by
  have hhh : h * h' ∈ S.M := S.M.mul_mem hh hh'
  have hφ : h * h' * (τ * (h * h') * τ⁻¹) ∈ S.M :=
    S.M.mul_mem hhh (S.M.mul_mem (S.M.mul_mem hτM hhh) (S.M.inv_mem hτM))
  have e1 : h * S.z = S.z * h := S.z_comm hh
  unfold phiOf
  calc h * (τ * h * τ⁻¹) * (h' * (τ * h' * τ⁻¹))
      = h * ((τ * h * τ⁻¹) * h') * (τ * h' * τ⁻¹) := by group
    _ = (h * S.z) * (h' * (τ * h * τ⁻¹)) * (τ * h' * τ⁻¹) := by rw [hc]; group
    _ = S.z * (h * h' * (τ * (h * h') * τ⁻¹)) := by rw [e1]; group
    _ = h * h' * (τ * (h * h') * τ⁻¹) * S.z := (S.z_comm hφ).symm

omit hτM hτX in
theorem phiOf_mul_self {h : G} (hh : h ∈ C.A) (hb : τ * h * τ⁻¹ ∈ C.B)
    (hc : (τ * h * τ⁻¹) * h = h * (τ * h * τ⁻¹)) : phiOf τ h * phiOf τ h = 1 := by
  unfold phiOf
  calc h * (τ * h * τ⁻¹) * (h * (τ * h * τ⁻¹)) = h * ((τ * h * τ⁻¹) * h) * (τ * h * τ⁻¹) := by
        group
    _ = (h * h) * ((τ * h * τ⁻¹) * (τ * h * τ⁻¹)) := by rw [hc]; group
    _ = 1 := by rw [C.A_mul_self hh, C.B_mul_self hb, one_mul]

omit [Finite G] hτM hτX in
theorem commutator_phiOf {l h : G} (hlτ : l * τ = τ * l)
    (hφ : phiOf τ (l * h * l⁻¹) * phiOf τ (l * h * l⁻¹) = 1) :
    ⁅phiOf τ h, l⁆ = phiOf τ h * phiOf τ (l * h * l⁻¹) := by
  have h1 : l * (phiOf τ h)⁻¹ * l⁻¹ = (phiOf τ (l * h * l⁻¹))⁻¹ := by
    rw [← conj_phiOf hlτ h]; group
  rw [commutatorElement_def, mul_assoc (phiOf τ h * l), mul_assoc, ← mul_assoc l, h1,
    inv_eq_of_mul_eq_one_right hφ]

end CFSG.LargeExtraspecial.GLW4
