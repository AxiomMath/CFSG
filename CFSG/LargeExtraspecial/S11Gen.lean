module

public import CFSG.LargeExtraspecial.S6Basic
public import CFSG.LargeExtraspecial.S6EightB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] (T : Setting G)

omit [Finite G] in
theorem conj_z_mul_self (u : G) : u * T.z * u⁻¹ * (u * T.z * u⁻¹) = 1 :=
  (T.conjBy u).z_mul_z

theorem sq_eq_one_of_mem_inf {τ u α : G} (hτM : τ ∈ T.M) (hτu : τ = u * T.z * u⁻¹)
    (hτQ : τ ∉ T.QG) (hα : α ∈ T.QG ⊓ T.Qa u) : α ^ 2 = 1 := by
  have ht1 : T.ρ ⟨τ, hτM⟩ ≠ 1 := fun h => hτQ ((T.ρ_eq_one_iff _).mp h)
  rcases T.sq_eq_one_or_z hα.1 with h | h
  · exact h
  · exact absurd (h ▸ pow_mem hα.2 2) (z_not_mem_Qa_of_tau ht1 rfl hτu)

theorem exists_conj_of_not_mem_commQt {τ u α : G} (hτM : τ ∈ T.M) (hτu : τ = u * T.z * u⁻¹)
    (hτQ : τ ∉ T.QG) (hα : α ∈ T.QG ⊓ T.Qa u) (hαU : T.cl α ∉ T.commQt τ) :
    ∃ h ∈ T.QG, h * τ * h⁻¹ = τ * T.z ∧ h * α * h⁻¹ = α * T.z := by
  have hτ2 : τ ^ 2 = 1 := by rw [pow_two, hτu]; exact conj_z_mul_self T u
  have ht1 : T.ρ ⟨τ, hτM⟩ ≠ 1 := fun h => hτQ ((T.ρ_eq_one_iff _).mp h)
  rw [T.commQt_eq_orthogonal hτM hτ2, LinearMap.BilinForm.mem_orthogonal_iff] at hαU
  push Not at hαU
  obtain ⟨w, hw, hwα⟩ := hαU
  obtain ⟨h, hhQ, rfl⟩ := T.exists_cl w
  have hpol : polar T.q (T.cl h) (T.cl α) ≠ 0 := hwα
  have hhα : h * α ≠ α * h := fun e => hpol ((T.polar_cl_eq_zero_iff hhQ hα.1).mpr e)
  have hhα' : h * α * h⁻¹ = α * T.z := by
    rcases T.mul_comm_or hhQ hα.1 with e | e
    · exact absurd e hhα
    · rw [e, show T.z * (α * h) * h⁻¹ = T.z * α by group]
      exact (T.z_comm_QG hα.1).symm
  have hfix := (T.cl_mem_fixQt_iff hτM hhQ).mp hw
  rcases (T.cl_eq_cl_iff hhQ (T.conj_mem_QG hτM hhQ)).mp hfix.symm with e | e
  · exfalso
    apply hhα
    refine (commute_of_mem_QG_inf_Qa ht1 rfl hτu hα hhQ ?_).symm
    calc h * τ = τ * h * τ⁻¹ * τ := by rw [e]
      _ = τ * h := by group
  · have hzh : h⁻¹ * T.z * h = T.z := by
      rw [mul_assoc, ← T.z_comm_QG hhQ, ← mul_assoc, inv_mul_cancel, one_mul]
    refine ⟨h⁻¹, T.QG.inv_mem hhQ, ?_, ?_⟩
    · calc h⁻¹ * τ * h⁻¹⁻¹ = h⁻¹ * (τ * h * τ⁻¹) * τ := by group
        _ = h⁻¹ * (h * T.z) * τ := by rw [e]
        _ = T.z * τ := by group
        _ = τ * T.z := (T.z_comm hτM).symm
    · calc h⁻¹ * α * h⁻¹⁻¹ = h⁻¹ * (h * α * h⁻¹ * T.z) * h := by
            rw [hhα', mul_assoc α, T.z_mul_z, mul_one, inv_inv]
        _ = α * (h⁻¹ * T.z * h) := by group
        _ = α * T.z := by rw [hzh]

theorem polar_sub_eq_q {s : T.O} (v : T.Qt) :
    polar T.q v ((s : T.Qt ≃ₗ[ZMod 2] T.Qt) v - v) = T.q ((s : T.Qt ≃ₗ[ZMod 2] T.Qt) v - v) := by
  have hiso : T.q ((s : T.Qt ≃ₗ[ZMod 2] T.Qt) v) = T.q v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp s.2 v
  have h1 : polar T.q v ((s : T.Qt ≃ₗ[ZMod 2] T.Qt) v - v) =
      -T.q ((s : T.Qt ≃ₗ[ZMod 2] T.Qt) v - v) := by
    rw [polar, add_sub_cancel, hiso]
    ring
  rw [h1]
  rcases OrthoF2.zmod2_eq_zero_or_eq_one (T.q ((s : T.Qt ≃ₗ[ZMod 2] T.Qt) v - v)) with h | h <;>
    rw [h] <;> decide

theorem exists_conj_of_mem_commQt {τ u α : G} (hτM : τ ∈ T.M) (hτu : τ = u * T.z * u⁻¹)
    (hτQ : τ ∉ T.QG) (hα : α ∈ T.QG ⊓ T.Qa u) (hαU : T.cl α ∈ T.commQt τ) :
    ∃ y ∈ T.QG, y * α = α * y ∧ (y * τ * y⁻¹ = τ * α ∨ y * τ * y⁻¹ = τ * α * T.z) := by
  obtain ⟨y, hyQ, hy⟩ := (T.mem_commQt_iff' hτM).mp hαU
  have hτα : α * τ = τ * α :=
    commute_of_mem_Qa_tau (τ := (⟨τ, hτM⟩ : T.M)) hτu hα.2
  have hcQ : y * τ * y⁻¹ * τ⁻¹ ∈ T.QG := by
    have := T.commutator_mem_QG' hτM hyQ
    simpa using this
  have hcomm : y * α = α * y := by
    have h1 := T.cl_commutator' hτM hyQ
    rw [hy] at h1
    have h2 : polar T.q (T.cl y) (T.cl α) = 0 := by
      rw [h1, polar_sub_eq_q T (s := T.ρ ⟨τ, hτM⟩), ← h1,
        T.q_cl_eq_zero_iff hα.1]
      exact sq_eq_one_of_mem_inf T hτM hτu hτQ hα
    exact (T.polar_cl_eq_zero_iff hyQ hα.1).mp h2
  refine ⟨y, hyQ, hcomm, ?_⟩
  rcases (T.cl_eq_cl_iff hcQ hα.1).mp hy with e | e
  · left
    calc y * τ * y⁻¹ = y * τ * y⁻¹ * τ⁻¹ * τ := by group
      _ = α * τ := by rw [← e]
      _ = τ * α := hτα
  · right
    have e' : y * τ * y⁻¹ * τ⁻¹ = α * T.z := by
      rw [e, mul_assoc (y * τ * y⁻¹ * τ⁻¹), T.z_mul_z, mul_one]
    calc y * τ * y⁻¹ = y * τ * y⁻¹ * τ⁻¹ * τ := by group
      _ = α * T.z * τ := by rw [e']
      _ = α * τ * T.z := by rw [mul_assoc, ← T.z_comm hτM, ← mul_assoc]
      _ = τ * α * T.z := by rw [hτα]

omit [Finite G] in
theorem exists_conj_of_conj_mul' {τ u γ k : G} (hτu : τ = u * T.z * u⁻¹)
    (hγ : γ ∈ T.Qa u) (hγ1 : γ ≠ 1) (hγτ : γ ≠ τ) (hk : k * T.z * k⁻¹ = τ * γ) :
    ∃ j : G, j * T.z * j⁻¹ = γ := by
  have hγτ' : γ ≠ (T.conjBy u).z := by
    rw [Setting.conjBy_z, ← hτu]
    exact hγτ
  obtain ⟨q, -, hq⟩ := (T.conjBy u).exists_conj_eq_mul_z hγ hγ1 hγτ'
  rw [Setting.conjBy_z, ← hτu] at hq
  have hcomm : γ * τ = τ * γ := by
    have := (T.conjBy u).z_comm_QG hγ
    rwa [Setting.conjBy_z, ← hτu] at this
  refine ⟨q⁻¹ * k, ?_⟩
  calc q⁻¹ * k * T.z * (q⁻¹ * k)⁻¹ = q⁻¹ * (k * T.z * k⁻¹) * q := by group
    _ = q⁻¹ * (q * γ * q⁻¹) * q := by rw [hk, hq, hcomm]
    _ = γ := by group

omit [Finite G] in
theorem exists_conj_of_conj_mul {τ u γ k : G} (hτu : τ = u * T.z * u⁻¹) (hτQ : τ ∉ T.QG)
    (hγ : γ ∈ T.QG ⊓ T.Qa u) (hγ1 : γ ≠ 1) (hk : k * T.z * k⁻¹ = τ * γ) :
    ∃ j : G, j * T.z * j⁻¹ = γ :=
  exists_conj_of_conj_mul' T hτu hγ.2 hγ1 (fun h => hτQ (h ▸ hγ.1)) hk

theorem exists_conj_mul_of_conj_core {τ u α x₁ y : G} (hτM : τ ∈ T.M)
    (hτu : τ = u * T.z * u⁻¹) (hτQ : τ ∉ T.QG) (hα : α ∈ T.QG ⊓ T.Qa u) (hα1 : α ≠ 1)
    (hαz : ∀ j : G, j * T.z * j⁻¹ ≠ α) (hx₁Q : x₁ ∈ T.QG) (hx₁2 : x₁ * x₁ = 1) (hx₁1 : x₁ ≠ 1)
    (hxL : ∀ j : G, j * T.z * j⁻¹ = x₁ → τ ∉ T.La j) (hyα : y * α = α * y)
    (hy : y * τ * y⁻¹ = τ * x₁) :
    ∃ j : G, j * T.z * j⁻¹ = α * x₁ ∧ α ∈ T.Qa j := by
  have hττ : τ * τ = 1 := by rw [hτu]; exact conj_z_mul_self T u
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hτα : α * τ = τ * α := commute_of_mem_Qa_tau (τ := (⟨τ, hτM⟩ : T.M)) hτu hα.2
  set u₁ := y * u with hu₁
  have hτ₁ : u₁ * T.z * u₁⁻¹ = τ * x₁ := by
    rw [← hy, hτu, hu₁]
    group
  have hτ₁τ₁ : τ * x₁ * (τ * x₁) = 1 := by rw [← hτ₁]; exact conj_z_mul_self T u₁
  have hτx : τ * x₁ = x₁ * τ := by
    have h1 : x₁ * τ * x₁ = τ := by
      calc x₁ * τ * x₁ = τ⁻¹ * (τ * x₁ * (τ * x₁)) := by group
        _ = τ := by rw [hτ₁τ₁, mul_one, hτi]
    calc τ * x₁ = x₁ * τ * x₁ * x₁ := by rw [h1]
      _ = x₁ * τ * (x₁ * x₁) := by group
      _ = x₁ * τ := by rw [hx₁2, mul_one]
  have hαu₁ : α ∈ T.Qa u₁ := by
    have := conj_mem_Qa_mul T (h := y) hα.2
    rwa [show y * α * y⁻¹ = α by rw [hyα, mul_inv_cancel_right]] at this
  set T₁ := T.conjBy u₁ with hT₁
  have hT₁z : T₁.z = τ * x₁ := hτ₁
  have hτM₁ : τ ∈ T₁.M := by
    rw [T₁.mem_M_iff, hT₁z]
    calc τ * (τ * x₁) = τ * (x₁ * τ) := by rw [hτx]
      _ = τ * x₁ * τ := by group
  set w := u * u₁⁻¹ with hw
  have hτw : τ = w * T₁.z * w⁻¹ := by
    rw [hT₁z, ← hτ₁, hw, hτu]
    group
  have hQaw : T₁.Qa w = T.Qa u := by
    rw [hT₁, T.Qa_conjBy, hw, inv_mul_cancel_right]
  have hτQa : τ ∈ T.Qa u := hτu ▸ T.conj_z_mem_Qa u
  have hτQ₁ : τ ∉ T₁.QG := by
    intro hτ1
    have hne : u * T.z * u⁻¹ ≠ u₁ * T.z * u₁⁻¹ := by
      rw [← hτu, hτ₁]
      intro h
      apply hx₁1
      calc x₁ = τ⁻¹ * (τ * x₁) := by group
        _ = 1 := by rw [← h, inv_mul_cancel]
    have h1 := T.mem_Qa_symm hne (by rw [← hτu]; exact hτ1)
    rw [hτ₁] at h1
    have hx₁u : x₁ ∈ T.Qa u := by
      have := mul_mem (inv_mem hτQa) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    obtain ⟨j, hj⟩ := exists_conj_of_conj_mul T hτu hτQ ⟨hx₁Q, hx₁u⟩ hx₁1 hτ₁
    have hne' : j * T.z * j⁻¹ ≠ u * T.z * u⁻¹ := by
      rw [hj, ← hτu]
      intro h
      exact hτQ (h ▸ hx₁Q)
    have hτj : τ ∈ T.Qa j := by
      rw [hτu]
      exact T.mem_Qa_symm hne' (hj ▸ hx₁u)
    exact hxL j hj ((L0_le_La T j) ⟨hτj, hτM⟩)
  have hα₁ : α ∈ T₁.QG ⊓ T₁.Qa w := ⟨hαu₁, hQaw ▸ hα.2⟩
  by_cases hU : T₁.cl α ∈ T₁.commQt τ
  · obtain ⟨y₁, -, hy₁α, hy₁⟩ := exists_conj_of_mem_commQt T₁ hτM₁ hτw hτQ₁ hα₁ hU
    rcases hy₁ with h | h
    · exfalso
      obtain ⟨j, hj⟩ := exists_conj_of_conj_mul T hτu hτQ hα hα1 (k := y₁ * u)
        (by rw [← h, hτu]; group)
      exact hαz j hj
    · refine ⟨y₁ * u, ?_, ?_⟩
      · calc y₁ * u * T.z * (y₁ * u)⁻¹ = y₁ * τ * y₁⁻¹ := by rw [hτu]; group
          _ = τ * α * T₁.z := h
          _ = α * (τ * τ) * x₁ := by rw [hT₁z, ← hτα]; group
          _ = α * x₁ := by rw [hττ, mul_one]
      · have := conj_mem_Qa_mul T (h := y₁) hα.2
        rwa [show y₁ * α * y₁⁻¹ = α by rw [hy₁α, mul_inv_cancel_right]] at this
  · obtain ⟨h, -, hhτ, hhα⟩ := exists_conj_of_not_mem_commQt T₁ hτM₁ hτw hτQ₁ hα₁ hU
    exfalso
    have hj : (h * u) * T.z * (h * u)⁻¹ = x₁ := by
      calc (h * u) * T.z * (h * u)⁻¹ = h * τ * h⁻¹ := by rw [hτu]; group
        _ = τ * T₁.z := hhτ
        _ = x₁ := by rw [hT₁z, ← mul_assoc, hττ, one_mul]
    apply hxL (h * u) hj
    have h1 : α * (τ * x₁) ∈ T.Qa (h * u) := by
      have := conj_mem_Qa_mul T (h := h) hα.2
      rwa [hhα, hT₁z] at this
    have h2 : x₁ ∈ T.Qa (h * u) := hj ▸ T.conj_z_mem_Qa (h * u)
    have h3 : α * τ ∈ T.Qa (h * u) := by
      have := mul_mem h1 h2
      rwa [mul_assoc, mul_assoc, hx₁2, mul_one] at this
    have h4 : α * τ ∈ T.M := T.M.mul_mem (T.QG_le_M hα.1) hτM
    rw [show τ = α⁻¹ * (α * τ) by group]
    exact mul_mem ((QG_le_La T _) (inv_mem hα.1)) ((L0_le_La T _) ⟨h3, h4⟩)

theorem exists_conj_mul_of_conj {τ u α x y : G} (hτM : τ ∈ T.M) (hτu : τ = u * T.z * u⁻¹)
    (hτQ : τ ∉ T.QG) (hα : α ∈ T.QG ⊓ T.Qa u) (hα1 : α ≠ 1)
    (hαz : ∀ j : G, j * T.z * j⁻¹ ≠ α) (hxQ : x ∈ T.QG) (hx2 : x * x = 1)
    (hxα : T.cl x ∉ (ZMod 2) ∙ T.cl α)
    (hxL : ∀ j : G, (j * T.z * j⁻¹ = x ∨ j * T.z * j⁻¹ = x * T.z) → τ ∉ T.La j)
    (hyα : y * α = α * y) (hy : y * τ * y⁻¹ = τ * x ∨ y * τ * y⁻¹ = τ * x * T.z) :
    ∃ j : G, j * T.z * j⁻¹ = α * x ∧ α ∈ T.Qa j := by
  have hx0 : T.cl x ≠ 0 := fun h => hxα (h ▸ zero_mem _)
  have hx1 : x ≠ 1 := fun h => hx0 (by rw [h, T.cl_one])
  have hxz : x * T.z ≠ 1 := fun h => hx0 (by
    rw [show x = T.z by
      calc x = x * T.z * T.z := by rw [mul_assoc, T.z_mul_z, mul_one]
        _ = T.z := by rw [h, one_mul]]
    exact T.cl_z)
  rcases hy with h | h
  · exact exists_conj_mul_of_conj_core T hτM hτu hτQ hα hα1 hαz hxQ hx2 hx1
      (fun j hj => hxL j (Or.inl hj)) hyα h
  · have hxz2 : x * T.z * (x * T.z) = 1 := by
      rw [show x * T.z * (x * T.z) = x * x * (T.z * T.z) by
        rw [mul_assoc x, ← mul_assoc T.z, ← T.z_comm_QG hxQ]; group, hx2, T.z_mul_z, one_mul]
    obtain ⟨j, hj, hαj⟩ := exists_conj_mul_of_conj_core T hτM hτu hτQ hα hα1 hαz
      (T.QG.mul_mem hxQ T.z_mem_QG) hxz2 hxz (fun j hj => hxL j (Or.inr hj)) hyα
      (by rw [h, mul_assoc])
    have hxα' : T.cl x ≠ T.cl α := fun e => hxα (e ▸ Submodule.mem_span_singleton_self _)
    obtain ⟨w, hw0, hw1⟩ := T.exists_polar_eq_zero_eq_one hx0 hxα'
    obtain ⟨q, hqQ, rfl⟩ := T.exists_cl w
    have hqα : q * α = α * q := (T.polar_cl_eq_zero_iff hqQ hα.1).mp hw0
    have hqx : q * x * q⁻¹ = x * T.z := by
      have hne : q * x ≠ x * q := (T.polar_cl_eq_one_iff hqQ hxQ).mp hw1
      rcases T.mul_comm_or hqQ hxQ with e | e
      · exact absurd e hne
      · rw [e, show T.z * (x * q) * q⁻¹ = T.z * x by group, T.z_comm_QG hxQ]
    have hqz : q * T.z * q⁻¹ = T.z := by rw [T.z_comm_QG hqQ, mul_inv_cancel_right]
    refine ⟨q * j, ?_, ?_⟩
    · calc q * j * T.z * (q * j)⁻¹ = q * (j * T.z * j⁻¹) * q⁻¹ := by group
        _ = (q * α * q⁻¹) * (q * x * q⁻¹) * (q * T.z * q⁻¹) := by rw [hj]; group
        _ = α * x := by
          rw [hqα, mul_inv_cancel_right, hqx, hqz, mul_assoc α, mul_assoc x, T.z_mul_z, mul_one]
    · have := conj_mem_Qa_mul T (h := q) hαj
      rwa [show q * α * q⁻¹ = α by rw [hqα, mul_inv_cancel_right]] at this

end CFSG.LargeExtraspecial.S11
