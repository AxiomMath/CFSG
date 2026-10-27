module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Step11

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

namespace Eight

open S6M

namespace E32Conf

variable {X : Type} [Group X] [Finite X] (C : E32Conf X)

omit [Finite X] in
theorem conjugate_one' (A : Subgroup X) : conjugate A 1 = A := by
  ext x
  rw [mem_conjugate_iff]
  simp

section Step12

variable {y : X} (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)
include hyU hyN hyW

theorem conj_E_cases {m : X} (hm : m ∈ normalizer ((C.Q y : Subgroup X) : Set X)) :
    (conjugate C.E m = C.E ∧ conjugate C.E0 m = C.E0) ∨
      (conjugate C.E m = conjugate C.E y ∧ conjugate C.E0 m = conjugate C.E0 y) := by
  have key : ∀ m' : X, m' ∈ normalizer ((C.Q y : Subgroup X) : Set X) →
      conjugate C.E0 m' = C.E0 → conjugate C.E m' = C.E := by
    intro m' hm' h0
    have hle : conjugate C.E m' ≤ C.E := by
      intro x hx
      have hxQ : x ∈ C.Q y := by
        rw [mem_conjugate_iff] at hx
        have := (mem_normalizer_iff.mp (inv_mem hm') _).mp (mem_sup_left hx)
        rwa [show m'⁻¹ * (m' * x * m'⁻¹) * m'⁻¹⁻¹ = x by group] at this
      refine C.mem_E_of_comm_E0 hyU hyN hyW hxQ fun e he => ?_
      have he' : e ∈ conjugate C.E0 m' := by rw [h0]; exact he
      rw [mem_conjugate_iff] at hx he'
      have := C.E_comm hx (C.E0_le_E he')
      calc x * e = m'⁻¹ * ((m' * x * m'⁻¹) * (m' * e * m'⁻¹)) * m' := by group
        _ = m'⁻¹ * ((m' * e * m'⁻¹) * (m' * x * m'⁻¹)) * m' := by rw [this]
        _ = e * x := by group
    exact eq_of_le_of_card_ge hle (by rw [Eight.card_conjugate_eq])
  rcases C.conj_E0_cases hyU hyN hyW hm with h | h
  · exact Or.inl ⟨key m hm h, h⟩
  · right
    have hm' : m * y⁻¹ ∈ normalizer ((C.Q y : Subgroup X) : Set X) :=
      mul_mem hm (inv_mem (C.y_mem_normalizer_Q hyU hyN hyW))
    have h0' : conjugate C.E0 (m * y⁻¹) = C.E0 := by
      rw [← conjugate_conjugate, h, conjugate_conjugate, mul_inv_cancel, conjugate_one']
    have h1 := key _ hm' h0'
    refine ⟨?_, h⟩
    calc conjugate C.E m = conjugate (conjugate C.E (m * y⁻¹)) y := by
          rw [conjugate_conjugate, inv_mul_cancel_right]
      _ = conjugate C.E y := by rw [h1]

abbrev M1 (y : X) : Subgroup X :=
  normalizer ((C.Q y : Subgroup X) : Set X) ⊓ normalizer ((C.E : Subgroup X) : Set X)

theorem conj_Ey_of_mem_M1 {m : X} (hm : m ∈ C.M1 y) : conjugate C.E (y * m) = conjugate C.E y := by
  have hym : y * m ∈ normalizer ((C.Q y : Subgroup X) : Set X) :=
    mul_mem (C.y_mem_normalizer_Q hyU hyN hyW) hm.1
  rcases C.conj_E_cases hyU hyN hyW hym with h | h
  · exfalso
    apply hyW
    refine ⟨hyU, mem_normalizer_of_conjugate_eq ?_⟩
    calc conjugate C.E y = conjugate (conjugate C.E (y * m)) m⁻¹ := by
          rw [conjugate_conjugate, mul_inv_cancel_right]
      _ = conjugate C.E m⁻¹ := by rw [h.1]
      _ = C.E := conjugate_eq_of_mem_normalizer (inv_mem hm.2)
  · exact h.1

theorem conj_y_mem_N {m : X} (hm : m ∈ C.M1 y) : y * m * y⁻¹ ∈ C.N := by
  apply mem_normalizer_of_conjugate_eq
  calc conjugate C.E (y * m * y⁻¹) = conjugate (conjugate C.E (y * m)) y⁻¹ := by
        rw [conjugate_conjugate]
    _ = conjugate (conjugate C.E y) y⁻¹ := by rw [C.conj_Ey_of_mem_M1 hyU hyN hyW hm]
    _ = C.E := by rw [conjugate_conjugate, mul_inv_cancel, conjugate_one']

theorem conj_y_inv_mem_M1 {m : X} (hm : m ∈ C.M1 y) : y⁻¹ * m * y ∈ C.M1 y := by
  have hyQ := C.y_mem_normalizer_Q hyU hyN hyW
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hyQ) (Subgroup.mem_inf.mp hm).1) hyQ,
    mem_normalizer_of_conjugate_eq ?_⟩
  have hy2 : conjugate C.E (y * y) = C.E :=
    conjugate_eq_of_mem_normalizer (C.W_le_normalizer_E (C.sq_mem_W hyU hyN hyW))
  calc conjugate C.E (y⁻¹ * m * y) = conjugate (conjugate (conjugate C.E y⁻¹) m) y := by
        rw [conjugate_conjugate, conjugate_conjugate, mul_assoc]
    _ = conjugate (conjugate (conjugate C.E y) m) y := by
        rw [C.conj_inv_eq hyU hyN hyW C.W_le_normalizer_E]
    _ = conjugate (conjugate C.E y) y := by
        rw [conjugate_conjugate C.E y m, C.conj_Ey_of_mem_M1 hyU hyN hyW hm]
    _ = C.E := by rw [conjugate_conjugate, hy2]

@[expose] noncomputable def χ : ↥(C.M1 y) →* ℤˣ where
  toFun m := Equiv.Perm.sign (C.π ⟨m, m.2.2⟩) *
    Equiv.Perm.sign (C.π ⟨y * m * y⁻¹, C.conj_y_mem_N hyU hyN hyW m.2⟩)
  map_one' := by
    have h1 : (⟨((1 : ↥(C.M1 y)) : X), (1 : ↥(C.M1 y)).2.2⟩ : ↥C.N) = 1 := rfl
    have h2 : (⟨y * ((1 : ↥(C.M1 y)) : X) * y⁻¹,
        C.conj_y_mem_N hyU hyN hyW (1 : ↥(C.M1 y)).2⟩ : ↥C.N) = 1 := by
      apply Subtype.ext
      show y * 1 * y⁻¹ = 1
      group
    rw [h1, h2, map_one, map_one, mul_one]
  map_mul' m₁ m₂ := by
    have h1 : (⟨((m₁ * m₂ : ↥(C.M1 y)) : X), (m₁ * m₂).2.2⟩ : ↥C.N) =
        ⟨(m₁ : X), m₁.2.2⟩ * ⟨(m₂ : X), m₂.2.2⟩ := rfl
    have h2 : (⟨y * ((m₁ * m₂ : ↥(C.M1 y)) : X) * y⁻¹,
        C.conj_y_mem_N hyU hyN hyW (m₁ * m₂).2⟩ : ↥C.N) =
        ⟨y * (m₁ : X) * y⁻¹, C.conj_y_mem_N hyU hyN hyW m₁.2⟩ *
          ⟨y * (m₂ : X) * y⁻¹, C.conj_y_mem_N hyU hyN hyW m₂.2⟩ := by
      apply Subtype.ext
      show y * ((m₁ : X) * m₂) * y⁻¹ = y * m₁ * y⁻¹ * (y * m₂ * y⁻¹)
      group
    rw [h1, h2, map_mul, map_mul, map_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem χ_conj (m : ↥(C.M1 y)) :
    C.χ hyU hyN hyW ⟨y⁻¹ * m * y, C.conj_y_inv_mem_M1 hyU hyN hyW m.2⟩ = C.χ hyU hyN hyW m := by
  have hy2N : y * y ∈ C.N := (C.sq_mem_W hyU hyN hyW).2
  simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk]
  have h1 : (⟨y * (y⁻¹ * (m : X) * y) * y⁻¹,
      C.conj_y_mem_N hyU hyN hyW (C.conj_y_inv_mem_M1 hyU hyN hyW m.2)⟩ : ↥C.N) =
      ⟨(m : X), m.2.2⟩ := by
    apply Subtype.ext
    show y * (y⁻¹ * (m : X) * y) * y⁻¹ = m
    group
  have h2 : (⟨y⁻¹ * (m : X) * y, (C.conj_y_inv_mem_M1 hyU hyN hyW m.2).2⟩ : ↥C.N) =
      (⟨y * y, hy2N⟩ : ↥C.N)⁻¹ * ⟨y * m * y⁻¹, C.conj_y_mem_N hyU hyN hyW m.2⟩ *
        ⟨y * y, hy2N⟩ := by
    apply Subtype.ext
    show y⁻¹ * (m : X) * y = (y * y)⁻¹ * (y * m * y⁻¹) * (y * y)
    group
  have h3 : ∀ a b : ↥C.N, Equiv.Perm.sign (C.π (a⁻¹ * b * a)) = Equiv.Perm.sign (C.π b) := by
    intro a b
    have : Equiv.Perm.sign (C.π (a⁻¹ * b * a)) = (Equiv.Perm.sign (C.π a))⁻¹ *
        Equiv.Perm.sign (C.π b) * Equiv.Perm.sign (C.π a) := by
      simp only [map_mul, map_inv]
    rw [this, mul_comm (Equiv.Perm.sign (C.π a))⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  rw [h1, h2, h3]
  exact mul_comm _ _

theorem sq_mem_M1 : y * y ∈ C.M1 y :=
  Subgroup.mem_inf.mpr ⟨C.W_le_normalizer_Q hyN (C.sq_mem_W hyU hyN hyW),
    (C.sq_mem_W hyU hyN hyW).2⟩

theorem χ_sq_y : C.χ hyU hyN hyW ⟨y * y, C.sq_mem_M1 hyU hyN hyW⟩ = 1 := by
  simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk]
  have h1 : (⟨y * (y * y) * y⁻¹, C.conj_y_mem_N hyU hyN hyW (C.sq_mem_M1 hyU hyN hyW)⟩ : ↥C.N) =
      ⟨y * y, (C.sq_mem_M1 hyU hyN hyW).2⟩ := by
    apply Subtype.ext
    show y * (y * y) * y⁻¹ = y * y
    group
  rw [h1, Int.units_mul_self]

omit hyU hyN hyW in
theorem c4_not_mem_E0 : C.c 4 ∉ C.E0 := by
  rw [← C.θ_ehat]
  intro h
  obtain ⟨v, hv, hve⟩ := C.mem_E0_iff.mp h
  rw [C.θ_inj_iff] at hve
  exact ehat4_odd (hve ▸ hv)

end Step12

end E32Conf

end Eight

end CFSG.ComponentClassification.GSThmB
