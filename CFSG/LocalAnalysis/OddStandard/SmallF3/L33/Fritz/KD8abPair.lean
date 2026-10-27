module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abSide3

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

omit [Finite X] in
theorem conj_fix_of_closure {g : X} {s : Set X} (h : ∀ a ∈ s, g * a * g⁻¹ = a) {e : X}
    (he : e ∈ closure s) : g * e * g⁻¹ = e := by
  have hle : closure s ≤ centralizer ({g} : Set X) := by
    rw [closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have := h a ha
    calc a * g = (g * a * g⁻¹) * g := by rw [this]
      _ = g * a := by group
  have := mem_centralizer_singleton_iff.mp (hle he)
  rw [← this, mul_inv_cancel_right]

namespace ISide

variable (V : ISide S T₁)

theorem yi_comm_t : V.yi * t = t * V.yi := A.commute_t V.yi_mem_T

open Classical in
noncomputable def w₁c : X := if V.D.q0 = .elem then V.w₁N else V.w₁N * V.yi

theorem w₁c_of_elem (h : V.D.q0 = .elem) : V.w₁c = V.w₁N := by unfold w₁c; simp [h]

theorem w₁c_of_homoc (h : V.D.q0 = .homocyclic) : V.w₁c = V.w₁N * V.yi := by
  unfold w₁c; simp [h]

theorem w₁c_eq : V.w₁c = V.w₁N ∨ V.w₁c = V.w₁N * V.yi := by
  rcases V.hq with h | h
  · exact Or.inl (V.w₁c_of_elem h)
  · exact Or.inr (V.w₁c_of_homoc h)

theorem w₁c_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.w₁c * e * V.w₁c⁻¹ = e := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact V.w₁N_conj_E0 he
  · rw [show V.w₁N * V.yi * e * (V.w₁N * V.yi)⁻¹ = V.w₁N * (V.yi * e * V.yi⁻¹) * V.w₁N⁻¹ by
      group, Sec7.conj_eq_of_comm (V.E0_comm V.yi_mem_E0 he), V.w₁N_conj_E0 he]

theorem w₁c_conj_t : V.w₁c * t * V.w₁c⁻¹ = t * S.z := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact V.w₁N_conj_t
  · rw [show V.w₁N * V.yi * t * (V.w₁N * V.yi)⁻¹ = V.w₁N * (V.yi * t * V.yi⁻¹) * V.w₁N⁻¹ by
      group, V.yi_comm_t, mul_inv_cancel_right, V.w₁N_conj_t]

theorem w₁c_comm_u : V.D.u * V.w₁c = V.w₁c * V.D.u := by
  have h : V.D.u * V.w₁c * V.D.u⁻¹ = V.w₁c := by
    rcases V.hq with hq | hq
    · rw [V.w₁c_of_elem hq]; exact V.u_conj_w₁N_of_elem hq
    · rw [V.w₁c_of_homoc hq, show V.D.u * (V.w₁N * V.yi) * V.D.u⁻¹ =
        (V.D.u * V.w₁N * V.D.u⁻¹) * (V.D.u * V.yi * V.D.u⁻¹) by group,
        V.u_conj_w₁N_of_homoc hq, V.u_conj_yi, mul_assoc V.w₁N, ← mul_assoc S.z, zz S,
        one_mul]
  calc V.D.u * V.w₁c = V.D.u * V.w₁c * V.D.u⁻¹ * V.D.u := by group
    _ = V.w₁c * V.D.u := by rw [h]

theorem w₁c_sq : V.w₁c ^ 2 = V.w₁N ^ 2 := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  have hc := V.w₁N_comm_E0 V.yi_mem_E0
  rw [pow_two, pow_two, show V.w₁N * V.yi * (V.w₁N * V.yi) = V.w₁N * (V.yi * V.w₁N) * V.yi by
    group, ← hc, show V.w₁N * (V.w₁N * V.yi) * V.yi = V.w₁N * V.w₁N * (V.yi * V.yi) by group,
    V.yi_sq, mul_one]

theorem w₁c_mem_T₁ : V.w₁c ∈ T₁ := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact V.w₁N_mem_T₁
  · exact mul_mem V.w₁N_mem_T₁ (V.T_le_T₁ V.yi_mem_T)

theorem w₁c_comm_vN_of (hA : V.w₁N * V.vN = V.vN * V.w₁N) : V.w₁c * V.vN = V.vN * V.w₁c := by
  have hy := V.vN_comm_E0 V.yi_mem_E0
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact hA
  · rw [mul_assoc, ← hy, ← mul_assoc, hA, mul_assoc]

theorem w₁c_conj_vN_of (hB : V.w₁N * V.vN * V.w₁N⁻¹ = V.vN * S.z) :
    V.w₁c * V.vN * V.w₁c⁻¹ = V.vN * S.z := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact hB
  · rw [show V.w₁N * V.yi * V.vN * (V.w₁N * V.yi)⁻¹ = V.w₁N * (V.yi * V.vN * V.yi⁻¹) * V.w₁N⁻¹ by
      group, ← V.vN_comm_E0 V.yi_mem_E0, mul_inv_cancel_right, hB]

theorem sq_vN_w₁c :
    (V.w₁N * V.vN = V.vN * V.w₁N → (V.vN * V.w₁c) ^ 2 = V.w₁N ^ 2) ∧
      (V.w₁N * V.vN * V.w₁N⁻¹ = V.vN * S.z → (V.vN * V.w₁c) ^ 2 = S.z * V.w₁N ^ 2) := by
  constructor
  · intro hA
    have hc := V.w₁c_comm_vN_of hA
    rw [← V.w₁c_sq, pow_two, pow_two, show V.vN * V.w₁c * (V.vN * V.w₁c) =
      V.vN * (V.w₁c * V.vN) * V.w₁c by group, hc, show V.vN * (V.vN * V.w₁c) * V.w₁c =
      (V.vN * V.vN) * (V.w₁c * V.w₁c) by group, V.vN_mul_vN, one_mul]
  · intro hB
    have hc := V.w₁c_conj_vN_of hB
    calc (V.vN * V.w₁c) ^ 2 = V.vN * (V.w₁c * V.vN * V.w₁c⁻¹) * (V.w₁c * V.w₁c) := by
          rw [pow_two]; group
      _ = (V.vN * V.vN) * S.z * V.w₁c ^ 2 := by rw [hc, ← pow_two]; group
      _ = S.z * V.w₁N ^ 2 := by rw [V.vN_mul_vN, one_mul, V.w₁c_sq]

end ISide

structure IPair (S : KDBase A C) (T₁ : Subgroup X) where
  V : ISide S T₁
  W : ISide S T₁
  hyy : W.yi = S.x * V.yi ∨ W.yi = S.z * (S.x * V.yi)
  hkk : W.ki = S.z * V.ki

namespace IPair

variable (P : IPair S T₁)

theorem yW_eq : P.W.yi = P.V.D.u ∨ P.W.yi = S.z * P.V.D.u := by
  rw [P.V.hu, P.V.hui]; exact P.hyy

theorem conj_yW_of {g : X} (hz : g * S.z * g⁻¹ = S.z) (hu : g * P.V.D.u * g⁻¹ = P.V.D.u) :
    g * P.W.yi * g⁻¹ = P.W.yi := by
  rcases P.yW_eq with h | h <;> rw [h]
  · exact hu
  · rw [show g * (S.z * P.V.D.u) * g⁻¹ = (g * S.z * g⁻¹) * (g * P.V.D.u * g⁻¹) by group, hz, hu]

theorem conj_kW_of {g : X} (hz : g * S.z * g⁻¹ = S.z) (hk : g * P.V.ki * g⁻¹ = P.V.ki) :
    g * P.W.ki * g⁻¹ = P.W.ki := by
  rw [P.hkk, show g * (S.z * P.V.ki) * g⁻¹ = (g * S.z * g⁻¹) * (g * P.V.ki * g⁻¹) by group, hz, hk]

theorem mem_EW_of {g : X} (hg : g ∈ T₁) (ht : g * t * g⁻¹ = t)
    (hy : g * P.W.yi * g⁻¹ = P.W.yi) : g ∈ S.E P.W.yi := by
  have hgt : g * t = t * g := by
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [ht]
  have hgy : g * P.W.yi = P.W.yi * g := by
    calc g * P.W.yi = (g * P.W.yi * g⁻¹) * g := by group
      _ = P.W.yi * g := by rw [hy]
  exact mem_E_of_mem_T₁ S P.V.h4 P.W.hyi hg hgt hgy

theorem conj_fix_E0W {g : X} (hz : g * S.z * g⁻¹ = S.z) (hy : g * P.W.yi * g⁻¹ = P.W.yi)
    (hk : g * P.W.ki * g⁻¹ = P.W.ki) {e : X} (he : e ∈ S.E0 P.W.yi P.W.ki) : g * e * g⁻¹ = e :=
  conj_fix_of_closure (by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hz
    · exact hy
    · exact hk) he

theorem g_conj_E0W {e : X} (he : e ∈ S.E0 P.W.yi P.W.ki) :
    (P.V.vN * P.V.w₁c) * e * (P.V.vN * P.V.w₁c)⁻¹ = e := by
  have hz : (P.V.vN * P.V.w₁c) * S.z * (P.V.vN * P.V.w₁c)⁻¹ = S.z := by
    rw [show P.V.vN * P.V.w₁c * S.z * (P.V.vN * P.V.w₁c)⁻¹ =
      P.V.vN * (P.V.w₁c * S.z * P.V.w₁c⁻¹) * P.V.vN⁻¹ by group,
      P.V.w₁c_conj_E0 P.V.z_mem_E0, P.V.vN_conj_z]
  have hk : (P.V.vN * P.V.w₁c) * P.V.ki * (P.V.vN * P.V.w₁c)⁻¹ = P.V.ki := by
    rw [show P.V.vN * P.V.w₁c * P.V.ki * (P.V.vN * P.V.w₁c)⁻¹ =
      P.V.vN * (P.V.w₁c * P.V.ki * P.V.w₁c⁻¹) * P.V.vN⁻¹ by group,
      P.V.w₁c_conj_E0 P.V.ki_mem_E0, P.V.vN_conj_ki]
  have hu : (P.V.vN * P.V.w₁c) * P.V.D.u * (P.V.vN * P.V.w₁c)⁻¹ = P.V.D.u := by
    rw [show P.V.vN * P.V.w₁c * P.V.D.u * (P.V.vN * P.V.w₁c)⁻¹ =
      P.V.vN * (P.V.w₁c * P.V.D.u) * P.V.w₁c⁻¹ * P.V.vN⁻¹ by group, ← P.V.w₁c_comm_u,
      show P.V.vN * (P.V.D.u * P.V.w₁c) * P.V.w₁c⁻¹ * P.V.vN⁻¹ = P.V.vN * P.V.D.u * P.V.vN⁻¹ by
        group, ← P.V.u_comm_vN, mul_inv_cancel_right]
  exact P.conj_fix_E0W hz (P.conj_yW_of hz hu) (P.conj_kW_of hz hk) he

theorem g_conj_t : (P.V.vN * P.V.w₁c) * t * (P.V.vN * P.V.w₁c)⁻¹ = t * P.W.ki := by
  have hkz : P.V.ki * S.z = S.z * P.V.ki := P.V.F.kF_comm_z
  rw [show P.V.vN * P.V.w₁c * t * (P.V.vN * P.V.w₁c)⁻¹ =
    P.V.vN * (P.V.w₁c * t * P.V.w₁c⁻¹) * P.V.vN⁻¹ by group, P.V.w₁c_conj_t,
    show P.V.vN * (t * S.z) * P.V.vN⁻¹ = (P.V.vN * t * P.V.vN⁻¹) * (P.V.vN * S.z * P.V.vN⁻¹) by
      group, P.V.vN_conj_t, P.V.vN_conj_z, P.hkk, mul_assoc, hkz]

theorem exists_vW : ∃ c ∈ S.E P.W.yi, P.V.vN * P.V.w₁c = P.W.vN * c := by
  refine ⟨P.W.vN⁻¹ * (P.V.vN * P.V.w₁c), P.mem_EW_of
    (mul_mem (inv_mem P.W.vN_mem_T₁) (mul_mem P.V.vN_mem_T₁ P.V.w₁c_mem_T₁)) ?_ ?_, by group⟩
  · rw [show P.W.vN⁻¹ * (P.V.vN * P.V.w₁c) * t * (P.W.vN⁻¹ * (P.V.vN * P.V.w₁c))⁻¹ =
      P.W.vN⁻¹ * ((P.V.vN * P.V.w₁c) * t * (P.V.vN * P.V.w₁c)⁻¹) * P.W.vN by group,
      P.g_conj_t, ← P.W.vN_conj_t]
    group
  · rw [show P.W.vN⁻¹ * (P.V.vN * P.V.w₁c) * P.W.yi * (P.W.vN⁻¹ * (P.V.vN * P.V.w₁c))⁻¹ =
      P.W.vN⁻¹ * ((P.V.vN * P.V.w₁c) * P.W.yi * (P.V.vN * P.V.w₁c)⁻¹) * P.W.vN by group,
      P.g_conj_E0W P.W.yi_mem_E0]
    calc P.W.vN⁻¹ * P.W.yi * P.W.vN = P.W.vN⁻¹ * (P.W.vN * P.W.yi * P.W.vN⁻¹) * P.W.vN := by
          rw [P.W.vN_conj_yi]
      _ = P.W.yi := by group

theorem vW_conj_EW {c : X} (hc : c ∈ S.E P.W.yi) :
    (c ∈ S.E0 P.W.yi P.W.ki ∧ P.W.vN * c * P.W.vN⁻¹ = c) ∨
      (c * t ∈ S.E0 P.W.yi P.W.ki ∧ P.W.vN * c * P.W.vN⁻¹ = c * P.W.ki) := by
  rcases P.W.F.mem_E0_or hc with h | h
  · exact Or.inl ⟨h, P.W.vN_conj_E0 h⟩
  · refine Or.inr ⟨h, ?_⟩
    have hc' : c = c * t * t := by rw [mul_assoc, tt (A := A), mul_one]
    rw [hc', show P.W.vN * (c * t * t) * P.W.vN⁻¹ = (P.W.vN * (c * t) * P.W.vN⁻¹) *
      (P.W.vN * t * P.W.vN⁻¹) by group, P.W.vN_conj_E0 h, P.W.vN_conj_t, ← mul_assoc]

theorem sq_vW_mul {c : X} (hc : c ∈ S.E P.W.yi) :
    (P.W.vN * c) ^ 2 = 1 ∨ (P.W.vN * c) ^ 2 = P.W.ki := by
  have hE := P.W.F.elemAbelianTwo_E
  have hc2 : c * c = 1 := by rw [← pow_two]; exact hE.sq_eq_one c hc
  have hsq : (P.W.vN * c) ^ 2 = (P.W.vN * c * P.W.vN⁻¹) * c := by
    rw [pow_two, show P.W.vN * c * (P.W.vN * c) = (P.W.vN * c * P.W.vN⁻¹) * (P.W.vN * P.W.vN) * c
      by group, P.W.vN_mul_vN, mul_one]
  rcases P.vW_conj_EW hc with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hsq, h]
  · exact Or.inl hc2
  · right
    have hkc : P.W.ki * c = c * P.W.ki := hE.comm _ (P.W.F.kF_mem_E _) c hc
    rw [mul_assoc, hkc, ← mul_assoc, hc2, one_mul]

theorem z_ne_kW : S.z ≠ 1 ∧ S.z ≠ P.W.ki := by
  refine ⟨z_ne_one S, fun h => P.V.ki_ne_one ?_⟩
  rw [P.hkk] at h
  exact (mul_eq_left.mp h.symm)

theorem option_of_elem (h : P.V.D.q0 = .elem) :
    P.V.D.w₂ * P.V.vN = P.V.vN * P.V.D.w₂ ∧ P.V.w₁N * P.V.vN = P.V.vN * P.V.w₁N := by
  rcases P.V.option with hA | hB
  · exact hA
  · exfalso
    obtain ⟨c, hc, he⟩ := P.exists_vW
    have h1 := P.V.sq_vN_w₁c.2 hB.2
    rw [P.V.w₁N_sq_of_elem h, mul_one, he] at h1
    rcases P.sq_vW_mul hc with h2 | h2 <;> rw [h1] at h2
    · exact P.z_ne_kW.1 h2
    · exact P.z_ne_kW.2 h2

theorem option_of_homoc (h : P.V.D.q0 = .homocyclic) :
    P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹ = P.V.vN * P.V.yi ∧
      P.V.w₁N * P.V.vN * P.V.w₁N⁻¹ = P.V.vN * S.z := by
  rcases P.V.option with hA | hB
  · exfalso
    obtain ⟨c, hc, he⟩ := P.exists_vW
    have h1 := P.V.sq_vN_w₁c.1 hA.2
    rw [P.V.w₁N_sq_of_homoc h, he] at h1
    rcases P.sq_vW_mul hc with h2 | h2 <;> rw [h1] at h2
    · exact P.z_ne_kW.1 h2
    · exact P.z_ne_kW.2 h2
  · exact hB

theorem sq_g : (P.V.vN * P.V.w₁c) ^ 2 = 1 := by
  rcases P.V.hq with h | h
  · rw [P.V.sq_vN_w₁c.1 (P.option_of_elem h).2, P.V.w₁N_sq_of_elem h]
  · rw [P.V.sq_vN_w₁c.2 (P.option_of_homoc h).2, P.V.w₁N_sq_of_homoc h, zz S]

end IPair

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
