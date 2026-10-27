module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8ISide

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

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

variable (V : ISide S F T₁)

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
      group, conj_eq_of_comm' (V.E0_comm (yi_mem_E0 _ _) he), V.w₁N_conj_E0 he]

theorem w₁c_conj_t : V.w₁c * S.t * V.w₁c⁻¹ = S.t * S.z := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact V.w₁N_conj_t
  · rw [show V.w₁N * V.yi * S.t * (V.w₁N * V.yi)⁻¹ = V.w₁N * (V.yi * S.t * V.yi⁻¹) * V.w₁N⁻¹ by
      group, V.hyi.comm_B t_mem_B, mul_inv_cancel_right, V.w₁N_conj_t]

theorem w₁c_comm_u : V.D.u * V.w₁c = V.w₁c * V.D.u := by
  have h : V.D.u * V.w₁c * V.D.u⁻¹ = V.w₁c := by
    rcases V.hq with hq | hq
    · rw [V.w₁c_of_elem hq]; exact V.u_conj_w₁N_of_elem hq
    · rw [V.w₁c_of_homoc hq, show V.D.u * (V.w₁N * V.yi) * V.D.u⁻¹ =
        (V.D.u * V.w₁N * V.D.u⁻¹) * (V.D.u * V.yi * V.D.u⁻¹) by group,
        V.u_conj_w₁N_of_homoc hq, V.u_conj_yi, mul_assoc V.w₁N, ← mul_assoc S.z, z_mul_z,
        one_mul]
  calc V.D.u * V.w₁c = V.D.u * V.w₁c * V.D.u⁻¹ * V.D.u := by group
    _ = V.w₁c * V.D.u := by rw [h]

theorem w₁c_sq : V.w₁c ^ 2 = V.w₁N ^ 2 := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  have hc := V.w₁N_comm_E0 (yi_mem_E0 V.yi V.ki)
  rw [pow_two, pow_two, show V.w₁N * V.yi * (V.w₁N * V.yi) = V.w₁N * (V.yi * V.w₁N) * V.yi by
    group, ← hc, show V.w₁N * (V.w₁N * V.yi) * V.yi = V.w₁N * V.w₁N * (V.yi * V.yi) by group,
    V.yi_sq, mul_one]

theorem w₁c_mem_T₁ : V.w₁c ∈ T₁ := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact V.w₁N_mem_T₁
  · exact mul_mem V.w₁N_mem_T₁ (V.T_le_T₁ V.hyi.mem_T)

theorem w₁c_comm_vN_of (hA : V.w₁N * V.vN = V.vN * V.w₁N) : V.w₁c * V.vN = V.vN * V.w₁c := by
  have hy := V.vN_comm_E0 (yi_mem_E0 V.yi V.ki)
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact hA
  · rw [mul_assoc, ← hy, ← mul_assoc, hA, mul_assoc]

theorem w₁c_conj_vN_of (hB : V.w₁N * V.vN * V.w₁N⁻¹ = V.vN * S.z) :
    V.w₁c * V.vN * V.w₁c⁻¹ = V.vN * S.z := by
  rcases V.w₁c_eq with h | h <;> rw [h]
  · exact hB
  · rw [show V.w₁N * V.yi * V.vN * (V.w₁N * V.yi)⁻¹ = V.w₁N * (V.yi * V.vN * V.yi⁻¹) * V.w₁N⁻¹ by
      group, ← V.vN_comm_E0 (yi_mem_E0 V.yi V.ki), mul_inv_cancel_right, hB]

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

structure IPair (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  V : ISide S F T₁
  W : ISide S F T₁
  hyy : W.yi = F.xF * V.yi ∨ W.yi = S.z * (F.xF * V.yi)
  hkk : W.ki = S.z * V.ki
  h4 : S.Sec4 F T₁

namespace IPair

variable (P : IPair S F T₁)

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

theorem mem_EW_of {g : X} (hg : g ∈ T₁) (ht : g * S.t * g⁻¹ = S.t)
    (hy : g * P.W.yi * g⁻¹ = P.W.yi) : g ∈ S.E P.W.yi := by
  have hgt : g * S.t = S.t * g := by
    calc g * S.t = (g * S.t * g⁻¹) * g := by group
      _ = S.t * g := by rw [ht]
  have hgT := S.data.mem_T_of_commute P.h4.isPGroup P.h4.le hg hgt
  refine P.W.hyi.mem_E_of_comm hgT ?_
  calc g * P.W.yi = (g * P.W.yi * g⁻¹) * g := by group
    _ = P.W.yi * g := by rw [hy]

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
      P.V.w₁c_conj_E0 (z_mem_E0 _ _), P.V.vN_conj_z]
  have hk : (P.V.vN * P.V.w₁c) * P.V.ki * (P.V.vN * P.V.w₁c)⁻¹ = P.V.ki := by
    rw [show P.V.vN * P.V.w₁c * P.V.ki * (P.V.vN * P.V.w₁c)⁻¹ =
      P.V.vN * (P.V.w₁c * P.V.ki * P.V.w₁c⁻¹) * P.V.vN⁻¹ by group,
      P.V.w₁c_conj_E0 (ki_mem_E0 _ _), P.V.vN_conj_ki]
  have hu : (P.V.vN * P.V.w₁c) * P.V.D.u * (P.V.vN * P.V.w₁c)⁻¹ = P.V.D.u := by
    rw [show P.V.vN * P.V.w₁c * P.V.D.u * (P.V.vN * P.V.w₁c)⁻¹ =
      P.V.vN * (P.V.w₁c * P.V.D.u) * P.V.w₁c⁻¹ * P.V.vN⁻¹ by group, ← P.V.w₁c_comm_u,
      show P.V.vN * (P.V.D.u * P.V.w₁c) * P.V.w₁c⁻¹ * P.V.vN⁻¹ = P.V.vN * P.V.D.u * P.V.vN⁻¹ by
        group, ← P.V.u_comm_vN, mul_inv_cancel_right]
  exact P.conj_fix_E0W hz (P.conj_yW_of hz hu) (P.conj_kW_of hz hk) he

theorem g_conj_t : (P.V.vN * P.V.w₁c) * S.t * (P.V.vN * P.V.w₁c)⁻¹ = S.t * P.W.ki := by
  rw [show P.V.vN * P.V.w₁c * S.t * (P.V.vN * P.V.w₁c)⁻¹ =
    P.V.vN * (P.V.w₁c * S.t * P.V.w₁c⁻¹) * P.V.vN⁻¹ by group, P.V.w₁c_conj_t,
    show P.V.vN * (S.t * S.z) * P.V.vN⁻¹ = (P.V.vN * S.t * P.V.vN⁻¹) * (P.V.vN * S.z * P.V.vN⁻¹) by
      group, P.V.vN_conj_t, P.V.vN_conj_z, P.hkk, mul_assoc, ki_comm_z P.V.hki]

theorem exists_vW : ∃ c ∈ S.E P.W.yi, P.V.vN * P.V.w₁c = P.W.vN * c := by
  refine ⟨P.W.vN⁻¹ * (P.V.vN * P.V.w₁c), P.mem_EW_of
    (mul_mem (inv_mem P.W.vN_mem_T₁) (mul_mem P.V.vN_mem_T₁ P.V.w₁c_mem_T₁)) ?_ ?_, by group⟩
  · rw [show P.W.vN⁻¹ * (P.V.vN * P.V.w₁c) * S.t * (P.W.vN⁻¹ * (P.V.vN * P.V.w₁c))⁻¹ =
      P.W.vN⁻¹ * ((P.V.vN * P.V.w₁c) * S.t * (P.V.vN * P.V.w₁c)⁻¹) * P.W.vN by group,
      P.g_conj_t, ← P.W.vN_conj_t]
    group
  · rw [show P.W.vN⁻¹ * (P.V.vN * P.V.w₁c) * P.W.yi * (P.W.vN⁻¹ * (P.V.vN * P.V.w₁c))⁻¹ =
      P.W.vN⁻¹ * ((P.V.vN * P.V.w₁c) * P.W.yi * (P.V.vN * P.V.w₁c)⁻¹) * P.W.vN by group,
      P.g_conj_E0W (yi_mem_E0 _ _)]
    calc P.W.vN⁻¹ * P.W.yi * P.W.vN = P.W.vN⁻¹ * (P.W.vN * P.W.yi * P.W.vN⁻¹) * P.W.vN := by
          rw [P.W.vN_conj_yi]
      _ = P.W.yi := by group

theorem vW_conj_EW {c : X} (hc : c ∈ S.E P.W.yi) :
    (c ∈ S.E0 P.W.yi P.W.ki ∧ P.W.vN * c * P.W.vN⁻¹ = c) ∨
      (c * S.t ∈ S.E0 P.W.yi P.W.ki ∧ P.W.vN * c * P.W.vN⁻¹ = c * P.W.ki) := by
  rcases P.W.hyi.mem_E0_or P.W.hki hc with h | h
  · exact Or.inl ⟨h, P.W.vN_conj_E0 h⟩
  · refine Or.inr ⟨h, ?_⟩
    have hc' : c = c * S.t * S.t := by rw [mul_assoc, t_mul_t, mul_one]
    rw [hc', show P.W.vN * (c * S.t * S.t) * P.W.vN⁻¹ = (P.W.vN * (c * S.t) * P.W.vN⁻¹) *
      (P.W.vN * S.t * P.W.vN⁻¹) by group, P.W.vN_conj_E0 h, P.W.vN_conj_t, ← mul_assoc]

theorem sq_vW_mul {c : X} (hc : c ∈ S.E P.W.yi) :
    (P.W.vN * c) ^ 2 = 1 ∨ (P.W.vN * c) ^ 2 = P.W.ki := by
  have hE := P.W.hyi.elemAbelianTwo_E
  have hc2 : c * c = 1 := by rw [← pow_two]; exact hE.sq_eq_one c hc
  have hsq : (P.W.vN * c) ^ 2 = (P.W.vN * c * P.W.vN⁻¹) * c := by
    rw [pow_two, show P.W.vN * c * (P.W.vN * c) = (P.W.vN * c * P.W.vN⁻¹) * (P.W.vN * P.W.vN) * c
      by group, P.W.vN_mul_vN, mul_one]
  rcases P.vW_conj_EW hc with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hsq, h]
  · exact Or.inl hc2
  · right
    rw [mul_assoc, hE.comm _ (B_le_E _ P.W.hki.mem) c hc, ← mul_assoc, hc2, one_mul]

theorem z_ne_kW : S.z ≠ 1 ∧ S.z ≠ P.W.ki := by
  refine ⟨S.z_ne_one, fun h => P.V.hki.ne_one ?_⟩
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
  · rw [P.V.sq_vN_w₁c.2 (P.option_of_homoc h).2, P.V.w₁N_sq_of_homoc h, z_mul_z]

theorem uW_mem_E0V : P.W.D.u ∈ S.E0 P.V.yi P.V.ki := by
  have hx : F.xF * F.xF = S.z := by rw [← pow_two, F.xF_sq]
  rw [P.W.hu, P.W.hui]
  rcases P.hyy with h | h <;> rw [h]
  · rw [← mul_assoc, hx]; exact mul_mem (z_mem_E0 _ _) (yi_mem_E0 _ _)
  · rw [← mul_assoc, ← S.central_of_mem_B z_mem_B (xF_mem_T F), mul_assoc S.z, ← mul_assoc F.xF,
      hx, ← mul_assoc, z_mul_z, one_mul]
    exact yi_mem_E0 _ _

theorem mem_zkW_of {e : X} (he : e ∈ S.E0 P.W.yi P.W.ki)
    (hu : P.W.D.u * e * P.W.D.u⁻¹ = e) : e ∈ (zpowers S.z ⊔ zpowers P.W.ki : Subgroup X) := by
  rw [E0_eq] at he
  rcases mem_or_of_mem_sup (elemAbelianTwo_zk P.W.hki) P.W.hyi.sq
    (fun _ hb => P.W.hyi.comm_B (zk_le_B P.W.hki hb)) he with h | h
  · exact h
  · exfalso
    have he' : e = e * P.W.yi * P.W.yi := by rw [mul_assoc, P.W.yi_sq, mul_one]
    rw [he', show P.W.D.u * (e * P.W.yi * P.W.yi) * P.W.D.u⁻¹ =
      (P.W.D.u * (e * P.W.yi) * P.W.D.u⁻¹) * (P.W.D.u * P.W.yi * P.W.D.u⁻¹) by group,
      P.W.u_conj_B (zk_le_B P.W.hki h), P.W.u_conj_yi] at hu
    have h2 : e * P.W.yi * (S.z * P.W.yi) = e * P.W.yi * P.W.yi := hu
    exact S.z_ne_one (mul_eq_right.mp (mul_left_cancel h2))

theorem exists_w₁W : ∃ c ∈ S.E P.W.yi, P.V.w₁c = P.W.w₁c * c := by
  have hWt : P.W.w₁c⁻¹ * (S.t * S.z) * P.W.w₁c = S.t := by
    rw [← P.W.w₁c_conj_t]; group
  have hVy : P.V.w₁c * P.W.yi * P.V.w₁c⁻¹ = P.W.yi :=
    P.conj_yW_of (P.V.w₁c_conj_E0 (z_mem_E0 _ _)) (by
      rw [← P.V.w₁c_comm_u, mul_inv_cancel_right])
  have hWy : P.W.w₁c⁻¹ * P.W.yi * P.W.w₁c = P.W.yi := by
    have := P.W.w₁c_conj_E0 (yi_mem_E0 P.W.yi P.W.ki)
    calc P.W.w₁c⁻¹ * P.W.yi * P.W.w₁c =
        P.W.w₁c⁻¹ * (P.W.w₁c * P.W.yi * P.W.w₁c⁻¹) * P.W.w₁c := by rw [this]
      _ = P.W.yi := by group
  refine ⟨P.W.w₁c⁻¹ * P.V.w₁c, P.mem_EW_of
    (mul_mem (inv_mem P.W.w₁c_mem_T₁) P.V.w₁c_mem_T₁) ?_ ?_, by group⟩
  · rw [show P.W.w₁c⁻¹ * P.V.w₁c * S.t * (P.W.w₁c⁻¹ * P.V.w₁c)⁻¹ =
      P.W.w₁c⁻¹ * (P.V.w₁c * S.t * P.V.w₁c⁻¹) * P.W.w₁c by group, P.V.w₁c_conj_t, hWt]
  · rw [show P.W.w₁c⁻¹ * P.V.w₁c * P.W.yi * (P.W.w₁c⁻¹ * P.V.w₁c)⁻¹ =
      P.W.w₁c⁻¹ * (P.V.w₁c * P.W.yi * P.V.w₁c⁻¹) * P.W.w₁c by group, hVy, hWy]

theorem sq_w₁W_mul {c : X} (hc : c ∈ S.E P.W.yi) :
    (c ∈ S.E0 P.W.yi P.W.ki ∧ (P.W.w₁c * c) ^ 2 = P.W.w₁c ^ 2) ∨
      (c * S.t ∈ S.E0 P.W.yi P.W.ki ∧ (P.W.w₁c * c) ^ 2 = P.W.w₁c ^ 2 * S.z) := by
  have hE := P.W.hyi.elemAbelianTwo_E
  have hc2 : c * c = 1 := by rw [← pow_two]; exact hE.sq_eq_one c hc
  have hsq : (P.W.w₁c * c) ^ 2 = P.W.w₁c ^ 2 * ((P.W.w₁c⁻¹ * c * P.W.w₁c) * c) := by
    rw [pow_two, pow_two]; group
  have hinv : ∀ e ∈ S.E0 P.W.yi P.W.ki, P.W.w₁c⁻¹ * e * P.W.w₁c = e := by
    intro e he
    have := P.W.w₁c_conj_E0 he
    calc P.W.w₁c⁻¹ * e * P.W.w₁c = P.W.w₁c⁻¹ * (P.W.w₁c * e * P.W.w₁c⁻¹) * P.W.w₁c := by
          rw [this]
      _ = e := by group
  rcases P.W.hyi.mem_E0_or P.W.hki hc with h | h
  · left
    refine ⟨h, ?_⟩
    rw [hsq, hinv c h, hc2, mul_one]
  · right
    refine ⟨h, ?_⟩
    have hWt : P.W.w₁c⁻¹ * S.t * P.W.w₁c = S.t * S.z := by
      have h1 := P.W.w₁c_conj_t
      have hz := hinv S.z (z_mem_E0 _ _)
      calc P.W.w₁c⁻¹ * S.t * P.W.w₁c = P.W.w₁c⁻¹ * (S.t * S.z * S.z) * P.W.w₁c := by
            rw [mul_assoc S.t, z_mul_z, mul_one]
        _ = P.W.w₁c⁻¹ * (P.W.w₁c * S.t * P.W.w₁c⁻¹) * P.W.w₁c * (P.W.w₁c⁻¹ * S.z * P.W.w₁c) := by
            rw [h1]; group
        _ = S.t * S.z := by rw [hz]; group
    have hct : c = c * S.t * S.t := by rw [mul_assoc, t_mul_t, mul_one]
    rw [hsq, hct, show P.W.w₁c⁻¹ * (c * S.t * S.t) * P.W.w₁c =
      (P.W.w₁c⁻¹ * (c * S.t) * P.W.w₁c) * (P.W.w₁c⁻¹ * S.t * P.W.w₁c) by group, hinv _ h, hWt,
      ← hct]
    have hzc : S.z * c = c * S.z := hE.comm _ (z_mem_E _) c hc
    congr 1
    rw [show c * S.t * (S.t * S.z) * c = c * (S.t * S.t) * S.z * c by group, t_mul_t, mul_one,
      mul_assoc, hzc, ← mul_assoc, hc2, one_mul]

theorem conj_uW_of_conj {g : X} (hg : g * P.W.D.u * g⁻¹ = P.W.D.u) :
    P.W.D.u * g * P.W.D.u⁻¹ = g := by
  have h : P.W.D.u * g = g * P.W.D.u := by
    calc P.W.D.u * g = (g * P.W.D.u * g⁻¹) * g := by rw [hg]
      _ = g * P.W.D.u := by group
  rw [h, mul_inv_cancel_right]

theorem exists_w₁W_same (h : P.V.D.q0 = P.W.D.q0) :
    ∃ c ∈ (zpowers S.z ⊔ zpowers P.W.ki : Subgroup X), P.V.w₁c = P.W.w₁c * c := by
  obtain ⟨c, hc, he⟩ := P.exists_w₁W
  have hsq : P.V.w₁c ^ 2 = P.W.w₁c ^ 2 := by
    rw [P.V.w₁c_sq, P.W.w₁c_sq]
    rcases P.V.hq with h1 | h1
    · rw [P.V.w₁N_sq_of_elem h1, P.W.w₁N_sq_of_elem (h ▸ h1)]
    · rw [P.V.w₁N_sq_of_homoc h1, P.W.w₁N_sq_of_homoc (h ▸ h1)]
  refine ⟨c, ?_, he⟩
  rcases P.sq_w₁W_mul hc with ⟨h0, -⟩ | ⟨-, h2⟩
  · refine P.mem_zkW_of h0 ?_
    have hc' : c = P.W.w₁c⁻¹ * P.V.w₁c := by rw [he]; group
    have hV := P.conj_uW_of_conj (P.V.w₁c_conj_E0 P.uW_mem_E0V)
    have hW : P.W.D.u * P.W.w₁c⁻¹ * P.W.D.u⁻¹ = P.W.w₁c⁻¹ := by
      rw [show P.W.D.u * P.W.w₁c⁻¹ * P.W.D.u⁻¹ = (P.W.D.u * P.W.w₁c * P.W.D.u⁻¹)⁻¹ by group,
        P.W.w₁c_comm_u, mul_inv_cancel_right]
    rw [hc', show P.W.D.u * (P.W.w₁c⁻¹ * P.V.w₁c) * P.W.D.u⁻¹ =
      (P.W.D.u * P.W.w₁c⁻¹ * P.W.D.u⁻¹) * (P.W.D.u * P.V.w₁c * P.W.D.u⁻¹) by group, hW, hV]
  · exfalso
    rw [← he, hsq] at h2
    exact S.z_ne_one (mul_eq_left.mp h2.symm)

theorem exists_vW_zk : ∃ c ∈ (zpowers S.z ⊔ zpowers P.W.ki : Subgroup X),
    P.V.vN * P.V.w₁c = P.W.vN * c := by
  obtain ⟨c, hc, he⟩ := P.exists_vW
  refine ⟨c, ?_, he⟩
  have hg := P.sq_g
  rw [he] at hg
  rcases P.vW_conj_EW hc with ⟨h0, -⟩ | ⟨-, h1⟩
  · refine P.mem_zkW_of h0 ?_
    have hc' : c = P.W.vN⁻¹ * (P.V.vN * P.V.w₁c) := by rw [he]; group
    have hV : (P.V.vN * P.V.w₁c) * P.W.D.u * (P.V.vN * P.V.w₁c)⁻¹ = P.W.D.u := by
      rw [show P.V.vN * P.V.w₁c * P.W.D.u * (P.V.vN * P.V.w₁c)⁻¹ =
        P.V.vN * (P.V.w₁c * P.W.D.u * P.V.w₁c⁻¹) * P.V.vN⁻¹ by group,
        P.V.w₁c_conj_E0 P.uW_mem_E0V, P.V.vN_conj_E0 P.uW_mem_E0V]
    have hV' := P.conj_uW_of_conj hV
    have hW : P.W.D.u * P.W.vN⁻¹ * P.W.D.u⁻¹ = P.W.vN⁻¹ := by
      rw [show P.W.D.u * P.W.vN⁻¹ * P.W.D.u⁻¹ = (P.W.D.u * P.W.vN * P.W.D.u⁻¹)⁻¹ by group,
        P.W.u_comm_vN, mul_inv_cancel_right]
    rw [hc', show P.W.D.u * (P.W.vN⁻¹ * (P.V.vN * P.V.w₁c)) * P.W.D.u⁻¹ =
      (P.W.D.u * P.W.vN⁻¹ * P.W.D.u⁻¹) * (P.W.D.u * (P.V.vN * P.V.w₁c) * P.W.D.u⁻¹) by group,
      hW, hV']
  · exfalso
    have hE := P.W.hyi.elemAbelianTwo_E
    have hc2 : c * c = 1 := by rw [← pow_two]; exact hE.sq_eq_one c hc
    have : (P.W.vN * c) ^ 2 = P.W.ki := by
      rw [pow_two, show P.W.vN * c * (P.W.vN * c) = (P.W.vN * c * P.W.vN⁻¹) *
        (P.W.vN * P.W.vN) * c by group, P.W.vN_mul_vN, mul_one, h1, mul_assoc,
        hE.comm _ (B_le_E _ P.W.hki.mem) c hc, ← mul_assoc, hc2, one_mul]
    rw [this] at hg
    exact P.W.hki.ne_one hg

theorem exists_w₁W_mixed (h : P.V.D.q0 ≠ P.W.D.q0) :
    ∃ c, c * S.t ∈ S.E0 P.W.yi P.W.ki ∧ P.V.w₁c = P.W.w₁c * c := by
  obtain ⟨c, hc, he⟩ := P.exists_w₁W
  refine ⟨c, ?_, he⟩
  rcases P.sq_w₁W_mul hc with ⟨-, h2⟩ | ⟨h1, -⟩
  · exfalso
    rw [← he, P.V.w₁c_sq, P.W.w₁c_sq] at h2
    rcases P.V.hq with h1 | h1 <;> rcases P.W.hq with h3 | h3
    · exact h (h1.trans h3.symm)
    · rw [P.V.w₁N_sq_of_elem h1, P.W.w₁N_sq_of_homoc h3] at h2
      exact S.z_ne_one h2.symm
    · rw [P.V.w₁N_sq_of_homoc h1, P.W.w₁N_sq_of_elem h3] at h2
      exact S.z_ne_one h2
    · exact h (h1.trans h3.symm)
  · exact h1

end IPair

end Sec8

end CFSG.ComponentClassification.HSFLit
