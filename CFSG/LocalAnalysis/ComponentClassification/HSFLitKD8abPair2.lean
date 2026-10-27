module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abPair

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace IPair

variable (P : IPair S T₁)

theorem uW_mem_E0V : P.W.D.u ∈ S.E0 P.V.yi P.V.ki := by
  have hx : S.x * S.x = S.z := (pow_two S.x).symm
  rw [P.W.hu, P.W.hui]
  rcases P.hyy with h | h <;> rw [h]
  · rw [← mul_assoc, hx]; exact mul_mem P.V.z_mem_E0 P.V.yi_mem_E0
  · rw [← mul_assoc, z_comm_T S (x_mem_T S), mul_assoc S.z, ← mul_assoc S.x, hx, ← mul_assoc,
      zz S, one_mul]
    exact P.V.yi_mem_E0

theorem mem_zkW_of {e : X} (he : e ∈ S.E0 P.W.yi P.W.ki)
    (hu : P.W.D.u * e * P.W.D.u⁻¹ = e) : e ∈ (zpowers S.z ⊔ zpowers P.W.ki : Subgroup X) := by
  have he' : e ∈ S.E0 P.W.F.yF P.W.F.kF := he
  rw [P.W.F.E0_eq'] at he'
  rcases Sec7.mem_or_of_mem_sup P.W.F.elemAbelianTwo_zk P.W.F.yF_sq
    (fun _ hb => P.W.F.yF_comm_zk hb) he' with h | h
  · exact h
  · exfalso
    change e * P.W.yi ∈ (zpowers S.z ⊔ zpowers P.W.ki : Subgroup X) at h
    have he'' : e = e * P.W.yi * P.W.yi := by rw [mul_assoc, P.W.yi_sq, mul_one]
    rw [he'', show P.W.D.u * (e * P.W.yi * P.W.yi) * P.W.D.u⁻¹ =
      (P.W.D.u * (e * P.W.yi) * P.W.D.u⁻¹) * (P.W.D.u * P.W.yi * P.W.D.u⁻¹) by group,
      P.W.u_conj_B (P.W.zk_le_B h), P.W.u_conj_yi] at hu
    have h2 : e * P.W.yi * (S.z * P.W.yi) = e * P.W.yi * P.W.yi := hu
    exact z_ne_one S (mul_eq_right.mp (mul_left_cancel h2))

theorem exists_w₁W : ∃ c ∈ S.E P.W.yi, P.V.w₁c = P.W.w₁c * c := by
  have hWt : P.W.w₁c⁻¹ * (t * S.z) * P.W.w₁c = t := by
    rw [← P.W.w₁c_conj_t]; group
  have hVy : P.V.w₁c * P.W.yi * P.V.w₁c⁻¹ = P.W.yi :=
    P.conj_yW_of (P.V.w₁c_conj_E0 P.V.z_mem_E0) (by
      rw [← P.V.w₁c_comm_u, mul_inv_cancel_right])
  have hWy : P.W.w₁c⁻¹ * P.W.yi * P.W.w₁c = P.W.yi := by
    have := P.W.w₁c_conj_E0 P.W.yi_mem_E0
    calc P.W.w₁c⁻¹ * P.W.yi * P.W.w₁c =
        P.W.w₁c⁻¹ * (P.W.w₁c * P.W.yi * P.W.w₁c⁻¹) * P.W.w₁c := by rw [this]
      _ = P.W.yi := by group
  refine ⟨P.W.w₁c⁻¹ * P.V.w₁c, P.mem_EW_of
    (mul_mem (inv_mem P.W.w₁c_mem_T₁) P.V.w₁c_mem_T₁) ?_ ?_, by group⟩
  · rw [show P.W.w₁c⁻¹ * P.V.w₁c * t * (P.W.w₁c⁻¹ * P.V.w₁c)⁻¹ =
      P.W.w₁c⁻¹ * (P.V.w₁c * t * P.V.w₁c⁻¹) * P.W.w₁c by group, P.V.w₁c_conj_t, hWt]
  · rw [show P.W.w₁c⁻¹ * P.V.w₁c * P.W.yi * (P.W.w₁c⁻¹ * P.V.w₁c)⁻¹ =
      P.W.w₁c⁻¹ * (P.V.w₁c * P.W.yi * P.V.w₁c⁻¹) * P.W.w₁c by group, hVy, hWy]

theorem sq_w₁W_mul {c : X} (hc : c ∈ S.E P.W.yi) :
    (c ∈ S.E0 P.W.yi P.W.ki ∧ (P.W.w₁c * c) ^ 2 = P.W.w₁c ^ 2) ∨
      (c * t ∈ S.E0 P.W.yi P.W.ki ∧ (P.W.w₁c * c) ^ 2 = P.W.w₁c ^ 2 * S.z) := by
  have hE := P.W.F.elemAbelianTwo_E
  have hc2 : c * c = 1 := by rw [← pow_two]; exact hE.sq_eq_one c hc
  have hsq : (P.W.w₁c * c) ^ 2 = P.W.w₁c ^ 2 * ((P.W.w₁c⁻¹ * c * P.W.w₁c) * c) := by
    rw [pow_two, pow_two]; group
  have hinv : ∀ e ∈ S.E0 P.W.yi P.W.ki, P.W.w₁c⁻¹ * e * P.W.w₁c = e := by
    intro e he
    have := P.W.w₁c_conj_E0 he
    calc P.W.w₁c⁻¹ * e * P.W.w₁c = P.W.w₁c⁻¹ * (P.W.w₁c * e * P.W.w₁c⁻¹) * P.W.w₁c := by
          rw [this]
      _ = e := by group
  rcases P.W.F.mem_E0_or hc with h | h
  · left
    refine ⟨h, ?_⟩
    rw [hsq, hinv c h, hc2, mul_one]
  · right
    refine ⟨h, ?_⟩
    have hWt : P.W.w₁c⁻¹ * t * P.W.w₁c = t * S.z := by
      have h1 := P.W.w₁c_conj_t
      have hz := hinv S.z P.W.z_mem_E0
      calc P.W.w₁c⁻¹ * t * P.W.w₁c = P.W.w₁c⁻¹ * (t * S.z * S.z) * P.W.w₁c := by
            rw [mul_assoc t, zz S, mul_one]
        _ = P.W.w₁c⁻¹ * (P.W.w₁c * t * P.W.w₁c⁻¹) * P.W.w₁c * (P.W.w₁c⁻¹ * S.z * P.W.w₁c) := by
            rw [h1]; group
        _ = t * S.z := by rw [hz]; group
    have hct : c = c * t * t := by rw [mul_assoc, tt (A := A), mul_one]
    rw [hsq, hct, show P.W.w₁c⁻¹ * (c * t * t) * P.W.w₁c =
      (P.W.w₁c⁻¹ * (c * t) * P.W.w₁c) * (P.W.w₁c⁻¹ * t * P.W.w₁c) by group, hinv _ h, hWt,
      ← hct]
    have hzc : S.z * c = c * S.z := hE.comm _ (Frame.z_mem_E _) c hc
    congr 1
    rw [show c * t * (t * S.z) * c = c * (t * t) * S.z * c by group, tt (A := A), mul_one,
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
    exact z_ne_one S (mul_eq_left.mp h2.symm)

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
    have hE := P.W.F.elemAbelianTwo_E
    have hc2 : c * c = 1 := by rw [← pow_two]; exact hE.sq_eq_one c hc
    have hkc : P.W.ki * c = c * P.W.ki := hE.comm _ (P.W.F.kF_mem_E _) c hc
    have : (P.W.vN * c) ^ 2 = P.W.ki := by
      rw [pow_two, show P.W.vN * c * (P.W.vN * c) = (P.W.vN * c * P.W.vN⁻¹) *
        (P.W.vN * P.W.vN) * c by group, P.W.vN_mul_vN, mul_one, h1, mul_assoc, hkc,
        ← mul_assoc, hc2, one_mul]
    rw [this] at hg
    exact P.W.ki_ne_one hg

theorem exists_w₁W_mixed (h : P.V.D.q0 ≠ P.W.D.q0) :
    ∃ c, c * t ∈ S.E0 P.W.yi P.W.ki ∧ P.V.w₁c = P.W.w₁c * c := by
  obtain ⟨c, hc, he⟩ := P.exists_w₁W
  refine ⟨c, ?_, he⟩
  rcases P.sq_w₁W_mul hc with ⟨-, h2⟩ | ⟨h1, -⟩
  · exfalso
    rw [← he, P.V.w₁c_sq, P.W.w₁c_sq] at h2
    rcases P.V.hq with h1 | h1 <;> rcases P.W.hq with h3 | h3
    · exact h (h1.trans h3.symm)
    · rw [P.V.w₁N_sq_of_elem h1, P.W.w₁N_sq_of_homoc h3] at h2
      exact z_ne_one S h2.symm
    · rw [P.V.w₁N_sq_of_homoc h1, P.W.w₁N_sq_of_elem h3] at h2
      exact z_ne_one S h2
    · exact h (h1.trans h3.symm)
  · exact h1

end IPair

end KD8ab

end CFSG.ComponentClassification.HSFLit
