module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD7W
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KFacts

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD}

namespace Setup

variable {S : KDBase A C} (P : Setup S)

theorem uw_eq_k {w : X} (hwQ : w ∈ P.Q₀) (hwE : ∀ e ∈ P.E₀, w * e * w⁻¹ = e)
    (hwt : w * t * w⁻¹ = t * S.z) (hw2 : w ^ 2 = P.D.w₁ ^ 2)
    (hf : P.D.u * w * P.D.u⁻¹ * w⁻¹ ∈ zpowers P.F.kF) :
    P.D.u * w * P.D.u⁻¹ * w⁻¹ = P.F.kF := by
  set u := P.D.u with hu
  set f := u * w * u⁻¹ * w⁻¹ with hfdef
  set g := (w * P.D.w₂)⁻¹ * (u * P.D.w₂ * u⁻¹) with hgdef
  have hut : u * t * u⁻¹ = t := Sec7.conj_eq_of_comm P.u_comm_t
  have hA : (u * P.D.w₂ * u⁻¹) * t * (u * P.D.w₂ * u⁻¹)⁻¹ = t * (S.z * P.F.yF) := by
    calc (u * P.D.w₂ * u⁻¹) * t * (u * P.D.w₂ * u⁻¹)⁻¹ =
          u * (P.D.w₂ * (u⁻¹ * t * u) * P.D.w₂⁻¹) * u⁻¹ := by group
      _ = t * (S.z * P.F.yF) := by
        rw [show u⁻¹ * t * u = t by
            calc u⁻¹ * t * u = u⁻¹ * (u * t * u⁻¹) * u := by rw [hut]
              _ = t := by group,
          P.w₂_t, Sec7.conj_mul_eq, hut, P.u_y]
  have hB : (w * P.D.w₂) * t * (w * P.D.w₂)⁻¹ = t * (S.z * P.F.yF) := by
    calc (w * P.D.w₂) * t * (w * P.D.w₂)⁻¹ = w * (P.D.w₂ * t * P.D.w₂⁻¹) * w⁻¹ := by group
      _ = t * (S.z * P.F.yF) := by
        rw [P.w₂_t, Sec7.conj_mul_eq, hwt, hwE _ P.F.yF_mem_E0, mul_assoc]
  have hgt : g * t = t * g := by
    have h1 : (w * P.D.w₂)⁻¹ * (u * P.D.w₂ * u⁻¹) * t * ((w * P.D.w₂)⁻¹ *
        (u * P.D.w₂ * u⁻¹))⁻¹ = t := by
      calc (w * P.D.w₂)⁻¹ * (u * P.D.w₂ * u⁻¹) * t * ((w * P.D.w₂)⁻¹ *
            (u * P.D.w₂ * u⁻¹))⁻¹ = (w * P.D.w₂)⁻¹ * ((u * P.D.w₂ * u⁻¹) * t *
            (u * P.D.w₂ * u⁻¹)⁻¹) * (w * P.D.w₂) := by group
        _ = (w * P.D.w₂)⁻¹ * ((w * P.D.w₂) * t * (w * P.D.w₂)⁻¹) * (w * P.D.w₂) := by
          rw [hA, hB]
        _ = t := by group
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hgdef, h1]
  have hgQ : g ∈ P.Q₀ := mul_mem (inv_mem (mul_mem hwQ P.w₂_mem_Q0)) (P.u_conj_Q₀ P.w₂_mem_Q0)
  have hgE := P.mem_E0_of_mem_Q0 hgQ hgt
  have huw : u * w * u⁻¹ = f * w := by rw [hfdef]; group
  have huu : u * u = 1 := P.u_mul_u
  have hw₂ : P.D.w₂ = f * w * (w * P.D.w₂ * g) * (u * g * u⁻¹) := by
    calc P.D.w₂ = u * (u * P.D.w₂ * u⁻¹) * u⁻¹ := by
          rw [show u * (u * P.D.w₂ * u⁻¹) * u⁻¹ = (u * u) * P.D.w₂ * (u * u)⁻¹ by group,
            huu]
          group
      _ = (u * w * u⁻¹) * (u * P.D.w₂ * u⁻¹) * (u * g * u⁻¹) := by rw [hgdef]; group
      _ = f * w * (w * P.D.w₂ * g) * (u * g * u⁻¹) := by rw [huw, hgdef]; group
  have hguE := P.u_conj_E0 hgE
  have hc1 : P.D.w₂ * (g * (u * g * u⁻¹)) = (g * (u * g * u⁻¹)) * P.D.w₂ :=
    (P.comm_of_mem_E0 (mul_mem hgE hguE) P.w₂_mem_Q0).symm
  have h2 : 1 * P.D.w₂ = (f * w ^ 2 * (g * (u * g * u⁻¹))) * P.D.w₂ := by
    rw [one_mul]
    conv_lhs => rw [hw₂]
    rw [pow_two]
    calc f * w * (w * P.D.w₂ * g) * (u * g * u⁻¹) = f * (w * w) * (P.D.w₂ *
          (g * (u * g * u⁻¹))) := by group
      _ = _ := by rw [hc1]; group
  have key : f * w ^ 2 * (g * (u * g * u⁻¹)) = 1 := (mul_right_cancel h2).symm
  have hfv : f = 1 ∨ f = P.F.kF := eq_one_or_eq_of_mem_zpowers P.F.kF_sq hf
  have hw1sq : P.D.w₁ ^ 2 = P.F.kF ∨ P.D.w₁ ^ 2 = S.z * P.F.kF := by
    have h := P.D.q0_holds
    rcases P.hq with hq | hq <;> rw [hq] at h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hk1 : P.F.kF ≠ 1 := P.F.kF_ne_one
  have hzk1 : S.z * P.F.kF ≠ 1 := fun h =>
    P.F.kF_not_mem_L (by rw [eq_inv_of_mul_eq_one_right h]; exact inv_mem (z_mem_L S))
  have hkz : P.F.kF * S.z = S.z * P.F.kF := P.F.kF_comm_z
  rw [hw2] at key
  have hf' : f = (P.D.w₁ ^ 2 * (g * (u * g * u⁻¹)))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact key)
  have hkk : P.F.kF⁻¹ = P.F.kF := P.F.kF_inv
  have hzkzk : (S.z * P.F.kF) * (S.z * P.F.kF) = 1 := by
    rw [mul_assoc, ← mul_assoc P.F.kF, hkz, mul_assoc, P.F.kF_kF, mul_one, zz S]
  rcases P.mul_u_conj_mem hgE with hg1 | hg1 <;> rw [hg1] at hf' <;>
    rcases hw1sq with hs | hs <;> rw [hs] at hf'
  · rw [hf', mul_one, hkk]
  · exfalso
    rw [mul_one, inv_eq_of_mul_eq_one_right hzkzk] at hf'
    rcases hfv with hf1 | hf1 <;> rw [hf1] at hf'
    · exact hzk1 hf'.symm
    · exact z_ne_one S (by simpa using hf'.symm)
  · exfalso
    rw [hkz, inv_eq_of_mul_eq_one_right hzkzk] at hf'
    rcases hfv with hf1 | hf1 <;> rw [hf1] at hf'
    · exact hzk1 hf'.symm
    · exact z_ne_one S (by simpa using hf'.symm)
  · rw [hf', show S.z * P.F.kF * S.z = P.F.kF by
      rw [mul_assoc, hkz, ← mul_assoc, zz S, one_mul], hkk]

theorem uw₁_mem_E0 : P.D.u * P.D.w₁ * P.D.u⁻¹ * P.D.w₁⁻¹ ∈ P.E₀ := by
  refine P.mem_E0_of_mem_Q0 (mul_mem (P.u_conj_Q₀ P.w₁_mem_Q0) (inv_mem P.w₁_mem_Q0)) ?_
  exact ((mem_centralizer_iff.mp P.D.u_comm_w₁) t (Frame.t_mem_E _)).symm

theorem exists_w₁' : ∃ w : X, (w = P.D.w₁ ∨ w = P.F.yF * P.D.w₁) ∧
    P.D.u * w * P.D.u⁻¹ * w⁻¹ = P.F.kF := by
  set u := P.D.u with hu
  set w₁ := P.D.w₁ with hw₁
  set f := u * w₁ * u⁻¹ * w₁⁻¹ with hf
  have hfE : f ∈ P.E₀ := P.uw₁_mem_E0
  have hfix : u * f * u⁻¹ = f := by
    have huu : u * u = 1 := P.u_mul_u
    have hinv : u⁻¹ = u := P.u_inv
    have h1 : u * f * u⁻¹ = f⁻¹ := by
      calc u * f * u⁻¹ = (u * u) * w₁ * u⁻¹ * w₁⁻¹ * u⁻¹ := by rw [hf]; group
        _ = w₁ * u⁻¹ * w₁⁻¹ * u⁻¹ := by rw [huu, one_mul]
        _ = w₁ * u * w₁⁻¹ * u⁻¹ := by rw [hinv]
        _ = f⁻¹ := by rw [hf]; group
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (by
      rw [← pow_two]; exact P.F.elemAbelianTwo_E0.sq_eq_one f hfE)
  have hfzk := P.mem_zk_of_mem_E0 hfE hfix
  rw [sup_comm] at hfzk
  have hkel : ElemAbelianTwo (zpowers P.F.kF) := elemAbelianTwo_zpowers P.F.kF_sq
  have hw1t := P.w₁_t
  rcases Sec7.mem_or_of_mem_sup hkel (z_sq S) (fun a ha =>
      (P.F.elemAbelianTwo_zk.comm S.z (mem_sup_left (mem_zpowers _)) a
        (mem_sup_right ha))) hfzk with h | h
  · exact ⟨w₁, Or.inl rfl, P.uw_eq_k P.w₁_mem_Q0 (fun e he => P.w₁_E0 he) hw1t rfl h⟩
  · refine ⟨P.F.yF * w₁, Or.inr rfl, P.uw_eq_k (mul_mem (P.E0_le_Q0 P.F.yF_mem_E0)
      P.w₁_mem_Q0) (fun e he => ?_) ?_ ?_ ?_⟩
    · rw [show P.F.yF * w₁ * e * (P.F.yF * w₁)⁻¹ = P.F.yF * (w₁ * e * w₁⁻¹) * P.F.yF⁻¹ by
        group, P.w₁_E0 he]
      exact Sec7.conj_eq_of_comm (P.F.comm_E0 P.F.yF_mem_E0 he)
    · rw [show P.F.yF * w₁ * t * (P.F.yF * w₁)⁻¹ = P.F.yF * (w₁ * t * w₁⁻¹) * P.F.yF⁻¹ by
        group, hw1t]
      exact Sec7.conj_eq_of_comm (Sec7.comm_mul_of (P.F.t_comm_E0 P.F.yF_mem_E0).symm
        (P.F.comm_E0 P.F.yF_mem_E0 P.F.z_mem_E0))
    · rw [pow_two, pow_two, show P.F.yF * w₁ * (P.F.yF * w₁) = P.F.yF * (w₁ * P.F.yF) * w₁ by
        group, ← P.comm_of_mem_E0 P.F.yF_mem_E0 P.w₁_mem_Q0, ← mul_assoc, P.F.yF_yF, one_mul]
    · have hcalc : u * (P.F.yF * w₁) * u⁻¹ * (P.F.yF * w₁)⁻¹ = f * S.z := by
        calc u * (P.F.yF * w₁) * u⁻¹ * (P.F.yF * w₁)⁻¹ =
              (u * P.F.yF * u⁻¹) * f * P.F.yF⁻¹ := by rw [hf]; group
          _ = S.z * P.F.yF * f * P.F.yF⁻¹ := by rw [P.u_y]
          _ = f * S.z := by
            rw [mul_assoc S.z, P.F.comm_E0 P.F.yF_mem_E0 hfE, ← mul_assoc, mul_assoc _ P.F.yF,
              mul_inv_cancel, mul_one, P.F.comm_E0 P.F.z_mem_E0 hfE]
      rw [hcalc]
      exact h

noncomputable def w₁' : X := Classical.choose P.exists_w₁'

theorem w₁'_eq : P.w₁' = P.D.w₁ ∨ P.w₁' = P.F.yF * P.D.w₁ :=
  (Classical.choose_spec P.exists_w₁').1

theorem u_w₁' : P.D.u * P.w₁' * P.D.u⁻¹ * P.w₁'⁻¹ = P.F.kF :=
  (Classical.choose_spec P.exists_w₁').2

theorem w₁'_E0 {e : X} (he : e ∈ P.E₀) : P.w₁' * e * P.w₁'⁻¹ = e := by
  rcases P.w₁'_eq with h | h <;> rw [h]
  · exact P.w₁_E0 he
  · rw [show P.F.yF * P.D.w₁ * e * (P.F.yF * P.D.w₁)⁻¹ =
      P.F.yF * (P.D.w₁ * e * P.D.w₁⁻¹) * P.F.yF⁻¹ by group, P.w₁_E0 he]
    exact Sec7.conj_eq_of_comm (P.F.comm_E0 P.F.yF_mem_E0 he)

theorem w₁'_t : P.w₁' * t * P.w₁'⁻¹ = t * S.z := by
  rcases P.w₁'_eq with h | h <;> rw [h]
  · exact P.w₁_t
  · rw [show P.F.yF * P.D.w₁ * t * (P.F.yF * P.D.w₁)⁻¹ =
      P.F.yF * (P.D.w₁ * t * P.D.w₁⁻¹) * P.F.yF⁻¹ by group, P.w₁_t]
    exact Sec7.conj_eq_of_comm (Sec7.comm_mul_of (P.F.t_comm_E0 P.F.yF_mem_E0).symm
      (P.F.comm_E0 P.F.yF_mem_E0 P.F.z_mem_E0))

theorem w₁'_u : P.w₁' * P.D.u * P.w₁'⁻¹ = P.F.kF * P.D.u := by
  calc P.w₁' * P.D.u * P.w₁'⁻¹ = (P.D.u * P.w₁' * P.D.u⁻¹ * P.w₁'⁻¹)⁻¹ * P.D.u := by
        group
    _ = P.F.kF * P.D.u := by rw [P.u_w₁', P.F.kF_inv]

theorem u_cases : (∃ c ∈ zpowers S.z, P.D.u = c * (P.F.xF * P.F.yF)) ∨
    (∃ c ∈ zpowers S.z, P.D.u = c * t * (P.F.xF * P.F.yF)) := by
  rcases P.D.u_eq with h | h <;> rcases P.hui with h' | h'
  · exact Or.inl ⟨1, one_mem _, by rw [h, h', one_mul]⟩
  · exact Or.inl ⟨S.z, mem_zpowers _, by rw [h, h']⟩
  · exact Or.inr ⟨1, one_mem _, by rw [h, h', one_mul]⟩
  · refine Or.inr ⟨S.z, mem_zpowers _, ?_⟩
    rw [h, h', ← mul_assoc, (A.commute_t (z_mem_T S)).symm]

theorem w₁'_xy : P.w₁' * (P.F.xF * P.F.yF) * P.w₁'⁻¹ = P.F.kF * (P.F.xF * P.F.yF) ∨
    P.w₁' * (P.F.xF * P.F.yF) * P.w₁'⁻¹ = S.z * P.F.kF * (P.F.xF * P.F.yF) := by
  have hwu := P.w₁'_u
  have hcz : ∀ c ∈ zpowers S.z, P.w₁' * c * P.w₁'⁻¹ = c := fun c hc =>
    P.w₁'_E0 ((zpowers_le.mpr P.F.z_mem_E0) hc)
  have hcT : ∀ c ∈ zpowers S.z, c ∈ A.T := fun c hc => zpowers_le.mpr (z_mem_T S) hc
  rcases P.u_cases with ⟨c, hc, hu⟩ | ⟨c, hc, hu⟩
  · left
    have hxy : P.F.xF * P.F.yF = c⁻¹ * P.D.u := by rw [hu]; group
    conv_lhs => rw [hxy]
    rw [Sec7.conj_mul_eq, hwu, show P.w₁' * c⁻¹ * P.w₁'⁻¹ = (P.w₁' * c * P.w₁'⁻¹)⁻¹ by group,
      hcz c hc, ← mul_assoc, (comm_zpowers_z S P.F.kF_mem_T (inv_mem hc)).symm, mul_assoc,
      ← hxy]
  · right
    have hxy : P.F.xF * P.F.yF = (c * t)⁻¹ * P.D.u := by rw [hu]; group
    have hct : P.w₁' * (c * t) * P.w₁'⁻¹ = c * t * S.z := by
      rw [Sec7.conj_mul_eq, hcz c hc, P.w₁'_t, mul_assoc]
    conv_lhs => rw [hxy]
    rw [Sec7.conj_mul_eq, hwu, show P.w₁' * (c * t)⁻¹ * P.w₁'⁻¹ =
      (P.w₁' * (c * t) * P.w₁'⁻¹)⁻¹ by group, hct, hu]
    have hkc : P.F.kF * c = c * P.F.kF := comm_zpowers_z S P.F.kF_mem_T hc
    have hkt : P.F.kF * t = t * P.F.kF := P.F.kF_comm_t
    calc (c * t * S.z)⁻¹ * (P.F.kF * (c * t * (P.F.xF * P.F.yF))) =
          S.z⁻¹ * t⁻¹ * c⁻¹ * (P.F.kF * c * t) * (P.F.xF * P.F.yF) := by group
      _ = S.z⁻¹ * t⁻¹ * c⁻¹ * (c * t * P.F.kF) * (P.F.xF * P.F.yF) := by
          rw [hkc, mul_assoc c, hkt]; group
      _ = S.z⁻¹ * P.F.kF * (P.F.xF * P.F.yF) := by group
      _ = S.z * P.F.kF * (P.F.xF * P.F.yF) := by rw [z_inv S]

theorem w₁'_normalizes : P.w₁' ∈ normalizer (S.E (P.F.xF * P.F.yF) : Set X) := by
  have hxyE : P.F.xF * P.F.yF ∈ S.E (P.F.xF * P.F.yF) := Frame.yi_mem_E _
  have hzE : S.z ∈ S.E (P.F.xF * P.F.yF) := Frame.z_mem_E _
  have hkE : P.F.kF ∈ S.E (P.F.xF * P.F.yF) := P.F.kF_mem_E _
  show P.w₁' ∈ normalizer (L2E S.z (P.F.xF * P.F.yF) t S.k : Set X)
  refine L2K.mem_normalizer_L2E ?_ ?_ ?_ ?_
  · rw [P.w₁'_E0 P.F.z_mem_E0]; exact hzE
  · rcases P.w₁'_xy with h | h <;> rw [h]
    · exact mul_mem hkE hxyE
    · exact mul_mem (mul_mem hzE hkE) hxyE
  · rw [P.w₁'_t]; exact mul_mem (Frame.t_mem_E _) hzE
  · rw [P.w₁'_E0 P.F.k_mem_E0]; exact Frame.k_mem_E _

theorem w₁'_xy_not_mem_L : P.w₁' * (P.F.xF * P.F.yF) * P.w₁'⁻¹ ∉ L := by
  have hxyL : P.F.xF * P.F.yF ∈ L := P.F.xyF_mem_R.2
  intro h
  apply P.F.kF_not_mem_L
  rcases P.w₁'_xy with h' | h' <;> rw [h'] at h
  · have := mul_mem h (inv_mem hxyL)
    rwa [mul_inv_cancel_right] at this
  · have := mul_mem (inv_mem (z_mem_L S)) (mul_mem h (inv_mem hxyL))
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at this

end Setup

end KD7

end CFSG.ComponentClassification.HSFLit
