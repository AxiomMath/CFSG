module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2h

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

abbrev tau : X := S.t * C.D₁.u

theorem ut : C.D₁.u * S.t = S.t * C.D₁.u := C.u_comm_B t_mem_B

theorem u_t : C.D₁.u * S.t * C.D₁.u⁻¹ = S.t := conj_eq_of_comm C.ut

theorem tau_mem : C.tau ∈ C.S₂ := mul_mem C.t_mem_S₂ C.u_mem_S₂

theorem tau_N : C.tau ∈ normalizer (C.D₁.Q₁ : Set X) := C.S₂_le C.tau_mem

theorem tau_tau : C.tau * C.tau = 1 := by
  rw [show S.t * C.D₁.u * (S.t * C.D₁.u) = S.t * (C.D₁.u * S.t) * C.D₁.u by group, C.ut,
    show S.t * (S.t * C.D₁.u) * C.D₁.u = (S.t * S.t) * (C.D₁.u * C.D₁.u) by group, tt S,
    C.u_mul_u, one_mul]

theorem tau_inv : C.tau⁻¹ = C.tau := inv_eq_of_mul_eq_one_right C.tau_tau

theorem tau_t : C.tau * S.t * C.tau⁻¹ = S.t := by
  rw [show C.tau * S.t * C.tau⁻¹ = S.t * (C.D₁.u * S.t * C.D₁.u⁻¹) * S.t⁻¹ by group, C.u_t,
    mul_inv_cancel_right]

theorem tau_E0 {e : X} (he : e ∈ C.E₀) : C.tau * e * C.tau⁻¹ = C.D₁.u * e * C.D₁.u⁻¹ := by
  rw [show C.tau * e * C.tau⁻¹ = S.t * (C.D₁.u * e * C.D₁.u⁻¹) * S.t⁻¹ by group,
    conj_eq_of_comm (C.t_comm_E0 (C.u_conj_E0 he))]

theorem tau_y : C.tau * C.F.yF * C.tau⁻¹ = S.z * C.F.yF := by rw [C.tau_E0 C.y_mem_E0, C.u_y]

theorem tau_z : C.tau * S.z * C.tau⁻¹ = S.z := by rw [C.tau_E0 C.z_mem_E0, C.u_z]

theorem tau_k : C.tau * C.F.kF * C.tau⁻¹ = C.F.kF := by rw [C.tau_E0 C.k_mem_E0, C.u_k]

theorem tau_v' : C.tau * C.v' * C.tau⁻¹ = C.F.kF * C.v' := by
  rw [show C.tau * C.v' * C.tau⁻¹ = S.t * (C.D₁.u * C.v' * C.D₁.u⁻¹) * S.t⁻¹ by group, C.u_v',
    C.t_v']

theorem tau_act_E₁ : act C.tau C.E₁ = C.E₁ := by
  rw [act_mul, C.u_E₁, C.act_Q₁_E₁ C.t_mem_Q₁]

theorem tau_act_G₁ : act C.tau C.G₁ = C.G₁ := by
  rw [act_mul, C.u_G₁, C.act_Q₁ C.t_mem_Q₁ C.r₁_mem]

theorem tau_act_G₂ : act C.tau C.G₂ = C.G₃ := by
  rw [act_mul, C.u_G₂', C.act_Q₁ C.t_mem_Q₁ C.r₃_mem]

theorem tau_act_G₃ : act C.tau C.G₃ = C.G₂ := by
  rw [act_mul, C.u_G₃', C.act_Q₁ C.t_mem_Q₁ C.r₂_mem]

theorem alpha_one : alpha S 1 = 1 := by rw [alpha_def]; group

theorem alpha_Fv {f : X} (hf : f ∈ C.Fv) : alpha S f = 1 ∨ alpha S f = C.F.kF := by
  rcases mem_or_of_mem_sup_zpowers (C.normalizes_E0_of_mem_Q₁ C.v'_mem_Q₁) C.v'_sq_mem_E0 hf with
    h | h
  · exact Or.inl (C.alpha_of_mem_E0 h)
  · right
    rw [show f = f * C.v'⁻¹ * C.v' by group, C.alpha_mul (C.E0_le_Q₁ h) C.v'_mem_Q₁,
      C.alpha_of_mem_E0 h, one_mul, C.alpha_v']

theorem mem_Fv_of_alpha {x : X} (hx : x ∈ C.D₁.Q₁) (hxv : x * C.v' = C.v' * x)
    (hα : alpha S x = 1 ∨ alpha S x = C.F.kF) : x ∈ C.Fv := by
  rcases hα with h | h
  · exact mem_sup_left (C.mem_E0_of_comm_v' (C.mem_E₁_of_comm_t hx (alpha_eq_one_iff.mp h)) hxv)
  · have hx' : x * C.v' ∈ C.D₁.Q₁ := mul_mem hx C.v'_mem_Q₁
    have hα' : alpha S (x * C.v') = 1 := by rw [C.alpha_mul hx C.v'_mem_Q₁, h, C.alpha_v', C.kk]
    have hv' : x * C.v' * C.v' = C.v' * (x * C.v') := by rw [← mul_assoc, ← hxv]
    have hE := C.mem_E0_of_comm_v' (C.mem_E₁_of_comm_t hx' (alpha_eq_one_iff.mp hα')) hv'
    rw [show x = x * C.v' * C.v'⁻¹ by group]
    exact mul_mem (mem_sup_left hE) (inv_mem (mem_sup_right (mem_zpowers _)))

theorem mem_Zz_of_tau {f : X} (hf : f ∈ C.Fv) (h : C.tau * f * C.tau⁻¹ = f) : f ∈ C.Zz := by
  have hel := C.isRefl_y.elemAbelianTwo_E0 C.isK_k
  rcases mem_or_of_mem_sup_zpowers (C.normalizes_E0_of_mem_Q₁ C.v'_mem_Q₁) C.v'_sq_mem_E0 hf with
    he | he
  · rw [C.tau_E0 he] at h
    exact C.mem_zk_of_mem_E0 he h
  · exfalso
    obtain ⟨e, he', rfl⟩ : ∃ e ∈ C.E₀, f = e * C.v' := ⟨_, he, by group⟩
    rw [conj_mul_eq, C.tau_E0 he', C.tau_v'] at h
    have h3 : C.D₁.u * e * C.D₁.u⁻¹ * C.F.kF = e :=
      mul_right_cancel (show (C.D₁.u * e * C.D₁.u⁻¹ * C.F.kF) * C.v' = e * C.v' by
        rw [← h]; group)
    have h1 : C.D₁.u * e * C.D₁.u⁻¹ = e * C.F.kF := by
      calc C.D₁.u * e * C.D₁.u⁻¹ = C.D₁.u * e * C.D₁.u⁻¹ * C.F.kF * C.F.kF := by
            rw [mul_assoc _ C.F.kF C.F.kF, C.kk, mul_one]
        _ = e * C.F.kF := by rw [h3]
    rcases C.mul_u_conj_mem he' with h4 | h4 <;>
      rw [h1, ← mul_assoc, ← pow_two, hel.sq_eq_one e he', one_mul] at h4
    · exact C.ne_one_k h4
    · exact C.k_not_mem_zpowers_z (h4 ▸ mem_zpowers _)

theorem sq_mul_tau {b : X} (h2 : (b * C.tau) ^ 2 = 1) : b * (C.tau * b * C.tau⁻¹) = 1 := by
  rw [C.tau_inv, ← h2, pow_two]; group

theorem mem_Zz_of_Fv_tau {f : X} (hf : f ∈ C.Fv) (h2 : (f * C.tau) ^ 2 = 1) : f ∈ C.Zz := by
  refine C.mem_Zz_of_tau hf ?_
  have h := C.sq_mul_tau h2
  have hf2 : f * f = 1 := by rw [← pow_two]; exact C.Fv_sq hf
  calc C.tau * f * C.tau⁻¹ = f * f * (C.tau * f * C.tau⁻¹) := by rw [hf2, one_mul]
    _ = f := by rw [mul_assoc, h, mul_one]

theorem alpha_tau_mul {b : X} (hb : b ∈ C.D₁.Q₁) (h2 : (b * C.tau) ^ 2 = 1) :
    alpha S b * (C.tau * alpha S b * C.tau⁻¹) = 1 := by
  rw [← alpha_conj S C.tau_t, ← C.alpha_mul hb (C.conj_mem_Q₁ C.tau_N hb), C.sq_mul_tau h2,
    alpha_one]

theorem E0_yzy : C.F.yF * (S.z * C.F.yF) = S.z := by
  rw [← mul_assoc, C.yz, mul_assoc, C.yy, mul_one]

theorem E0_kykzy : C.F.kF * C.F.yF * (C.F.kF * (S.z * C.F.yF)) = S.z := by
  calc C.F.kF * C.F.yF * (C.F.kF * (S.z * C.F.yF)) =
        C.F.kF * (C.F.yF * C.F.kF) * (S.z * C.F.yF) := by group
    _ = C.F.kF * (C.F.kF * C.F.yF) * (S.z * C.F.yF) := by rw [C.ky]
    _ = (C.F.kF * C.F.kF) * (C.F.yF * (S.z * C.F.yF)) := by group
    _ = S.z := by rw [C.kk, one_mul, C.E0_yzy]

theorem E0_zyzzy : S.z * C.F.yF * (S.z * (S.z * C.F.yF)) = S.z := by
  calc S.z * C.F.yF * (S.z * (S.z * C.F.yF)) = S.z * C.F.yF * ((S.z * S.z) * C.F.yF) := by group
    _ = S.z := by rw [zz S, one_mul, mul_assoc, C.yy, mul_one]

theorem E0_kzykzzy : C.F.kF * (S.z * C.F.yF) * (C.F.kF * (S.z * (S.z * C.F.yF))) = S.z := by
  have hc : S.z * C.F.yF * C.F.kF = C.F.kF * (S.z * C.F.yF) := by
    rw [mul_assoc, ← C.ky, ← mul_assoc, ← C.kz, mul_assoc]
  calc C.F.kF * (S.z * C.F.yF) * (C.F.kF * (S.z * (S.z * C.F.yF))) =
        C.F.kF * (S.z * C.F.yF * C.F.kF) * ((S.z * S.z) * C.F.yF) := by group
    _ = (C.F.kF * C.F.kF) * (S.z * C.F.yF) * C.F.yF := by rw [hc, zz S, one_mul]; group
    _ = S.z := by rw [C.kk, one_mul, mul_assoc, C.yy, mul_one]

theorem not_case₂ {f : X} (hf : f ∈ C.Fv) (hb : f * C.D₁.w₂ ∈ C.D₁.Q₁)
    (h2 : (f * C.D₁.w₂ * C.tau) ^ 2 = 1) : False := by
  have h := C.alpha_tau_mul hb h2
  rw [C.alpha_mul (C.Fv_le_Q₁ hf) C.w₂_mem_Q₁, C.alpha_w₂, conj_mul_eq, C.tau_y] at h
  rcases C.alpha_Fv hf with ha | ha <;> rw [ha] at h
  · rw [show C.tau * 1 * C.tau⁻¹ = 1 by group, one_mul, one_mul, C.E0_yzy] at h
    exact S.z_ne_one h
  · rw [C.tau_k, C.E0_kykzy] at h
    exact S.z_ne_one h

theorem not_case₃ {f : X} (hf : f ∈ C.Fv) (hb : f * (C.w₁' * C.D₁.w₂) ∈ C.D₁.Q₁)
    (h2 : (f * (C.w₁' * C.D₁.w₂) * C.tau) ^ 2 = 1) : False := by
  have h := C.alpha_tau_mul hb h2
  rw [C.alpha_mul (C.Fv_le_Q₁ hf) (mul_mem C.w₁'_mem_Q₁ C.w₂_mem_Q₁),
    C.alpha_mul C.w₁'_mem_Q₁ C.w₂_mem_Q₁, C.alpha_w₁', C.alpha_w₂, conj_mul_eq, conj_mul_eq,
    C.tau_y, C.tau_z] at h
  rcases C.alpha_Fv hf with ha | ha <;> rw [ha] at h
  · rw [show C.tau * 1 * C.tau⁻¹ = 1 by group, one_mul, one_mul, C.E0_zyzzy] at h
    exact S.z_ne_one h
  · rw [C.tau_k, C.E0_kzykzzy] at h
    exact S.z_ne_one h

theorem exists_conj_B {b : X} (hb : b ∈ C.D₁.Q₁) (hbv : b * C.v' = C.v' * b)
    (h2 : (b * C.tau) ^ 2 = 1) : ∃ h : X, ∃ c ∈ C.Zz, h * (b * C.tau) * h⁻¹ = c * C.tau := by
  rcases C.mem_B_cases hb hbv with h | h | h | h
  · exact ⟨1, b, C.mem_Zz_of_Fv_tau h h2, by group⟩
  · obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, b = f * C.w₁' := ⟨_, h, by group⟩
    set b'' := C.D₁.w₂⁻¹ * (f * C.w₁') * (C.tau * C.D₁.w₂ * C.tau⁻¹) with hb''
    have e : C.D₁.w₂⁻¹ * (f * C.w₁' * C.tau) * C.D₁.w₂⁻¹⁻¹ = b'' * C.tau := by
      rw [hb'']; group
    have hwτ := C.conj_mem_Q₁ C.tau_N C.w₂_mem_Q₁
    have hb''Q : b'' ∈ C.D₁.Q₁ := mul_mem (mul_mem (inv_mem C.w₂_mem_Q₁) hb) hwτ
    have hwv : (C.tau * C.D₁.w₂ * C.tau⁻¹) * C.v' = C.v' * (C.tau * C.D₁.w₂ * C.tau⁻¹) := by
      have h1 : C.tau⁻¹ * C.v' * C.tau = C.F.kF * C.v' := by
        rw [C.tau_inv]
        calc C.tau * C.v' * C.tau = C.tau * C.v' * C.tau⁻¹ := by rw [C.tau_inv]
          _ = C.F.kF * C.v' := C.tau_v'
      have h2 : C.D₁.w₂ * (C.F.kF * C.v') = (C.F.kF * C.v') * C.D₁.w₂ := by
        rw [← mul_assoc, C.w₂_comm_E0 C.k_mem_E0, mul_assoc, C.w₂_v', ← mul_assoc]
      calc C.tau * C.D₁.w₂ * C.tau⁻¹ * C.v' =
            C.tau * (C.D₁.w₂ * (C.tau⁻¹ * C.v' * C.tau)) * C.tau⁻¹ := by group
        _ = C.tau * ((C.tau⁻¹ * C.v' * C.tau) * C.D₁.w₂) * C.tau⁻¹ := by rw [h1, h2]
        _ = C.v' * (C.tau * C.D₁.w₂ * C.tau⁻¹) := by group
    have hb''v : b'' * C.v' = C.v' * b'' := by
      have c1 : Commute C.D₁.w₂⁻¹ C.v' := (show Commute C.D₁.w₂ C.v' from C.w₂_v').inv_left
      have c2 : Commute (f * C.w₁') C.v' := hbv
      have c3 : Commute (C.tau * C.D₁.w₂ * C.tau⁻¹) C.v' := hwv
      exact ((c1.mul_left c2).mul_left c3).eq
    have hα : alpha S b'' = 1 ∨ alpha S b'' = C.F.kF := by
      rw [hb'', C.alpha_mul (mul_mem (inv_mem C.w₂_mem_Q₁) hb) hwτ,
        C.alpha_mul (inv_mem C.w₂_mem_Q₁) hb, C.alpha_inv C.w₂_mem_Q₁, C.alpha_w₂,
        C.alpha_mul (C.Fv_le_Q₁ hf) C.w₁'_mem_Q₁, C.alpha_w₁', alpha_conj S C.tau_t, C.alpha_w₂,
        C.tau_y]
      rcases C.alpha_Fv hf with ha | ha <;> rw [ha]
      · left
        rw [show C.F.yF⁻¹ * (1 * S.z) * (S.z * C.F.yF) = C.F.yF⁻¹ * (S.z * S.z) * C.F.yF by group,
          zz S]
        group
      · right
        rw [show C.F.yF⁻¹ * (C.F.kF * S.z) * (S.z * C.F.yF) =
          C.F.yF⁻¹ * C.F.kF * (S.z * S.z) * C.F.yF by group, zz S, mul_one, mul_assoc, C.ky]
        group
    have hb''F := C.mem_Fv_of_alpha hb''Q hb''v hα
    have h2'' : (b'' * C.tau) ^ 2 = 1 := by
      rw [← e, show (C.D₁.w₂⁻¹ * (f * C.w₁' * C.tau) * C.D₁.w₂⁻¹⁻¹) ^ 2 =
        C.D₁.w₂⁻¹ * (f * C.w₁' * C.tau) ^ 2 * C.D₁.w₂⁻¹⁻¹ by rw [pow_two, pow_two]; group, h2]
      group
    exact ⟨C.D₁.w₂⁻¹, b'', C.mem_Zz_of_Fv_tau hb''F h2'', e⟩
  · exfalso
    obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, b = f * C.D₁.w₂ := ⟨_, h, by group⟩
    exact C.not_case₂ hf hb h2
  · exfalso
    obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, b = f * (C.w₁' * C.D₁.w₂) := ⟨_, h, by group⟩
    exact C.not_case₃ hf hb h2

omit [Finite X] in
theorem act_sq_eq {c : X} (h2 : c ^ 2 = 1) (A : Subgroup X) : act c (act c A) = A := by
  rw [← act_mul, ← pow_two, h2, act_one_eq]

theorem exists_conj_Zz_tau {s : X} (hs : s ∈ C.Q₂₀) (h2 : (s * C.tau) ^ 2 = 1) :
    ∃ h : X, ∃ c ∈ C.Zz, h * (s * C.tau) * h⁻¹ = c * C.tau := by
  obtain ⟨-, a0, a1, a2, a3, -, -⟩ := C.q₁_spec
  obtain ⟨-, b0, b2, b1, b3, -, -⟩ := C.q₂_spec
  have hvF : C.v' ∈ C.Fv := mem_sup_right (mem_zpowers _)
  obtain ⟨w, hw, hwa | hwa⟩ := C.mem_S₂_cases hs.1
  swap
  · exfalso
    obtain ⟨a, ha, hsa⟩ : ∃ a ∈ C.D₁.Q₁, s = w * a * C.D₁.u := ⟨_, hwa, by group⟩
    have hy := C.Q₂₀_F hs (mem_sup_left C.y_mem_E0)
    rw [hsa, show w * a * C.D₁.u * C.F.yF * (w * a * C.D₁.u)⁻¹ =
      w * (a * (C.D₁.u * C.F.yF * C.D₁.u⁻¹) * a⁻¹) * w⁻¹ by group, C.u_y,
      C.conj_eq_of_mem_Q₁ ha (mul_mem C.z_mem_E0 C.y_mem_E0),
      C.W_F hw (mem_sup_left (mul_mem C.z_mem_E0 C.y_mem_E0))] at hy
    exact S.z_ne_one (by simpa using hy)
  obtain ⟨a, ha, hsa⟩ : ∃ a ∈ C.D₁.Q₁, s = w * a := ⟨_, hwa, by group⟩
  clear hwa
  have hav : a * C.v' = C.v' * a := by
    have h1 : a * C.v' * a⁻¹ = C.v' := by
      have hs' := C.Q₂₀_F hs hvF
      rw [hsa, show w * a * C.v' * (w * a)⁻¹ = w * (a * C.v' * a⁻¹) * w⁻¹ by group] at hs'
      calc a * C.v' * a⁻¹ = w⁻¹ * (w * (a * C.v' * a⁻¹) * w⁻¹) * w := by group
        _ = w⁻¹ * (w * C.v' * w⁻¹) * w := by rw [hs', C.W_F hw hvF]
        _ = C.v' := by group
    calc a * C.v' = a * C.v' * a⁻¹ * a := by group
      _ = C.v' * a := by rw [h1]
  rcases hw with rfl | rfl | rfl | rfl
  · rw [one_mul] at hsa
    subst hsa
    exact C.exists_conj_B ha hav h2
  ·
    subst hsa
    set b' := C.q₂⁻¹ * (C.q₁ * a) * (C.tau * C.q₂ * C.tau⁻¹) with hb'
    have e : C.q₂⁻¹ * (C.q₁ * a * C.tau) * C.q₂⁻¹⁻¹ = b' * C.tau := by rw [hb']; group
    have hb'S : b' ∈ C.S₂ := mul_mem (mul_mem (inv_mem C.q₂_mem) (mul_mem C.q₁_mem
      (C.Q₁_le_S₂ ha))) (mul_mem (mul_mem C.tau_mem C.q₂_mem) (inv_mem C.tau_mem))
    have hb'Q : b' ∈ C.D₁.Q₁ := by
      refine C.mem_Q₁_of_fix hb'S ?_ ?_
      · rw [hb', act_mul, act_mul, act_mul, act_mul, act_mul, C.tau_inv, C.tau_act_E₁, b0,
          C.tau_act_G₂, C.act_Q₁ ha C.r₃_mem, a3, act_inv_eq b0]
      · rw [hb', act_mul, act_mul, act_mul, act_mul, act_mul, C.tau_inv, C.tau_act_G₂, b3,
          C.tau_act_G₁, C.act_Q₁ ha C.r₁_mem, a1, act_inv_eq b2]
    have hb'v : b' * C.v' = C.v' * b' := by
      have c1 : Commute C.q₂⁻¹ C.v' := (show Commute C.q₂ C.v' by
        calc C.q₂ * C.v' = C.q₂ * C.v' * C.q₂⁻¹ * C.q₂ := by group
          _ = C.v' * C.q₂ := by rw [C.q₂_F hvF]).inv_left
      have c2 : Commute (C.q₁ * a) C.v' := by
        refine Commute.mul_left ?_ hav
        calc C.q₁ * C.v' = C.q₁ * C.v' * C.q₁⁻¹ * C.q₁ := by group
          _ = C.v' * C.q₁ := by rw [C.q₁_F hvF]
      have c3 : Commute (C.tau * C.q₂ * C.tau⁻¹) C.v' := by
        have h1 : C.tau⁻¹ * C.v' * C.tau ∈ C.Fv := by
          rw [← act_Fv C (inv_mem C.tau_N)]
          exact ⟨C.v', hvF, by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
        have h2 := C.q₂_F h1
        show C.tau * C.q₂ * C.tau⁻¹ * C.v' = C.v' * (C.tau * C.q₂ * C.tau⁻¹)
        calc C.tau * C.q₂ * C.tau⁻¹ * C.v' =
              C.tau * (C.q₂ * (C.tau⁻¹ * C.v' * C.tau)) * C.tau⁻¹ := by group
          _ = C.tau * ((C.q₂ * (C.tau⁻¹ * C.v' * C.tau) * C.q₂⁻¹) * C.q₂) * C.tau⁻¹ := by group
          _ = C.tau * ((C.tau⁻¹ * C.v' * C.tau) * C.q₂) * C.tau⁻¹ := by rw [h2]
          _ = C.v' * (C.tau * C.q₂ * C.tau⁻¹) := by group
      exact ((c1.mul_left c2).mul_left c3).eq
    have h2' : (b' * C.tau) ^ 2 = 1 := by
      rw [← e, show (C.q₂⁻¹ * (C.q₁ * a * C.tau) * C.q₂⁻¹⁻¹) ^ 2 =
        C.q₂⁻¹ * (C.q₁ * a * C.tau) ^ 2 * C.q₂⁻¹⁻¹ by rw [pow_two, pow_two]; group, h2]
      group
    obtain ⟨h, c, hc, hh⟩ := C.exists_conj_B hb'Q hb'v h2'
    refine ⟨h * C.q₂⁻¹, c, hc, ?_⟩
    rw [show h * C.q₂⁻¹ * (C.q₁ * a * C.tau) * (h * C.q₂⁻¹)⁻¹ =
      h * (C.q₂⁻¹ * (C.q₁ * a * C.tau) * C.q₂⁻¹⁻¹) * h⁻¹ by group, e, hh]
  · exfalso
    subst hsa
    have h1 : act (C.q₂ * a * C.tau) C.E₁ = C.G₂ := by
      rw [act_mul, act_mul, C.tau_act_E₁, C.act_Q₁_E₁ ha, b0]
    have h3 : act (C.q₂ * a * C.tau) C.G₂ = C.G₁ := by
      rw [act_mul, act_mul, C.tau_act_G₂, C.act_Q₁ ha C.r₃_mem, b3]
    have := act_sq_eq h2 C.E₁
    rw [h1, h3] at this
    exact C.E₁_ne_G₁ this.symm
  · exfalso
    subst hsa
    have h1 : act (C.q₁ * C.q₂ * a * C.tau) C.E₁ = C.G₃ := by
      rw [act_mul, act_mul, act_mul, C.tau_act_E₁, C.act_Q₁_E₁ ha, b0, a2]
    have h3 : act (C.q₁ * C.q₂ * a * C.tau) C.G₃ = C.G₁ := by
      rw [act_mul, act_mul, act_mul, C.tau_act_G₃, C.act_Q₁ ha C.r₂_mem, b2, a0]
    have := act_sq_eq h2 C.E₁
    rw [h1, h3] at this
    exact C.E₁_ne_G₁ this.symm

theorem Zz_le_Et0 : C.Zz ≤ C.Et₀ :=
  sup_le (zpowers_le.mpr C.z_mem_Et0) (zpowers_le.mpr C.k_mem_Et0)

theorem not_conjTo_Zz_tau {c : X} (hc : c ∈ C.Zz) : ¬ ConjTo S.t (c * C.tau) := by
  obtain ⟨c₀, hc₀, hu⟩ := C.u_t_form
  have hc₀E : c₀ ∈ C.E₀ := zpowers_le.mpr C.z_mem_E0 hc₀
  have htau : C.tau = c₀ * (C.F.xF * C.F.yF) := by
    show S.t * C.D₁.u = _
    rw [hu, show S.t * (c₀ * S.t * (C.F.xF * C.F.yF)) = (S.t * c₀) * S.t * (C.F.xF * C.F.yF) by
      group, C.t_comm_E0 hc₀E, mul_assoc c₀, tt S, mul_one]
  apply not_conjTo_of_mem_E0_any C.D₂ (isRefl_xyF C.F) (isK_zkF C.F)
  rw [htau]
  exact mul_mem (C.Zz_le_Et0 hc) (mul_mem (zpowers_le.mpr C.z_mem_Et0 hc₀) C.xy_mem_Et0)

theorem not_conjTo_Q₂₀_tau {s : X} (hs : s ∈ C.Q₂₀) : ¬ ConjTo S.t (s * C.tau) := by
  intro hc
  obtain ⟨h, c, hcZ, hh⟩ := C.exists_conj_Zz_tau hs (sq_of_conjTo hc)
  exact C.not_conjTo_Zz_tau hcZ (hh ▸ conjTo_conj hc)

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
