module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7TwoE
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Local

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_of_conj_gen [Finite X] {a g : X} (ha : g * a * g⁻¹ ∈ zpowers a) :
    g ∈ normalizer ((zpowers a : Subgroup X) : Set X) := by
  have hle : (zpowers a).map (MulAut.conj g).toMonoidHom ≤ zpowers a := by
    rw [map_le_iff_le_comap]
    exact zpowers_le.mpr ha
  refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj g).injective]

theorem t_mem_T (S : A7Base X) : S.t ∈ S.data.T := S.B_le_T t_mem_B

theorem tt (S : A7Base X) : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem exists_inv_v : ∃ v' : X, (v' = C.D₁.v ∨ v' = C.D₁.v * S.t) ∧ v' ^ 2 = 1 :=
  Sec7.exists_v' (D := C.D₁) C.isRefl_y C.isK_k C.k_mem_E0

def v' : X := Classical.choose C.exists_inv_v

theorem v'_eq : C.v' = C.D₁.v ∨ C.v' = C.D₁.v * S.t :=
  (Classical.choose_spec C.exists_inv_v).1

theorem v'_sq : C.v' ^ 2 = 1 := (Classical.choose_spec C.exists_inv_v).2

theorem v'v' : C.v' * C.v' = 1 := by rw [← pow_two, C.v'_sq]

theorem v'_E0 {e : X} (he : e ∈ C.E₀) : C.v' * e * C.v'⁻¹ = e := by
  rcases C.v'_eq with h | h <;> rw [h]
  · exact C.v_E0 he
  · rw [show C.D₁.v * S.t * e * (C.D₁.v * S.t)⁻¹ = C.D₁.v * (S.t * e * S.t⁻¹) * C.D₁.v⁻¹ by
      group, conj_eq_of_comm (C.t_comm_E0 he), C.v_E0 he]

theorem comm_v'_E0 {e : X} (he : e ∈ C.E₀) : C.v' * e = e * C.v' := by
  have := C.v'_E0 he
  calc C.v' * e = C.v' * e * C.v'⁻¹ * C.v' := by group
    _ = e * C.v' := by rw [this]

theorem v'_t : C.v' * S.t * C.v'⁻¹ = S.t * C.F.kF := by
  rcases C.v'_eq with h | h <;> rw [h]
  · exact C.v_t
  · rw [show C.D₁.v * S.t * S.t * (C.D₁.v * S.t)⁻¹ = C.D₁.v * S.t * C.D₁.v⁻¹ by group, C.v_t]

theorem v'_mem_C : C.v' ∈ C.D₁.Q₁ ⊓ centralizer (C.D₁.D₁₁ : Set X) := by
  rcases C.v'_eq with h | h <;> rw [h]
  · exact C.v_mem_C
  · exact mul_mem C.v_mem_C (t_mem_C C.D₁)

theorem v'_mem_T₁ : C.v' ∈ C.T₁ := by
  rcases C.v'_eq with h | h <;> rw [h]
  · exact C.v_mem_T₁
  · exact mul_mem C.v_mem_T₁ (C.h4.le (t_mem_T S))

theorem u_comm_v' : C.D₁.u * C.v' = C.v' * C.D₁.u := C.D₁.u_comm_C _ C.v'_mem_C

theorem v'_xy : C.v' * (C.F.xF * C.F.yF) * C.v'⁻¹ = C.F.kF * (C.F.xF * C.F.yF) := by
  rcases C.v'_eq with h | h <;> rw [h]
  · exact C.v_xy
  · rw [show C.D₁.v * S.t * (C.F.xF * C.F.yF) * (C.D₁.v * S.t)⁻¹ =
      C.D₁.v * (S.t * (C.F.xF * C.F.yF) * S.t⁻¹) * C.D₁.v⁻¹ by group,
      conj_eq_of_comm (S.central_of_mem_B t_mem_B C.xy_mem_T), C.v_xy]

theorem wt₁_sq : C.D₂.w₁ ^ 2 = 1 := by
  have h := C.D₂.q0_holds
  rw [C.q0₂_extraspecial] at h
  exact h.1

theorem wt₁_mem_Qt0 : C.D₂.w₁ ∈ C.Qt₀ := mem_sup_left (mem_sup_right (mem_zpowers _))

theorem wt₁_mem_T₁ : C.D₂.w₁ ∈ C.T₁ := C.D₂.T₁_eq.ge (mem_sup_right (mem_zpowers _))

theorem vt_mem_T₁ : C.D₂.v ∈ C.T₁ := C.D₂.T₁_eq.ge (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem zkzk : S.z * C.F.kF * (S.z * C.F.kF) = 1 := by
  rw [← pow_two]; exact (isK_zkF C.F).sq

theorem wt₁_t : C.D₂.w₁ * S.t * C.D₂.w₁⁻¹ = S.t * C.F.kF := by
  rw [C.hact₂.2.2.1, mul_assoc S.t, ← mul_assoc S.z, zz S, one_mul]

theorem wt₁_z : C.D₂.w₁ * S.z * C.D₂.w₁⁻¹ = S.z := C.hact₂.2.2.2.2.1

theorem wt₁_zk : C.D₂.w₁ * (S.z * C.F.kF) * C.D₂.w₁⁻¹ = S.z * C.F.kF :=
  C.hact₂.2.2.2.2.2.2.2.2.1

theorem wt₁_k : C.D₂.w₁ * C.F.kF * C.D₂.w₁⁻¹ = C.F.kF := by
  calc C.D₂.w₁ * C.F.kF * C.D₂.w₁⁻¹ =
        (C.D₂.w₁ * S.z * C.D₂.w₁⁻¹)⁻¹ * (C.D₂.w₁ * (S.z * C.F.kF) * C.D₂.w₁⁻¹) := by group
    _ = C.F.kF := by rw [C.wt₁_z, C.wt₁_zk]; group

theorem wt₁_xy : C.D₂.w₁ * (C.F.xF * C.F.yF) * C.D₂.w₁⁻¹ =
    C.F.xF * C.F.yF * (S.z * C.F.kF) := C.hact₂.2.2.2.2.2.2.2.1

theorem vt_Et0 {e : X} (he : e ∈ C.Et₀) : C.D₂.v * e * C.D₂.v⁻¹ = e := C.hact₂.1 e he

theorem vt_t : C.D₂.v * S.t * C.D₂.v⁻¹ = S.t * (S.z * C.F.kF) := C.hact₂.2.1

theorem vt_inv_t : C.D₂.v⁻¹ * S.t * C.D₂.v = S.t * (S.z * C.F.kF) :=
  conj_inv_eq_of C.vt_t (C.vt_Et0 C.zk_mem_Et0) C.zkzk

theorem comm_Et (a b : X) (ha : a ∈ S.E (C.F.xF * C.F.yF)) (hb : b ∈ S.E (C.F.xF * C.F.yF)) :
    a * b = b * a :=
  (isRefl_xyF C.F).elemAbelianTwo_E.comm a ha b hb

theorem t_mem_Et : S.t ∈ S.E (C.F.xF * C.F.yF) := t_mem_E _

theorem Et0_le_Et : C.Et₀ ≤ S.E (C.F.xF * C.F.yF) := E0_le_E (isK_zkF C.F) _

theorem mul_wt₁_conj {e : X} (he : e ∈ C.Et₀) :
    e * (C.D₂.w₁ * e * C.D₂.w₁⁻¹) = 1 ∨ e * (C.D₂.w₁ * e * C.D₂.w₁⁻¹) = S.z * C.F.kF := by
  have he' : e ∈ S.E0 (C.F.xF * C.F.yF) (S.z * C.F.kF) := he
  rw [E0_eq] at he'
  have hZ : (zpowers S.z ⊔ zpowers (S.z * C.F.kF) : Subgroup X) = C.Zz := by
    rw [C.Zz_eq', sup_comm]
  have hfix : ∀ f ∈ (zpowers S.z ⊔ zpowers (S.z * C.F.kF) : Subgroup X),
      C.D₂.w₁ * f * C.D₂.w₁⁻¹ = f := fun f hf =>
    C.fix_Zz C.wt₁_z C.wt₁_k (hZ ▸ hf)
  have hel := elemAbelianTwo_zk (isK_zkF C.F)
  rcases mem_or_of_mem_sup hel (xyF_sq C.F) (fun _ hb => (isRefl_xyF C.F).comm_B
      (zk_le_B (isK_zkF C.F) hb)) he' with h | h
  · left
    rw [hfix e h, ← pow_two]
    exact hel.sq_eq_one e h
  · right
    set f := e * (C.F.xF * C.F.yF) with hf
    have hfB := zk_le_B (isK_zkF C.F) h
    have hef : e = f * (C.F.xF * C.F.yF) := by
      rw [hf, mul_assoc, ← pow_two, xyF_sq, mul_one]
    have hfxy : f * (C.F.xF * C.F.yF) = C.F.xF * C.F.yF * f :=
      ((isRefl_xyF C.F).comm_B hfB).symm
    have hf2 : f * f = 1 := by rw [← pow_two]; exact hel.sq_eq_one f h
    have hxyzk : C.F.xF * C.F.yF * (S.z * C.F.kF) = S.z * C.F.kF * (C.F.xF * C.F.yF) :=
      (isRefl_xyF C.F).comm_B (isK_zkF C.F).mem
    rw [hef, conj_mul_eq, hfix f h, C.wt₁_xy]
    calc f * (C.F.xF * C.F.yF) * (f * (C.F.xF * C.F.yF * (S.z * C.F.kF))) =
          (f * (C.F.xF * C.F.yF)) * (f * (C.F.xF * C.F.yF)) * (S.z * C.F.kF) := by group
      _ = S.z * C.F.kF := by
          rw [hfxy, show C.F.xF * C.F.yF * f * (C.F.xF * C.F.yF * f) =
              C.F.xF * C.F.yF * (f * (C.F.xF * C.F.yF)) * f by group, hfxy,
            show C.F.xF * C.F.yF * (C.F.xF * C.F.yF * f) * f = (C.F.xF * C.F.yF) *
              (C.F.xF * C.F.yF) * (f * f) by group, hf2, ← pow_two, xyF_sq, one_mul, one_mul]

theorem v'yw_fix {e : X} (he : e ∈ S.E (C.F.xF * C.F.yF)) :
    (C.v' * C.F.yF * C.D₂.w₁) * e * (C.v' * C.F.yF * C.D₂.w₁)⁻¹ = e := by
  set g := C.v' * C.F.yF * C.D₂.w₁ with hg
  have hconj : ∀ a, g * a * g⁻¹ = C.v' * (C.F.yF * (C.D₂.w₁ * a * C.D₂.w₁⁻¹) * C.F.yF⁻¹) *
      C.v'⁻¹ := fun a => by rw [hg]; group
  have hyB : ∀ b ∈ S.B, C.F.yF * b * C.F.yF⁻¹ = b := fun b hb =>
    conj_eq_of_comm (C.isRefl_y.comm_B hb)
  have hv'k : C.v' * C.F.kF * C.v'⁻¹ = C.F.kF := C.v'_E0 C.k_mem_E0
  have hv'z : C.v' * S.z * C.v'⁻¹ = S.z := C.v'_E0 C.z_mem_E0
  have hkxy : C.F.kF * (C.F.xF * C.F.yF) = C.F.xF * C.F.yF * C.F.kF := kF_comm C.F C.xy_mem_T
  have hzxy : S.z * (C.F.xF * C.F.yF) = C.F.xF * C.F.yF * S.z :=
    S.central_of_mem_B z_mem_B C.xy_mem_T
  have hkz : C.F.kF * S.z = S.z * C.F.kF := commute_of_mem_B (kF_mem_B C.F) z_mem_B
  refine fix_E_of_fix C.F (C.F.xF * C.F.yF) ?_ ?_ ?_ ?_ he
  · rw [hconj, C.wt₁_z, hyB _ z_mem_B, hv'z]
  · rw [hconj, C.wt₁_t, hyB _ (mul_mem t_mem_B (kF_mem_B C.F)), conj_mul_eq, C.v'_t, hv'k,
      mul_assoc, C.kk, mul_one]
  · rw [hconj, C.wt₁_k, hyB _ (kF_mem_B C.F), hv'k]
  · have h2 : C.F.yF * (C.F.xF * C.F.yF * (S.z * C.F.kF)) * C.F.yF⁻¹ =
        S.z * (C.F.xF * C.F.yF) * (S.z * C.F.kF) := by
      rw [conj_mul_eq, C.y_conj_xy, hyB _ (isK_zkF C.F).mem]
    have h3 : C.v' * (S.z * (C.F.xF * C.F.yF) * (S.z * C.F.kF)) * C.v'⁻¹ = C.F.xF * C.F.yF := by
      calc C.v' * (S.z * (C.F.xF * C.F.yF) * (S.z * C.F.kF)) * C.v'⁻¹ =
            (C.v' * S.z * C.v'⁻¹) * (C.v' * (C.F.xF * C.F.yF) * C.v'⁻¹) *
              (C.v' * (S.z * C.F.kF) * C.v'⁻¹) := by group
        _ = S.z * (C.F.kF * (C.F.xF * C.F.yF)) * (S.z * C.F.kF) := by
          rw [hv'z, C.v'_xy, C.v'_E0 (mul_mem C.z_mem_E0 C.k_mem_E0)]
        _ = (C.F.xF * C.F.yF) * (S.z * C.F.kF) * (S.z * C.F.kF) := by
          have hc : S.z * (C.F.kF * (C.F.xF * C.F.yF)) = C.F.xF * C.F.yF * (S.z * C.F.kF) := by
            rw [hkxy, ← mul_assoc, hzxy, mul_assoc]
          rw [hc]
        _ = C.F.xF * C.F.yF := by rw [mul_assoc, C.zkzk, mul_one]
    rw [hconj, C.wt₁_xy, h2, h3]

theorem v'yw_mem_Et : C.v' * C.F.yF * C.D₂.w₁ ∈ S.E (C.F.xF * C.F.yF) := by
  have hT : C.v' * C.F.yF * C.D₂.w₁ ∈ C.T₁ :=
    mul_mem (mul_mem C.v'_mem_T₁ (C.h4.le (yF_mem_T C.F))) C.wt₁_mem_T₁
  exact mem_E_of_centralizes (isRefl_xyF C.F) C.h4.isPGroup hT fun e he => C.v'yw_fix he

theorem v'y_sq : (C.v' * C.F.yF) * (C.v' * C.F.yF) = 1 := by
  rw [show C.v' * C.F.yF * (C.v' * C.F.yF) = C.v' * (C.F.yF * C.v') * C.F.yF by group,
    ← C.comm_v'_E0 C.y_mem_E0, show C.v' * (C.v' * C.F.yF) * C.F.yF =
      (C.v' * C.v') * (C.F.yF * C.F.yF) by group, C.v'v', C.yy, one_mul]

theorem v'y_mem_Qt0 : C.v' * C.F.yF ∈ C.Qt₀ := by
  set g := C.v' * C.F.yF * C.D₂.w₁ with hg
  have hgy : C.v' * C.F.yF = g * C.D₂.w₁ := by rw [hg, mul_assoc, ← pow_two, C.wt₁_sq, mul_one]
  rcases (isRefl_xyF C.F).mem_E0_or (isK_zkF C.F) C.v'yw_mem_Et with h | h
  · rw [hgy]
    exact mul_mem (C.Et0_le_Qt0 h) C.wt₁_mem_Qt0
  · exfalso
    set e := g * S.t with he
    have hge : g = e * S.t := by rw [he, mul_assoc, tt S, mul_one]
    have hsq := C.v'y_sq
    rw [hgy, hge] at hsq
    have heE := C.Et0_le_Et h
    have he'E := C.Et0_le_Et (conj_mem_of_mem_normalizer (show C.D₂.w₁ ∈ normalizer
      (C.Et₀ : Set X) from ?_) h)
    · have hcalc : e * S.t * C.D₂.w₁ * (e * S.t * C.D₂.w₁) =
          e * (C.D₂.w₁ * e * C.D₂.w₁⁻¹) * C.F.kF := by
        calc e * S.t * C.D₂.w₁ * (e * S.t * C.D₂.w₁) =
              e * S.t * (C.D₂.w₁ * e * C.D₂.w₁⁻¹) * (C.D₂.w₁ * S.t * C.D₂.w₁⁻¹) *
                (C.D₂.w₁ * C.D₂.w₁) := by group
          _ = e * (C.D₂.w₁ * e * C.D₂.w₁⁻¹) * C.F.kF := by
            rw [C.wt₁_t, ← pow_two, C.wt₁_sq, mul_one, mul_assoc e S.t,
              C.comm_Et _ _ C.t_mem_Et he'E]
            rw [show e * (C.D₂.w₁ * e * C.D₂.w₁⁻¹ * S.t) * (S.t * C.F.kF) =
              e * (C.D₂.w₁ * e * C.D₂.w₁⁻¹) * (S.t * S.t) * C.F.kF by group, tt S, mul_one]
      rw [hcalc] at hsq
      rcases C.mul_wt₁_conj h with h1 | h1 <;> rw [h1] at hsq
      · exact (isK_kF C.F).ne_one (by simpa using hsq)
      · apply S.z_ne_one
        calc S.z = S.z * C.F.kF * C.F.kF := by rw [mul_assoc, C.kk, mul_one]
          _ = 1 := hsq
    · refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge ?_ ?_)
      · rw [map_le_iff_le_comap]
        intro a ha
        show C.D₂.w₁ * a * C.D₂.w₁⁻¹ ∈ C.Et₀
        rcases C.mul_wt₁_conj ha with h1 | h1
        · have : C.D₂.w₁ * a * C.D₂.w₁⁻¹ = a⁻¹ := eq_inv_of_mul_eq_one_right h1
          rw [this]; exact inv_mem ha
        · have : C.D₂.w₁ * a * C.D₂.w₁⁻¹ = a⁻¹ * (S.z * C.F.kF) := eq_inv_mul_of_mul_eq h1
          rw [this]; exact mul_mem (inv_mem ha) C.zk_mem_Et0
      · rw [card_map_of_injective (MulAut.conj C.D₂.w₁).injective]

theorem not_conjTo_v'y : ¬ ConjTo S.t (C.v' * C.F.yF) :=
  C.D₂.no_conj_extraspecial C.q0₂_extraspecial _ C.v'y_mem_Qt0

theorem vt_inv_Et0 {e : X} (he : e ∈ C.Et₀) : C.D₂.v⁻¹ * e * C.D₂.v = e := by
  have := C.vt_Et0 he
  calc C.D₂.v⁻¹ * e * C.D₂.v = C.D₂.v⁻¹ * (C.D₂.v * e * C.D₂.v⁻¹) * C.D₂.v := by rw [this]
    _ = e := by group

theorem v'yw₁'_fix {e : X} (he : e ∈ S.E (C.F.xF * C.F.yF)) :
    (C.v' * C.F.yF * C.w₁' * C.D₂.v⁻¹) * e * (C.v' * C.F.yF * C.w₁' * C.D₂.v⁻¹)⁻¹ = e := by
  have hconj : ∀ a, (C.v' * C.F.yF * C.w₁' * C.D₂.v⁻¹) * a *
      (C.v' * C.F.yF * C.w₁' * C.D₂.v⁻¹)⁻¹ = C.v' * (C.F.yF * (C.w₁' * (C.D₂.v⁻¹ * a *
        C.D₂.v) * C.w₁'⁻¹) * C.F.yF⁻¹) * C.v'⁻¹ := fun a => by group
  have hyB : ∀ b ∈ S.B, C.F.yF * b * C.F.yF⁻¹ = b := fun b hb =>
    conj_eq_of_comm (C.isRefl_y.comm_B hb)
  have hv'k : C.v' * C.F.kF * C.v'⁻¹ = C.F.kF := C.v'_E0 C.k_mem_E0
  have hv'z : C.v' * S.z * C.v'⁻¹ = S.z := C.v'_E0 C.z_mem_E0
  have hw'z : C.w₁' * S.z * C.w₁'⁻¹ = S.z := C.w₁'_E0 C.z_mem_E0
  have hw'k : C.w₁' * C.F.kF * C.w₁'⁻¹ = C.F.kF := C.w₁'_E0 C.k_mem_E0
  have hkxy : C.F.kF * (C.F.xF * C.F.yF) = C.F.xF * C.F.yF * C.F.kF := kF_comm C.F C.xy_mem_T
  have hzxy : S.z * (C.F.xF * C.F.yF) = C.F.xF * C.F.yF * S.z :=
    S.central_of_mem_B z_mem_B C.xy_mem_T
  have hkz : C.F.kF * S.z = S.z * C.F.kF := commute_of_mem_B (kF_mem_B C.F) z_mem_B
  refine fix_E_of_fix C.F (C.F.xF * C.F.yF) ?_ ?_ ?_ ?_ he
  · rw [hconj, C.vt_inv_Et0 C.z_mem_Et0, hw'z, hyB _ z_mem_B, hv'z]
  · have i1 : C.w₁' * (S.t * (S.z * C.F.kF)) * C.w₁'⁻¹ = S.t * S.z * (S.z * C.F.kF) := by
      rw [conj_mul_eq, C.w₁'_t, C.w₁'_E0 (mul_mem C.z_mem_E0 C.k_mem_E0)]
    have i2 : C.F.yF * (S.t * S.z * (S.z * C.F.kF)) * C.F.yF⁻¹ = S.t * S.z * (S.z * C.F.kF) :=
      hyB _ (mul_mem (mul_mem t_mem_B z_mem_B) (mul_mem z_mem_B (kF_mem_B C.F)))
    have i3 : C.v' * (S.t * S.z * (S.z * C.F.kF)) * C.v'⁻¹ = S.t := by
      calc C.v' * (S.t * S.z * (S.z * C.F.kF)) * C.v'⁻¹ = (C.v' * S.t * C.v'⁻¹) *
            (C.v' * S.z * C.v'⁻¹) * (C.v' * (S.z * C.F.kF) * C.v'⁻¹) := by group
        _ = S.t * (C.F.kF * (S.z * S.z) * C.F.kF) := by
          rw [C.v'_t, hv'z, C.v'_E0 (mul_mem C.z_mem_E0 C.k_mem_E0)]; group
        _ = S.t := by rw [zz S, mul_one, C.kk, mul_one]
    rw [hconj, C.vt_inv_t, i1, i2, i3]
  · rw [hconj, C.vt_inv_Et0 C.k_mem_Et0, hw'k, hyB _ (kF_mem_B C.F), hv'k]
  · have i2 : C.F.yF * (S.z * C.F.kF * (C.F.xF * C.F.yF)) * C.F.yF⁻¹ =
        S.z * C.F.kF * (S.z * (C.F.xF * C.F.yF)) := by
      rw [show C.F.yF * (S.z * C.F.kF * (C.F.xF * C.F.yF)) * C.F.yF⁻¹ =
        (C.F.yF * (S.z * C.F.kF) * C.F.yF⁻¹) * (C.F.yF * (C.F.xF * C.F.yF) * C.F.yF⁻¹) by group,
        hyB _ (isK_zkF C.F).mem, C.y_conj_xy]
    rw [hconj, C.vt_inv_Et0 C.xy_mem_Et0, C.w₁'_xy', i2]
    calc C.v' * (S.z * C.F.kF * (S.z * (C.F.xF * C.F.yF))) * C.v'⁻¹ =
          (C.v' * (S.z * C.F.kF) * C.v'⁻¹) * (C.v' * S.z * C.v'⁻¹) *
            (C.v' * (C.F.xF * C.F.yF) * C.v'⁻¹) := by group
      _ = S.z * C.F.kF * S.z * (C.F.kF * (C.F.xF * C.F.yF)) := by
          rw [C.v'_E0 (mul_mem C.z_mem_E0 C.k_mem_E0), hv'z, C.v'_xy]
      _ = C.F.xF * C.F.yF := by
          have hzkz : S.z * C.F.kF * S.z = C.F.kF := by
            rw [mul_assoc S.z C.F.kF S.z, hkz, ← mul_assoc, zz S, one_mul]
          rw [hzkz, ← mul_assoc, C.kk, one_mul]

theorem v'yw₁'_mem_Et : C.v' * C.F.yF * C.w₁' * C.D₂.v⁻¹ ∈ S.E (C.F.xF * C.F.yF) := by
  have hT : C.v' * C.F.yF * C.w₁' * C.D₂.v⁻¹ ∈ C.T₁ :=
    mul_mem (mul_mem (mul_mem C.v'_mem_T₁ (C.h4.le (yF_mem_T C.F))) C.w₁'_mem_T₁)
      (inv_mem C.vt_mem_T₁)
  exact mem_E_of_centralizes (isRefl_xyF C.F) C.h4.isPGroup hT fun e he => C.v'yw₁'_fix he

theorem vt_sq : C.D₂.v ^ 2 = 1 ∨ C.D₂.v ^ 2 = S.z * C.F.kF :=
  Sec7.v_sq_eq (D := C.D₂) (isRefl_xyF C.F) (isK_zkF C.F) C.k_mem_Et0

theorem v'yw₁'_sq : (C.v' * C.F.yF * C.w₁') ^ 2 = 1 ∨
    (C.v' * C.F.yF * C.w₁') ^ 2 = S.z * C.F.kF := by
  set a := C.v' * C.F.yF * C.w₁' with ha
  set g := a * C.D₂.v⁻¹ with hg
  have hag : a = g * C.D₂.v := by rw [hg]; group
  have hzk : S.z * C.F.kF ∈ S.E (C.F.xF * C.F.yF) := C.Et0_le_Et C.zk_mem_Et0
  rcases (isRefl_xyF C.F).mem_E0_or (isK_zkF C.F) C.v'yw₁'_mem_Et with h | h
  ·
    have hsq : a ^ 2 = C.D₂.v ^ 2 := by
      rw [hag, pow_two, pow_two, show g * C.D₂.v * (g * C.D₂.v) =
        g * (C.D₂.v * g * C.D₂.v⁻¹) * (C.D₂.v * C.D₂.v) by group, C.vt_Et0 h, ← pow_two,
        ((isRefl_xyF C.F).elemAbelianTwo_E0 (isK_zkF C.F)).sq_eq_one g h, one_mul]
    rw [hsq]; exact C.vt_sq
  ·
    set e := g * S.t with he
    have hge : g = e * S.t := by rw [he, mul_assoc, tt S, mul_one]
    have heE := C.Et0_le_Et h
    have hsq : a ^ 2 = S.z * C.F.kF * C.D₂.v ^ 2 := by
      rw [hag, hge, pow_two, pow_two, show e * S.t * C.D₂.v * (e * S.t * C.D₂.v) =
        e * S.t * (C.D₂.v * e * C.D₂.v⁻¹) * (C.D₂.v * S.t * C.D₂.v⁻¹) * (C.D₂.v * C.D₂.v) by
          group, C.vt_Et0 h, C.vt_t, mul_assoc e S.t, C.comm_Et _ _ C.t_mem_Et heE,
        show e * (e * S.t) * (S.t * (S.z * C.F.kF)) = (e * e) * (S.t * S.t) * (S.z * C.F.kF) by
          group, tt S, ← pow_two e, ((isRefl_xyF C.F).elemAbelianTwo_E0 (isK_zkF C.F)).sq_eq_one
          e h, one_mul, one_mul]
    rw [hsq]
    rcases C.vt_sq with h1 | h1 <;> rw [h1]
    · exact Or.inr (mul_one _)
    · exact Or.inl C.zkzk

theorem w₁'_comm_y : C.w₁' * C.F.yF = C.F.yF * C.w₁' := by
  have := C.w₁'_E0 C.y_mem_E0
  calc C.w₁' * C.F.yF = C.w₁' * C.F.yF * C.w₁'⁻¹ * C.w₁' := by group
    _ = C.F.yF * C.w₁' := by rw [this]

theorem v'yw₁'_sq_eq : (C.v' * C.F.yF * C.w₁') ^ 2 = (C.v' * C.w₁') ^ 2 := by
  rw [pow_two, pow_two, mul_assoc C.v', ← C.w₁'_comm_y,
    show C.v' * (C.w₁' * C.F.yF) * (C.v' * (C.w₁' * C.F.yF)) =
      C.v' * C.w₁' * (C.F.yF * C.v') * C.w₁' * C.F.yF by group, ← C.comm_v'_E0 C.y_mem_E0,
    show C.v' * C.w₁' * (C.v' * C.F.yF) * C.w₁' * C.F.yF =
      C.v' * C.w₁' * C.v' * (C.F.yF * C.w₁') * C.F.yF by group, ← C.w₁'_comm_y,
    show C.v' * C.w₁' * C.v' * (C.w₁' * C.F.yF) * C.F.yF =
      C.v' * C.w₁' * (C.v' * C.w₁') * (C.F.yF * C.F.yF) by group, C.yy, mul_one]

theorem comm_w₁'_v'_mem : C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ ∈ zpowers S.z := by
  have h := C.D₁.w₁_comm_C _ C.v'_mem_C
  rw [C.act_one] at h
  have h1 : C.D₁.w₁ * C.v' * C.D₁.w₁⁻¹ * C.v'⁻¹ ∈ zpowers S.z := by
    rw [zpowers_eq_closure]; exact h
  rcases C.w₁'_eq with h2 | h2 <;> rw [h2]
  · exact h1
  · have hc := zpowers_le.mpr C.z_mem_E0 h1
    rw [show C.F.yF * C.D₁.w₁ * C.v' * (C.F.yF * C.D₁.w₁)⁻¹ * C.v'⁻¹ =
      C.F.yF * (C.D₁.w₁ * C.v' * C.D₁.w₁⁻¹ * C.v'⁻¹) * (C.v' * C.F.yF⁻¹ * C.v'⁻¹) by group,
      show C.v' * C.F.yF⁻¹ * C.v'⁻¹ = C.F.yF⁻¹ by
        rw [show C.v' * C.F.yF⁻¹ * C.v'⁻¹ = (C.v' * C.F.yF * C.v'⁻¹)⁻¹ by group,
          C.v'_E0 C.y_mem_E0],
      conj_eq_of_comm (C.comm_E0 C.y_mem_E0 hc)]
    exact h1

theorem w₁'_sq : C.w₁' ^ 2 = C.D₁.w₁ ^ 2 := by
  rcases C.w₁'_eq with h | h <;> rw [h]
  rw [pow_two, pow_two, show C.F.yF * C.D₁.w₁ * (C.F.yF * C.D₁.w₁) =
    C.F.yF * (C.D₁.w₁ * C.F.yF * C.D₁.w₁⁻¹) * (C.D₁.w₁ * C.D₁.w₁) by group,
    C.w₁_E0 C.y_mem_E0, ← mul_assoc, C.yy, one_mul]

theorem v'w₁'_sq : (C.v' * C.w₁') ^ 2 = (C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹) * C.D₁.w₁ ^ 2 := by
  set c := C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ with hc
  have hcE : c ∈ C.E₀ := zpowers_le.mpr C.z_mem_E0 C.comm_w₁'_v'_mem
  have hwv : C.w₁' * C.v' = c * C.v' * C.w₁' := by rw [hc]; group
  rw [pow_two, show C.v' * C.w₁' * (C.v' * C.w₁') = C.v' * (C.w₁' * C.v') * C.w₁' by group, hwv,
    show C.v' * (c * C.v' * C.w₁') * C.w₁' = (C.v' * c) * C.v' * (C.w₁' * C.w₁') by group,
    C.comm_v'_E0 hcE, mul_assoc c, C.v'v', mul_one, ← pow_two, C.w₁'_sq]

theorem comm_w₁'_v'_e4q8 (hq : C.D₁.q0 = .e4q8) : C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ = S.z := by
  have hw : C.D₁.w₁ ^ 2 = C.F.kF := by
    have h := C.D₁.q0_holds
    rw [hq] at h
    exact h.1
  have h1 := C.v'yw₁'_sq
  rw [C.v'yw₁'_sq_eq, C.v'w₁'_sq, hw] at h1
  rcases eq_one_or_eq_of_mem_zpowers z_sq C.comm_w₁'_v'_mem with h2 | h2
  · exfalso
    rw [h2, one_mul] at h1
    rcases h1 with h1 | h1
    · exact (isK_kF C.F).ne_one h1
    · exact S.z_ne_one (by simpa using h1.symm)
  · exact h2

theorem comm_w₁'_v'_exc (hq : C.D₁.q0 = .exceptional) :
    C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ = 1 := by
  have hw : C.D₁.w₁ ^ 2 = S.z * C.F.kF := by
    have h := C.D₁.q0_holds
    rw [hq] at h
    exact h.1
  have h1 := C.v'yw₁'_sq
  rw [C.v'yw₁'_sq_eq, C.v'w₁'_sq, hw] at h1
  rcases eq_one_or_eq_of_mem_zpowers z_sq C.comm_w₁'_v'_mem with h2 | h2
  · exact h2
  · exfalso
    rw [h2, ← mul_assoc, zz S, one_mul] at h1
    rcases h1 with h1 | h1
    · exact (isK_kF C.F).ne_one h1
    · exact S.z_ne_one (by simpa using h1.symm)

theorem t_inv (S : A7Base X) : S.t⁻¹ = S.t := inv_eq_of_mul_eq_one_right (tt S)

theorem t_v' : S.t * C.v' * S.t⁻¹ = C.F.kF * C.v' := by
  calc S.t * C.v' * S.t⁻¹ = S.t * (C.v' * S.t * C.v'⁻¹) * C.v' := by rw [t_inv S]; group
    _ = S.t * (S.t * C.F.kF) * C.v' := by rw [C.v'_t]
    _ = C.F.kF * C.v' := by rw [← mul_assoc, tt S, one_mul]

theorem C_le : C.D₁.Q₁ ⊓ centralizer (C.D₁.D₁₁ : Set X) ≤
    zpowers C.F.kF ⊔ zpowers C.v' ⊔ zpowers S.t := by
  rw [C.D₁.C_eq, closure_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h <;> rw [h]
  · exact mem_sup_right (mem_zpowers _)
  · exact mem_sup_left (mem_sup_left (mem_zpowers _))
  · rcases C.v'_eq with h' | h'
    · rw [← h']; exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · have : C.D₁.v = C.v' * S.t⁻¹ := by rw [h']; group
      rw [this]
      exact mul_mem (mem_sup_left (mem_sup_right (mem_zpowers _)))
        (inv_mem (mem_sup_right (mem_zpowers _)))

theorem w₁'_t_ne : C.w₁' * S.t ≠ S.t * C.w₁' := by
  intro h
  have := C.w₁'_t
  rw [h, mul_inv_cancel_right] at this
  exact S.z_ne_one (by simpa using this.symm)

theorem mem_of_mem_C₁ {V : Subgroup X} (htV : S.t ∈ normalizer (V : Set X))
    (hCV : C.D₁.Q₁ ⊓ centralizer (C.D₁.D₁₁ : Set X) ≤ V ⊔ zpowers S.t)
    (hVw : ∀ c ∈ V, c * C.w₁' = C.w₁' * c) {c : X} (hc : c ∈ C.D₁.C₁) : c ∈ V := by
  have hcC := hCV (C.D₁.C₁_le hc)
  have ht2 : S.t ^ 2 ∈ V := by rw [S.t_sq]; exact one_mem _
  rcases mem_or_of_mem_sup_zpowers htV ht2 hcC with h | h
  · exact h
  · exfalso
    have hcw : c * C.w₁' = C.w₁' * c := C.D₁.C₁_comm c hc _ C.w₁'_mem_Q0
    set d := c * S.t⁻¹ with hdd
    have h1 := hVw _ h
    have ht : S.t = d⁻¹ * c := by rw [hdd]; group
    have hd : d⁻¹ * C.w₁' = C.w₁' * d⁻¹ := by
      calc d⁻¹ * C.w₁' = d⁻¹ * (C.w₁' * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * C.w₁') * d⁻¹ := by rw [h1]
        _ = C.w₁' * d⁻¹ := by group
    apply C.w₁'_t_ne
    symm
    calc S.t * C.w₁' = d⁻¹ * (c * C.w₁') := by rw [ht]; group
      _ = d⁻¹ * (C.w₁' * c) := by rw [hcw]
      _ = (d⁻¹ * C.w₁') * c := by group
      _ = C.w₁' * d⁻¹ * c := by rw [hd]
      _ = C.w₁' * S.t := by rw [ht]; group

theorem v'_mem_C₁ (hq : C.D₁.q0 = .exceptional) : C.v' ∈ C.D₁.C₁ := by
  set V : Subgroup X := zpowers C.F.kF ⊔ zpowers C.v' with hV
  have hkv : C.F.kF * C.v' = C.v' * C.F.kF := (C.comm_v'_E0 C.k_mem_E0).symm
  have hw'v' : C.v' * C.w₁' = C.w₁' * C.v' := by
    have h := C.comm_w₁'_v'_exc hq
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hw'k : C.F.kF * C.w₁' = C.w₁' * C.F.kF := by
    have := C.w₁'_E0 C.k_mem_E0
    calc C.F.kF * C.w₁' = C.w₁' * (C.w₁'⁻¹ * C.F.kF * C.w₁') := by group
      _ = C.w₁' * C.F.kF := by
        rw [show C.w₁'⁻¹ * C.F.kF * C.w₁' = C.F.kF from by
          calc C.w₁'⁻¹ * C.F.kF * C.w₁' = C.w₁'⁻¹ * (C.w₁' * C.F.kF * C.w₁'⁻¹) * C.w₁' := by
                rw [this]
            _ = C.F.kF := by group]
  have hVw : ∀ c ∈ V, c * C.w₁' = C.w₁' * c := by
    intro c hc
    have hle : V ≤ centralizer ({C.w₁'} : Set X) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;> rw [mem_centralizer_singleton_iff]
      · exact hw'k
      · exact hw'v'
    exact mem_centralizer_singleton_iff.mp (hle hc)
  have htV : S.t ∈ normalizer (V : Set X) := by
    refine mem_normalizer_of_conj_gens ?_ ?_
    · rw [conj_eq_of_comm (C.isRefl_y.comm_E0_t C.isK_k C.k_mem_E0)]
      exact mem_sup_left (mem_zpowers _)
    · rw [C.t_v']
      exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  have hle : C.D₁.C₁ ≤ V := fun c hc => C.mem_of_mem_C₁ htV C.C_le hVw hc
  have hcardV : Nat.card V ≤ 4 := by
    by_cases hv : C.v' ∈ zpowers C.F.kF
    · rw [hV, sup_eq_left.mpr (zpowers_le.mpr hv), Nat.card_zpowers,
        orderOf_eq_prime C.F.kF_sq (isK_kF C.F).ne_one]
      norm_num
    · have hkel : ElemAbelianTwo (zpowers C.F.kF) :=
        ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr (kF_mem_B C.F) ha)
          (zpowers_le.mpr (kF_mem_B C.F) hb),
          fun a ha => S.sq_of_mem_B (zpowers_le.mpr (kF_mem_B C.F) ha)⟩
      rw [hV, card_sup_of_not_mem hkel C.v'_sq hv (fun a ha => ?_), Nat.card_zpowers,
        orderOf_eq_prime C.F.kF_sq (isK_kF C.F).ne_one]
      exact (C.comm_v'_E0 ((zpowers_le.mpr C.k_mem_E0) ha))
  have heq : C.D₁.C₁ = V := Subgroup.eq_of_le_of_card_ge hle (by rw [C.D₁.card_C₁]; exact hcardV)
  rw [heq]
  exact mem_sup_right (mem_zpowers _)

theorem v'_comm_Q0 (hq : C.D₁.q0 = .exceptional) {a : X} (ha : a ∈ C.Q₀) :
    C.v' * a = a * C.v' :=
  C.D₁.C₁_comm _ (C.v'_mem_C₁ hq) a ha

theorem v't_mem_C₁ (hq : C.D₁.q0 = .e4q8) : C.v' * S.t ∈ C.D₁.C₁ := by
  set V : Subgroup X := zpowers (C.v' * S.t) with hV
  have hsq : (C.v' * S.t) * (C.v' * S.t) = C.F.kF := by
    rw [show C.v' * S.t * (C.v' * S.t) = (C.v' * S.t * C.v'⁻¹) * (C.v' * C.v') * S.t by
      group, C.v'_t, C.v'v', mul_one, mul_assoc,
      ← C.isRefl_y.comm_E0_t C.isK_k C.k_mem_E0, ← mul_assoc, tt S, one_mul]
  have hkV : C.F.kF ∈ V := by rw [← hsq]; exact mul_mem (mem_zpowers _) (mem_zpowers _)
  have hw'v't : (C.v' * S.t) * C.w₁' = C.w₁' * (C.v' * S.t) := by
    have hc := C.comm_w₁'_v'_e4q8 hq
    have h1 : C.w₁' * C.v' * C.w₁'⁻¹ = S.z * C.v' := by rw [← hc]; group
    have hzv : S.z * C.v' = C.v' * S.z := (C.comm_v'_E0 C.z_mem_E0).symm
    have hzt : S.z * S.t = S.t * S.z := (C.isRefl_y.comm_E0_t C.isK_k C.z_mem_E0).symm
    have h3 : C.w₁' * (C.v' * S.t) * C.w₁'⁻¹ = C.v' * S.t := by
      rw [conj_mul_eq, h1, C.w₁'_t]
      calc S.z * C.v' * (S.t * S.z) = C.v' * (S.z * S.t) * S.z := by rw [hzv]; group
        _ = C.v' * S.t * (S.z * S.z) := by rw [hzt]; group
        _ = C.v' * S.t := by rw [zz S, mul_one]
    calc C.v' * S.t * C.w₁' = C.w₁' * (C.v' * S.t) * C.w₁'⁻¹ * C.w₁' := by rw [h3]
      _ = C.w₁' * (C.v' * S.t) := by group
  have hVw : ∀ c ∈ V, c * C.w₁' = C.w₁' * c := by
    intro c hc
    have hle : V ≤ centralizer ({C.w₁'} : Set X) := by
      refine zpowers_le.mpr ?_
      rw [mem_centralizer_singleton_iff]
      exact hw'v't
    exact mem_centralizer_singleton_iff.mp (hle hc)
  have htV : S.t ∈ normalizer (V : Set X) := by
    have : S.t * (C.v' * S.t) * S.t⁻¹ = C.F.kF * (C.v' * S.t) := by
      rw [show S.t * (C.v' * S.t) * S.t⁻¹ = (S.t * C.v' * S.t⁻¹) * S.t by group, C.t_v',
        mul_assoc]
    refine mem_normalizer_of_conj_gen ?_
    rw [this]; exact mul_mem hkV (mem_zpowers _)
  have hCV : C.D₁.Q₁ ⊓ centralizer (C.D₁.D₁₁ : Set X) ≤ V ⊔ zpowers S.t := by
    refine C.C_le.trans (sup_le (sup_le (zpowers_le.mpr (mem_sup_left hkV))
      (zpowers_le.mpr ?_)) le_sup_right)
    rw [show C.v' = (C.v' * S.t) * S.t⁻¹ by group]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (inv_mem (mem_sup_right (mem_zpowers _)))
  have hle : C.D₁.C₁ ≤ V := fun c hc => C.mem_of_mem_C₁ htV hCV hVw hc
  have hcardV : Nat.card V ≤ 4 := by
    rw [hV, Nat.card_zpowers]
    refine orderOf_le_of_pow_eq_one (by norm_num) ?_
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two (C.v' * S.t), hsq, C.F.kF_sq]
  have heq : C.D₁.C₁ = V := Subgroup.eq_of_le_of_card_ge hle (by rw [C.D₁.card_C₁]; exact hcardV)
  rw [heq]
  exact mem_zpowers _

theorem v't_comm_Q0 (hq : C.D₁.q0 = .e4q8) {a : X} (ha : a ∈ C.Q₀) :
    (C.v' * S.t) * a = a * (C.v' * S.t) :=
  C.D₁.C₁_comm _ (C.v't_mem_C₁ hq) a ha

theorem u_w₂ : ∃ e ∈ C.E₀, C.D₁.u * C.D₁.w₂ * C.D₁.u⁻¹ = e * (C.D₁.w₁ * C.D₁.w₂) := by
  set a := C.D₁.u * C.D₁.w₂ * C.D₁.u⁻¹ with ha
  have hut : C.D₁.u * S.t * C.D₁.u⁻¹ = S.t := conj_eq_of_comm (C.u_comm_B t_mem_B)
  have hut' : C.D₁.u⁻¹ * S.t * C.D₁.u = S.t := by
    calc C.D₁.u⁻¹ * S.t * C.D₁.u = C.D₁.u⁻¹ * (C.D₁.u * S.t * C.D₁.u⁻¹) * C.D₁.u := by
          rw [hut]
      _ = S.t := by group
  have hat : a * S.t * a⁻¹ = S.t * (S.z * C.F.yF) := by
    rw [ha, show C.D₁.u * C.D₁.w₂ * C.D₁.u⁻¹ * S.t * (C.D₁.u * C.D₁.w₂ * C.D₁.u⁻¹)⁻¹ =
      C.D₁.u * (C.D₁.w₂ * (C.D₁.u⁻¹ * S.t * C.D₁.u) * C.D₁.w₂⁻¹) * C.D₁.u⁻¹ by group, hut',
      C.w₂_t, conj_mul_eq, hut, C.u_y]
  have hcomm : ∀ e ∈ C.E₀, ∀ b : X, (e * b) * S.t * (e * b)⁻¹ = e * (b * S.t * b⁻¹) * e⁻¹ :=
    fun e _ b => by group
  have hfix : ∀ e ∈ C.E₀, ∀ f ∈ C.E₀, e * (S.t * f) * e⁻¹ = S.t * f := fun e he f hf =>
    conj_eq_of_comm (comm_mul_of (C.t_comm_E0 he).symm (C.comm_E0 he hf))
  have hzy : S.z * C.F.yF ≠ S.z := fun h => C.y_ne_one (by simpa using h)
  have hzy' : S.z * C.F.yF ≠ C.F.yF := fun h => S.z_ne_one (by simpa using h)
  rcases C.mem_Q₀ (C.u_conj_Q₀ C.w₂_mem_Q0) with h | h | h | h
  · exfalso
    have : a * S.t * a⁻¹ = S.t := conj_eq_of_comm (C.t_comm_E0 h).symm
    rw [hat] at this
    exact C.zy_ne_one (by simpa using this)
  · exfalso
    have e1 : a = (a * C.D₁.w₁⁻¹) * C.D₁.w₁ := by group
    have : a * S.t * a⁻¹ = S.t * S.z := by
      rw [e1, hcomm _ h, C.w₁_t, hfix _ h _ C.z_mem_E0]
    rw [hat] at this
    exact hzy (mul_left_cancel this)
  · exfalso
    have e1 : a = (a * C.D₁.w₂⁻¹) * C.D₁.w₂ := by group
    have : a * S.t * a⁻¹ = S.t * C.F.yF := by
      rw [e1, hcomm _ h, C.w₂_t, hfix _ h _ C.y_mem_E0]
    rw [hat] at this
    exact hzy' (mul_left_cancel this)
  · exact ⟨_, h, by rw [ha]; simp [mul_assoc]⟩

theorem w₁w₂_sq : (C.D₁.w₁ * C.D₁.w₂) ^ 2 =
    (C.D₁.w₁ * C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹)⁻¹ * C.D₁.w₁ ^ 2 * C.D₁.w₂ ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c, c = C.D₁.w₁ * C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹ := ⟨_, rfl⟩
  rw [← hc]
  have hcE : c ∈ C.E₀ := hc ▸ C.comm_w₁w₂_mem
  have hw : C.D₁.w₂ * C.D₁.w₁ = c⁻¹ * (C.D₁.w₁ * C.D₁.w₂) := by rw [hc]; group
  calc (C.D₁.w₁ * C.D₁.w₂) ^ 2 = C.D₁.w₁ * (C.D₁.w₂ * C.D₁.w₁) * C.D₁.w₂ := by
        rw [pow_two]; group
    _ = C.D₁.w₁ * (c⁻¹ * (C.D₁.w₁ * C.D₁.w₂)) * C.D₁.w₂ := by rw [hw]
    _ = (C.D₁.w₁ * c⁻¹) * C.D₁.w₁ * (C.D₁.w₂ * C.D₁.w₂) := by group
    _ = (c⁻¹ * C.D₁.w₁) * C.D₁.w₁ * (C.D₁.w₂ * C.D₁.w₂) := by
        rw [← C.comm_of_mem_E0 (inv_mem hcE) C.w₁_mem_Q0]
    _ = c⁻¹ * C.D₁.w₁ ^ 2 * C.D₁.w₂ ^ 2 := by rw [pow_two, pow_two]; group

theorem comm_w₁w₂ : C.D₁.w₁ * C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹ = C.F.kF := by
  have h := C.D₁.q0_holds
  rcases C.hq with hq | hq <;> rw [hq] at h
  · obtain ⟨hw₁, hw₂, -, -⟩ := h
    obtain ⟨e, he, hu⟩ := C.u_w₂
    have h1 : (C.D₁.u * C.D₁.w₂ * C.D₁.u⁻¹) ^ 2 = C.F.kF := by
      rw [show (C.D₁.u * C.D₁.w₂ * C.D₁.u⁻¹) ^ 2 = C.D₁.u * C.D₁.w₂ ^ 2 * C.D₁.u⁻¹ by
        rw [pow_two, pow_two]; group, hw₂, conj_eq_of_comm (C.u_comm_B (kF_mem_B C.F))]
    rw [hu, pow_two, show e * (C.D₁.w₁ * C.D₁.w₂) * (e * (C.D₁.w₁ * C.D₁.w₂)) =
      (e * e) * ((C.D₁.w₁ * C.D₁.w₂) * (C.D₁.w₁ * C.D₁.w₂)) by
        rw [mul_assoc e, ← mul_assoc _ e, ← C.comm_of_mem_E0 he
          (mul_mem C.w₁_mem_Q0 C.w₂_mem_Q0)]; group, ← pow_two e,
      (C.isRefl_y.elemAbelianTwo_E0 C.isK_k).sq_eq_one e he, one_mul, ← pow_two, C.w₁w₂_sq,
      hw₁, hw₂, mul_assoc, C.kk, mul_one, inv_eq_iff_eq_inv] at h1
    rw [h1]
    exact inv_eq_of_mul_eq_one_right C.kk
  · exact h.2.2.1

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
