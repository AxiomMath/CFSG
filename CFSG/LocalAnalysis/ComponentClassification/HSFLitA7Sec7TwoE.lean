module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Two

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_of_conj_gens [Finite X] {a b g : X}
    (ha : g * a * g⁻¹ ∈ zpowers a ⊔ zpowers b) (hb : g * b * g⁻¹ ∈ zpowers a ⊔ zpowers b) :
    g ∈ normalizer ((zpowers a ⊔ zpowers b : Subgroup X) : Set X) := by
  have hle : (zpowers a ⊔ zpowers b : Subgroup X).map (MulAut.conj g).toMonoidHom ≤
      zpowers a ⊔ zpowers b := by
    rw [map_le_iff_le_comap]
    exact sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb)
  refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj g).injective]

namespace Setup

variable {S : A7Base X} (C : Setup S)

abbrev Et₀ : Subgroup X := S.E0 (C.F.xF * C.F.yF) (S.z * C.F.kF)

abbrev Qt₀ : Subgroup X := S.Q0 (C.F.xF * C.F.yF) (S.z * C.F.kF) C.D₂.w₁ C.D₂.w₂

theorem z_mem_Et0 : S.z ∈ C.Et₀ := subset_closure (by simp)

theorem xy_mem_Et0 : C.F.xF * C.F.yF ∈ C.Et₀ := subset_closure (by simp)

theorem zk_mem_Et0 : S.z * C.F.kF ∈ C.Et₀ := subset_closure (by simp)

theorem k_mem_Et0 : C.F.kF ∈ C.Et₀ := by
  have := mul_mem (inv_mem C.z_mem_Et0) C.zk_mem_Et0
  rwa [inv_mul_cancel_left] at this

theorem Et0_le_Qt0 : C.Et₀ ≤ C.Qt₀ := le_sup_left.trans le_sup_left

theorem wt₂_mem_Qt0 : C.D₂.w₂ ∈ C.Qt₀ := mem_sup_right (mem_zpowers _)

theorem ut_form : ∃ b ∈ Bzt S, C.D₂.u = b * C.F.yF := by
  have hz : S.z ∈ Bzt S := mem_sup_left (mem_zpowers _)
  have ht : S.t ∈ Bzt S := mem_sup_right (mem_zpowers _)
  rcases C.D₂.u_eq with h | h <;> rcases C.hu₂ with h' | h'
  · exact ⟨S.z, hz, by rw [h, h']⟩
  · exact ⟨1, one_mem _, by rw [h, h', one_mul]⟩
  · exact ⟨S.t * S.z, mul_mem ht hz, by rw [h, h', mul_assoc]⟩
  · exact ⟨S.t, ht, by rw [h, h']⟩

theorem y_conj_xy : C.F.yF * (C.F.xF * C.F.yF) * C.F.yF⁻¹ = S.z * (C.F.xF * C.F.yF) := by
  have h1 : C.F.yF * C.F.xF * C.F.yF⁻¹ = C.F.xF⁻¹ := C.F.yF_inv
  calc C.F.yF * (C.F.xF * C.F.yF) * C.F.yF⁻¹ = (C.F.yF * C.F.xF * C.F.yF⁻¹) * C.F.yF := by
        group
    _ = S.z * (C.F.xF * C.F.yF) := by rw [h1, xF_inv, mul_assoc]

theorem ut_conj_xy : C.D₂.u * (C.F.xF * C.F.yF) * C.D₂.u⁻¹ = S.z * (C.F.xF * C.F.yF) := by
  obtain ⟨b, hb, hu⟩ := C.ut_form
  have hbB := zt_le_B hb
  rw [hu, show b * C.F.yF * (C.F.xF * C.F.yF) * (b * C.F.yF)⁻¹ =
    b * (C.F.yF * (C.F.xF * C.F.yF) * C.F.yF⁻¹) * b⁻¹ by group, C.y_conj_xy]
  exact conj_eq_of_comm (S.central_of_mem_B hbB (mul_mem z_mem_T C.xy_mem_T))

theorem ut_conj_z : C.D₂.u * S.z * C.D₂.u⁻¹ = S.z := by
  obtain ⟨b, hb, hu⟩ := C.ut_form
  have hut : C.D₂.u ∈ S.data.T := by
    rw [hu]; exact mul_mem (S.B_le_T (zt_le_B hb)) (yF_mem_T C.F)
  exact conj_eq_of_comm (S.central_of_mem_B z_mem_B hut).symm

theorem act₂_two : C.D₂.act = .two := by
  cases hact : C.D₂.act with
  | two => rfl
  | one =>
    exfalso
    have hA := C.D₂.act_holds
    rw [hact] at hA
    obtain ⟨hE0, -, -, -⟩ := hA
    set V : Subgroup X := zpowers S.z ⊔ zpowers (C.F.xF * C.F.yF) with hV
    have hzV : S.z ∈ V := mem_sup_left (mem_zpowers _)
    have hxyV : C.F.xF * C.F.yF ∈ V := mem_sup_right (mem_zpowers _)
    have hcent : ∀ g : X, (∀ e ∈ C.Et₀, g * e * g⁻¹ = e) → g ∈ normalizer (V : Set X) := by
      intro g hg
      refine mem_normalizer_of_conj_gens ?_ ?_
      · rw [hg _ C.z_mem_Et0]; exact hzV
      · rw [hg _ C.xy_mem_Et0]; exact hxyV
    have hS : C.D₂.S₁ ≤ normalizer (V : Set X) := by
      rw [C.D₂.S₁_eq]
      refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
      · intro e he
        refine hcent e fun a ha => ?_
        have hel := (isRefl_xyF C.F).elemAbelianTwo_E
        exact conj_eq_of_comm (hel.comm e he a (E0_le_E (isK_zkF C.F) _ ha))
      · exact zpowers_le.mpr (hcent _ fun e he => (hE0 e he).1)
      · exact zpowers_le.mpr (hcent _ fun e he => (hE0 e he).2.1)
      · exact zpowers_le.mpr (hcent _ fun e he => (hE0 e he).2.2)
      · refine zpowers_le.mpr (mem_normalizer_of_conj_gens ?_ ?_)
        · rw [C.ut_conj_z]; exact hzV
        · rw [C.ut_conj_xy]; exact mul_mem hzV hxyV
    have hw := hS (C.D₂.T₁_le C.w₁'_mem_T₁)
    have hmem := conj_mem_of_mem_normalizer hw hxyV
    have hVR : V ≤ S.data.R := sup_le (zpowers_le.mpr S.z_mem) (zpowers_le.mpr (xyF_mem_R C.F))
    apply C.F.kF_not_mem
    refine mem_sup_left (hVR ?_)
    rcases C.w₁'_xy with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hmem
    · have := mul_mem hmem (inv_mem hxyV)
      rwa [mul_inv_cancel_right] at this
    · have := mul_mem (inv_mem hzV) (mul_mem hmem (inv_mem hxyV))
      rwa [mul_inv_cancel_right, inv_mul_cancel_left] at this

theorem hact₂ : S.ActHolds (C.F.xF * C.F.yF) (S.z * C.F.kF) C.D₂.v C.D₂.w₁ C.D₂.w₂ .two := by
  have h := C.D₂.act_holds
  rw [C.act₂_two] at h
  exact h

theorem wt₂_z : C.D₂.w₂ * S.z * C.D₂.w₂⁻¹ = S.z * (S.z * C.F.kF) := C.hact₂.2.2.2.2.2.2.1

theorem wt₂_z_ne : C.D₂.w₂ * S.z * C.D₂.w₂⁻¹ ≠ S.z := by
  rw [C.wt₂_z]
  intro h
  exact (isK_zkF C.F).ne_one (by simpa using h)

theorem q0₂_extraspecial : C.D₂.q0 = .extraspecial := by
  have h := C.D₂.q0_holds
  have hz := C.Et0_le_Qt0 C.z_mem_Et0
  have hcomm_fail : C.D₂.w₂ * S.z ≠ S.z * C.D₂.w₂ := fun h' =>
    C.wt₂_z_ne (by rw [h', mul_inv_cancel_right])
  cases hq : C.D₂.q0 with
  | elem => rw [hq] at h; exact absurd (h.1 _ C.wt₂_mem_Qt0 _ hz) hcomm_fail
  | homocyclic => rw [hq] at h; exact absurd (h.2.2.1 _ C.wt₂_mem_Qt0 _ hz) hcomm_fail
  | e4q8 =>
    rw [hq] at h
    exact absurd (((h.2.2.1 _ hz).mpr C.z_mem_Et0) _ C.wt₂_mem_Qt0).symm hcomm_fail
  | exceptional =>
    rw [hq] at h
    exact absurd (((h.2.2.2.1 _ hz).mpr C.z_mem_Et0) _ C.wt₂_mem_Qt0).symm hcomm_fail
  | extraspecial => rfl

abbrev Zz : Subgroup X := zpowers S.z ⊔ zpowers C.F.kF

theorem Zz_le_B : C.Zz ≤ S.B := sup_le (zpowers_le.mpr z_mem_B) (zpowers_le.mpr (kF_mem_B C.F))

theorem Zz_eq' : C.Zz = zpowers (S.z * C.F.kF) ⊔ zpowers S.z := by
  apply le_antisymm
  · refine sup_le (zpowers_le.mpr (mem_sup_right (mem_zpowers _))) (zpowers_le.mpr ?_)
    have := mul_mem (inv_mem (show S.z ∈ (zpowers (S.z * C.F.kF) ⊔ zpowers S.z : Subgroup X) from
      mem_sup_right (mem_zpowers _))) (show S.z * C.F.kF ∈ (zpowers (S.z * C.F.kF) ⊔
        zpowers S.z : Subgroup X) from mem_sup_left (mem_zpowers _))
    rwa [inv_mul_cancel_left] at this
  · exact sup_le (zpowers_le.mpr (mul_mem (mem_sup_left (mem_zpowers _))
      (mem_sup_right (mem_zpowers _)))) (zpowers_le.mpr (mem_sup_left (mem_zpowers _)))

theorem k_not_mem_zpowers_z : C.F.kF ∉ zpowers S.z := fun h =>
  (isK_kF C.F).not_mem (mem_sup_left h)

theorem z_not_mem_zpowers_zk : S.z ∉ zpowers (S.z * C.F.kF) := by
  intro h
  rcases eq_one_or_eq_of_mem_zpowers (isK_zkF C.F).sq h with h1 | h1
  · exact S.z_ne_one h1
  · exact (isK_kF C.F).ne_one (by
      have := congrArg (S.z⁻¹ * ·) h1
      simpa using this.symm)

theorem parity_z {c d : X} (hc : c ∈ C.Zz) (hd : d ∈ C.Zz) :
    c * d ∈ zpowers S.z ↔ (c ∈ zpowers S.z ↔ d ∈ zpowers S.z) :=
  mul_mem_zpowers_iff (commute_of_mem_B z_mem_B (kF_mem_B C.F)) C.F.kF_sq C.k_not_mem_zpowers_z
    hc hd

theorem parity_zk {c d : X} (hc : c ∈ C.Zz) (hd : d ∈ C.Zz) :
    c * d ∈ zpowers (S.z * C.F.kF) ↔
      (c ∈ zpowers (S.z * C.F.kF) ↔ d ∈ zpowers (S.z * C.F.kF)) := by
  rw [C.Zz_eq'] at hc hd
  exact mul_mem_zpowers_iff (commute_of_mem_B (mul_mem z_mem_B (kF_mem_B C.F)) z_mem_B) z_sq
    C.z_not_mem_zpowers_zk hc hd

theorem fix_Zz {g : X} (hz : g * S.z * g⁻¹ = S.z) (hk : g * C.F.kF * g⁻¹ = C.F.kF) {c : X}
    (hc : c ∈ C.Zz) : g * c * g⁻¹ = c := by
  have hzel : ElemAbelianTwo (zpowers S.z) :=
    ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr z_mem_B ha) (zpowers_le.mpr z_mem_B hb),
      fun a ha => S.sq_of_mem_B (zpowers_le.mpr z_mem_B ha)⟩
  rcases mem_or_of_mem_sup hzel C.F.kF_sq (fun a ha => commute_of_mem_B (kF_mem_B C.F)
      (zpowers_le.mpr z_mem_B ha)) hc with h | h
  · rcases eq_one_or_eq_of_mem_zpowers z_sq h with rfl | rfl
    · group
    · exact hz
  · have hc' : c = (c * C.F.kF) * C.F.kF := by rw [mul_assoc, C.kk, mul_one]
    rw [hc', conj_mul_eq, hk]
    rcases eq_one_or_eq_of_mem_zpowers z_sq h with h1 | h1 <;> rw [h1]
    · group
    · rw [hz]

def H₂ : Subgroup X where
  carrier := {g | g * S.z * g⁻¹ = S.z ∧ g * C.F.kF * g⁻¹ = C.F.kF ∧
    S.t⁻¹ * (g * S.t * g⁻¹) ∈ C.Zz ∧
    (C.F.xF * C.F.yF)⁻¹ * (g * (C.F.xF * C.F.yF) * g⁻¹) ∈ C.Zz ∧
    (S.t⁻¹ * (g * S.t * g⁻¹) ∈ zpowers (S.z * C.F.kF) ↔
      (C.F.xF * C.F.yF)⁻¹ * (g * (C.F.xF * C.F.yF) * g⁻¹) ∈ zpowers S.z)}
  mul_mem' := by
    rintro g h ⟨hgz, hgk, hga, hgb, hgp⟩ ⟨hhz, hhk, hha, hhb, hhp⟩
    set xy := C.F.xF * C.F.yF
    have ea : S.t⁻¹ * (g * h * S.t * (g * h)⁻¹) =
        (S.t⁻¹ * (g * S.t * g⁻¹)) * (S.t⁻¹ * (h * S.t * h⁻¹)) := by
      have h1 : g * h * S.t * (g * h)⁻¹ =
          (g * S.t * g⁻¹) * (g * (S.t⁻¹ * (h * S.t * h⁻¹)) * g⁻¹) := by group
      rw [h1, C.fix_Zz hgz hgk hha]; group
    have eb : xy⁻¹ * (g * h * xy * (g * h)⁻¹) =
        (xy⁻¹ * (g * xy * g⁻¹)) * (xy⁻¹ * (h * xy * h⁻¹)) := by
      have h1 : g * h * xy * (g * h)⁻¹ =
          (g * xy * g⁻¹) * (g * (xy⁻¹ * (h * xy * h⁻¹)) * g⁻¹) := by group
      rw [h1, C.fix_Zz hgz hgk hhb]; group
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc g * h * S.z * (g * h)⁻¹ = g * (h * S.z * h⁻¹) * g⁻¹ := by group
        _ = S.z := by rw [hhz, hgz]
    · calc g * h * C.F.kF * (g * h)⁻¹ = g * (h * C.F.kF * h⁻¹) * g⁻¹ := by group
        _ = C.F.kF := by rw [hhk, hgk]
    · rw [ea]; exact mul_mem hga hha
    · rw [eb]; exact mul_mem hgb hhb
    · rw [ea, eb, C.parity_zk hga hha, C.parity_z hgb hhb, hgp, hhp]
  one_mem' := by
    refine ⟨by group, by group, ?_, ?_, ?_⟩
    · rw [show S.t⁻¹ * (1 * S.t * 1⁻¹) = 1 by group]; exact one_mem _
    · rw [show (C.F.xF * C.F.yF)⁻¹ * (1 * (C.F.xF * C.F.yF) * 1⁻¹) = 1 by group]; exact one_mem _
    · rw [show S.t⁻¹ * (1 * S.t * 1⁻¹) = 1 by group,
        show (C.F.xF * C.F.yF)⁻¹ * (1 * (C.F.xF * C.F.yF) * 1⁻¹) = 1 by group]
      exact iff_of_true (one_mem _) (one_mem _)
  inv_mem' := by
    rintro g ⟨hgz, hgk, hga, hgb, hgp⟩
    set xy := C.F.xF * C.F.yF
    have hz' : g⁻¹ * S.z * g⁻¹⁻¹ = S.z := by
      calc g⁻¹ * S.z * g⁻¹⁻¹ = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hgz, inv_inv]
        _ = S.z := by group
    have hk' : g⁻¹ * C.F.kF * g⁻¹⁻¹ = C.F.kF := by
      calc g⁻¹ * C.F.kF * g⁻¹⁻¹ = g⁻¹ * (g * C.F.kF * g⁻¹) * g := by rw [hgk, inv_inv]
        _ = C.F.kF := by group
    have hZel : ∀ c ∈ C.Zz, c⁻¹ = c := fun c hc =>
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact S.sq_of_mem_B (C.Zz_le_B hc))
    have ea : S.t⁻¹ * (g⁻¹ * S.t * g⁻¹⁻¹) = S.t⁻¹ * (g * S.t * g⁻¹) := by
      have h1 := C.fix_Zz hz' hk' hga
      have : g⁻¹ * S.t * g⁻¹⁻¹ = S.t * (S.t⁻¹ * (g * S.t * g⁻¹))⁻¹ := by
        calc g⁻¹ * S.t * g⁻¹⁻¹ = g⁻¹ * (g * S.t * g⁻¹) * g * (g⁻¹ * (S.t⁻¹ *
              (g * S.t * g⁻¹)) * g⁻¹⁻¹)⁻¹ := by group
          _ = S.t * (S.t⁻¹ * (g * S.t * g⁻¹))⁻¹ := by rw [h1]; group
      rw [this, inv_mul_cancel_left, hZel _ hga]
    have eb : xy⁻¹ * (g⁻¹ * xy * g⁻¹⁻¹) = xy⁻¹ * (g * xy * g⁻¹) := by
      have h1 := C.fix_Zz hz' hk' hgb
      have : g⁻¹ * xy * g⁻¹⁻¹ = xy * (xy⁻¹ * (g * xy * g⁻¹))⁻¹ := by
        calc g⁻¹ * xy * g⁻¹⁻¹ = g⁻¹ * (g * xy * g⁻¹) * g * (g⁻¹ * (xy⁻¹ *
              (g * xy * g⁻¹)) * g⁻¹⁻¹)⁻¹ := by group
          _ = xy * (xy⁻¹ * (g * xy * g⁻¹))⁻¹ := by rw [h1]; group
      rw [this, inv_mul_cancel_left, hZel _ hgb]
    exact ⟨hz', hk', ea ▸ hga, eb ▸ hgb, by rw [ea, eb]; exact hgp⟩

theorem T_le_H₂ : S.data.T ≤ C.H₂ := by
  intro g hg
  have hcz : g * S.z * g⁻¹ = S.z := conj_eq_of_comm (S.central_of_mem_B z_mem_B hg).symm
  have hck : g * C.F.kF * g⁻¹ = C.F.kF :=
    conj_eq_of_comm (S.central_of_mem_B (kF_mem_B C.F) hg).symm
  have hct : g * S.t * g⁻¹ = S.t := conj_eq_of_comm (S.data.commute_t hg)
  have hb : (C.F.xF * C.F.yF)⁻¹ * (g * (C.F.xF * C.F.yF) * g⁻¹) ∈ zpowers S.z := by
    rcases S.commutator_eq hg C.xy_mem_T with h | h
    · rw [show g * (C.F.xF * C.F.yF) * g⁻¹ = g * (C.F.xF * C.F.yF) * g⁻¹ *
          (C.F.xF * C.F.yF)⁻¹ * (C.F.xF * C.F.yF) by group, h, one_mul, inv_mul_cancel]
      exact one_mem _
    · rw [show g * (C.F.xF * C.F.yF) * g⁻¹ = g * (C.F.xF * C.F.yF) * g⁻¹ *
          (C.F.xF * C.F.yF)⁻¹ * (C.F.xF * C.F.yF) by group, h,
        S.central_of_mem_B z_mem_B C.xy_mem_T, inv_mul_cancel_left]
      exact mem_zpowers _
  refine ⟨hcz, hck, ?_, mem_sup_left hb, ?_⟩
  · rw [hct, inv_mul_cancel]; exact one_mem _
  · rw [hct, inv_mul_cancel]; exact iff_of_true (one_mem _) hb

theorem vt_mem_H₂ : C.D₂.v ∈ C.H₂ := by
  obtain ⟨hE0, hv, -⟩ := C.hact₂
  have hz := hE0 _ C.z_mem_Et0
  have hk := hE0 _ C.k_mem_Et0
  have hxy := hE0 _ C.xy_mem_Et0
  refine ⟨hz, hk, ?_, ?_, ?_⟩
  · rw [hv, inv_mul_cancel_left]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  · rw [hxy, inv_mul_cancel]; exact one_mem _
  · rw [hv, inv_mul_cancel_left, hxy, inv_mul_cancel]
    exact iff_of_true (mem_zpowers _) (one_mem _)

theorem wt₁_mem_H₂ : C.D₂.w₁ ∈ C.H₂ := by
  obtain ⟨-, -, hw₁t, -, hw₁z, -, -, hw₁y, hw₁k, -⟩ := C.hact₂
  have hk : C.D₂.w₁ * C.F.kF * C.D₂.w₁⁻¹ = C.F.kF := by
    calc C.D₂.w₁ * C.F.kF * C.D₂.w₁⁻¹ =
          (C.D₂.w₁ * S.z * C.D₂.w₁⁻¹)⁻¹ * (C.D₂.w₁ * (S.z * C.F.kF) * C.D₂.w₁⁻¹) := by group
      _ = C.F.kF := by rw [hw₁k, hw₁z]; group
  have ha : S.t⁻¹ * (C.D₂.w₁ * S.t * C.D₂.w₁⁻¹) = C.F.kF := by
    rw [hw₁t, show S.t⁻¹ * (S.t * S.z * (S.z * C.F.kF)) = (S.z * S.z) * C.F.kF by group, zz S,
      one_mul]
  have hb : (C.F.xF * C.F.yF)⁻¹ * (C.D₂.w₁ * (C.F.xF * C.F.yF) * C.D₂.w₁⁻¹) =
      S.z * C.F.kF := by
    rw [hw₁y, inv_mul_cancel_left]
  refine ⟨hw₁z, hk, ?_, ?_, ?_⟩
  · rw [ha]; exact mem_sup_right (mem_zpowers _)
  · rw [hb]; exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  · rw [ha, hb]
    refine iff_of_false ?_ ?_
    · intro h
      rcases eq_one_or_eq_of_mem_zpowers (isK_zkF C.F).sq h with h1 | h1
      · exact (isK_kF C.F).ne_one h1
      · exact S.z_ne_one (by
          have := congrArg (· * C.F.kF⁻¹) h1
          simpa using this.symm)
    · intro h
      rcases eq_one_or_eq_of_mem_zpowers z_sq h with h1 | h1
      · exact (isK_zkF C.F).ne_one h1
      · exact (isK_kF C.F).ne_one (by
          have := congrArg (S.z⁻¹ * ·) h1
          simpa using this)

theorem T₁_le_H₂ : C.T₁ ≤ C.H₂ := by
  rw [show C.T₁ = S.data.T ⊔ zpowers C.D₂.v ⊔ zpowers C.D₂.w₁ from C.D₂.T₁_eq]
  exact sup_le (sup_le C.T_le_H₂ (zpowers_le.mpr C.vt_mem_H₂)) (zpowers_le.mpr C.wt₁_mem_H₂)

theorem u_t_form : ∃ c ∈ zpowers S.z, C.D₁.u = c * S.t * (C.F.xF * C.F.yF) := by
  rcases C.u_cases with ⟨c, hc, hu⟩ | h
  · exfalso
    have hvH := C.T₁_le_H₂ C.v_mem_T₁
    obtain ⟨-, -, -, -, hp⟩ := hvH
    have hcE : c ∈ C.E₀ := (zpowers_le.mpr C.z_mem_E0) hc
    have hvc : C.D₁.v * c * C.D₁.v⁻¹ = c := C.v_E0 hcE
    have hvxy : C.D₁.v * (C.F.xF * C.F.yF) * C.D₁.v⁻¹ = C.F.xF * C.F.yF := by
      have h1 : C.D₁.v * C.D₁.u * C.D₁.v⁻¹ = C.D₁.u := by
        rw [← C.u_comm_v, mul_inv_cancel_right]
      have h2 : C.D₁.v * (C.F.xF * C.F.yF) * C.D₁.v⁻¹ =
          (C.D₁.v * c * C.D₁.v⁻¹)⁻¹ * (C.D₁.v * C.D₁.u * C.D₁.v⁻¹) := by rw [hu]; group
      rw [h2, h1, hvc, hu, inv_mul_cancel_left]
    rw [Setup.v_t, hvxy, inv_mul_cancel_left, inv_mul_cancel] at hp
    have hk := hp.mpr (one_mem _)
    rcases eq_one_or_eq_of_mem_zpowers (isK_zkF C.F).sq hk with h1 | h1
    · exact (isK_kF C.F).ne_one h1
    · exact S.z_ne_one (by
        have := congrArg (· * C.F.kF⁻¹) h1
        simpa using this.symm)
  · exact h

theorem v_xy : C.D₁.v * (C.F.xF * C.F.yF) * C.D₁.v⁻¹ = C.F.kF * (C.F.xF * C.F.yF) := by
  obtain ⟨c, hc, hu⟩ := C.u_t_form
  have hcE : c ∈ C.E₀ := (zpowers_le.mpr C.z_mem_E0) hc
  have h1 : C.D₁.v * C.D₁.u * C.D₁.v⁻¹ = C.D₁.u := by
    rw [← C.u_comm_v, mul_inv_cancel_right]
  have h2 : C.D₁.v * (C.F.xF * C.F.yF) * C.D₁.v⁻¹ =
      (C.D₁.v * S.t * C.D₁.v⁻¹)⁻¹ * (C.D₁.v * c * C.D₁.v⁻¹)⁻¹ *
        (C.D₁.v * C.D₁.u * C.D₁.v⁻¹) := by rw [hu]; group
  have hkinv : C.F.kF⁻¹ = C.F.kF := inv_eq_of_mul_eq_one_right C.kk
  rw [h2, h1, C.v_E0 hcE, Setup.v_t, hu]
  have hkc : C.F.kF * c = c * C.F.kF := commute_of_mem_B (kF_mem_B C.F) (zpow_z_mem_B hc)
  have hkt : C.F.kF * S.t = S.t * C.F.kF := commute_of_mem_B (kF_mem_B C.F) t_mem_B
  calc (S.t * C.F.kF)⁻¹ * c⁻¹ * (c * S.t * (C.F.xF * C.F.yF)) =
        C.F.kF⁻¹ * (C.F.xF * C.F.yF) := by group
    _ = C.F.kF * (C.F.xF * C.F.yF) := by rw [hkinv]

theorem w₁'_xy' : C.w₁' * (C.F.xF * C.F.yF) * C.w₁'⁻¹ = S.z * C.F.kF * (C.F.xF * C.F.yF) := by
  rcases C.w₁'_xy with ⟨-, c, hc, hu⟩ | ⟨h, -⟩
  · exfalso
    obtain ⟨c', hc', hu'⟩ := C.u_t_form
    apply t_not_mem_zt' (S := S)
    have : S.t = c'⁻¹ * c := by
      have := hu.symm.trans hu'
      calc S.t = c'⁻¹ * (c' * S.t * (C.F.xF * C.F.yF)) * (C.F.xF * C.F.yF)⁻¹ := by group
        _ = c'⁻¹ * c := by rw [← this]; group
    rw [this]
    exact mul_mem (inv_mem hc') hc
  · exact h

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
