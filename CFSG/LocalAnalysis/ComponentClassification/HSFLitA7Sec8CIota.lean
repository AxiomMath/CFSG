module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Rel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MCFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Fus

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace VSide

variable (V : VSide S F T₁)

theorem E_le_S₁ : S.E V.yi ≤ V.D.S₁ := by
  rw [V.D.S₁_eq]; exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))

theorem yi_mem_S₁ : V.yi ∈ V.D.S₁ := V.E_le_S₁ (mem_E_self _)

theorem B_le_S₁ : S.B ≤ V.D.S₁ := (B_le_E V.yi).trans V.E_le_S₁

theorem E0_le_Q0 : S.E0 V.yi V.ki ≤ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ :=
  le_sup_left.trans le_sup_left

theorem not_conjTo_of_mem_Q0 {q : X} (hq : q ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂) :
    ¬ ConjTo S.t q := V.D.no_conj_extraspecial V.hq q hq

theorem u_comm_vN' : V.D.u * V.vN * V.D.u⁻¹ = V.vN := by
  rw [V.u_comm_vN, mul_inv_cancel_right]

theorem conj_E {e f : X} (he : e ∈ S.E V.yi) (hf : f ∈ S.E V.yi) : e * f * e⁻¹ = f := by
  rw [V.hyi.elemAbelianTwo_E.comm _ he _ hf, mul_inv_cancel_right]

end VSide

namespace CPair

variable (P : CPair S F T₁)

theorem pcX : MC.PcX P.w₂N P.V.D.u P.w₁N P.V.vN S.z P.V.yi S.t P.V.ki where
  w₂_sq := P.w₂N_sq
  w₂_u := P.w₂N_conj_u
  w₂_w₁ := P.w₂N_conj_w₁N
  w₂_v := P.w₂N_conj_vN
  w₂_z := P.w₂N_conj_z
  w₂_y := P.w₂N_conj_yi
  w₂_t := P.w₂N_conj_t
  w₂_k := P.w₂N_conj_ki
  u_sq := P.V.u_mul_u
  u_w₁ := P.u_conj_w₁N
  u_v := P.V.u_comm_vN'
  u_z := P.V.u_conj_B z_mem_B
  u_y := P.V.u_conj_yi
  u_t := P.V.u_conj_B t_mem_B
  u_k := P.V.u_conj_B P.V.hki.mem
  w₁_sq := P.w₁N_sq
  w₁_v := P.w₁N_conj_vN
  w₁_z := P.w₁N_conj_z
  w₁_y := P.w₁N_conj_yi
  w₁_t := P.w₁N_conj_t
  w₁_k := P.w₁N_conj_ki
  v_sq := by rw [← pow_two, P.V.vN_sq]
  v_z := P.V.vN_conj_z
  v_y := P.V.vN_conj_yi
  v_t := P.V.vN_conj_t
  v_k := P.V.vN_conj_ki
  z_sq := z_mul_z
  z_y := P.V.conj_E (z_mem_E _) (mem_E_self _)
  z_t := P.V.conj_E (z_mem_E _) (t_mem_E _)
  z_k := P.V.conj_E (z_mem_E _) (B_le_E _ P.V.hki.mem)
  y_sq := P.V.yi_mul_yi
  y_t := P.V.conj_E (mem_E_self _) (t_mem_E _)
  y_k := P.V.conj_E (mem_E_self _) (B_le_E _ P.V.hki.mem)
  t_sq := t_mul_t
  t_k := P.V.conj_E (t_mem_E _) (B_le_E _ P.V.hki.mem)
  k_sq := P.V.ki_sq

noncomputable def ι : MC →* X := Classical.choose (MC.exists_hom P.pcX)

theorem ι_spec : P.ι MC.w₂ = P.w₂N ∧ P.ι MC.u = P.V.D.u ∧ P.ι MC.w₁ = P.w₁N ∧
    P.ι MC.v = P.V.vN ∧ P.ι MC.z = S.z ∧ P.ι MC.y = P.V.yi ∧ P.ι MC.t = S.t ∧
      P.ι MC.k = P.V.ki :=
  Classical.choose_spec (MC.exists_hom P.pcX)

theorem ι_w₂ : P.ι MC.w₂ = P.w₂N := P.ι_spec.1
theorem ι_u : P.ι MC.u = P.V.D.u := P.ι_spec.2.1
theorem ι_w₁ : P.ι MC.w₁ = P.w₁N := P.ι_spec.2.2.1
theorem ι_v : P.ι MC.v = P.V.vN := P.ι_spec.2.2.2.1
theorem ι_z : P.ι MC.z = S.z := P.ι_spec.2.2.2.2.1
theorem ι_y : P.ι MC.y = P.V.yi := P.ι_spec.2.2.2.2.2.1
theorem ι_t : P.ι MC.t = S.t := P.ι_spec.2.2.2.2.2.2.1
theorem ι_k : P.ι MC.k = P.V.ki := P.ι_spec.2.2.2.2.2.2.2

theorem ι_injective : Function.Injective P.ι :=
  MC.injective_of P.ι (by rw [P.ι_k]; exact P.V.hki.ne_one)

theorem w₂N_mem_S₁ : P.w₂N ∈ P.V.D.S₁ := by
  rcases P.w₂N_eq with h | h <;> rw [h]
  · exact P.V.w₂_mem_S₁
  · exact mul_mem P.V.yi_mem_S₁ P.V.w₂_mem_S₁

theorem cN_mem_S₁ : P.cN ∈ P.V.D.S₁ := P.V.B_le_S₁ P.cN_mem_B

theorem w₁N_mem_S₁ : P.w₁N ∈ P.V.D.S₁ := by
  rw [P.w₁N_eq]; exact mul_mem P.V.w₁_mem_S₁ P.cN_mem_S₁

theorem range_ι : P.ι.range = P.V.D.S₁ := by
  apply le_antisymm
  · refine MC.range_le P.ι fun g hg => ?_
    simp only [MC.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [P.ι_w₂]; exact P.w₂N_mem_S₁
    · rw [P.ι_u]; exact P.V.u_mem_S₁
    · rw [P.ι_w₁]; exact P.w₁N_mem_S₁
    · rw [P.ι_v]; exact P.V.vN_mem_S₁
    · rw [P.ι_z]; exact P.V.B_le_S₁ z_mem_B
    · rw [P.ι_y]; exact P.V.yi_mem_S₁
    · rw [P.ι_t]; exact P.V.B_le_S₁ t_mem_B
    · rw [P.ι_k]; exact P.V.B_le_S₁ P.V.hki.mem
  · have hz : S.z ∈ P.ι.range := ⟨MC.z, P.ι_z⟩
    have hy : P.V.yi ∈ P.ι.range := ⟨MC.y, P.ι_y⟩
    have ht : S.t ∈ P.ι.range := ⟨MC.t, P.ι_t⟩
    have hk : P.V.ki ∈ P.ι.range := ⟨MC.k, P.ι_k⟩
    have hv : P.V.vN ∈ P.ι.range := ⟨MC.v, P.ι_v⟩
    have hB : S.B ≤ P.ι.range := by
      rw [P.V.B_eq]
      exact sup_le (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hk)) (zpowers_le.mpr ht)
    have hcN : P.cN ∈ P.ι.range := hB P.cN_mem_B
    rw [P.V.D.S₁_eq]
    refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) (zpowers_le.mpr ⟨MC.u, P.ι_u⟩)
    · rw [E_eq]; exact sup_le hB (zpowers_le.mpr hy)
    · refine zpowers_le.mpr ?_
      rcases P.V.vN_eq with h | h
      · rw [← h]; exact hv
      · have : P.V.D.v = P.V.vN * S.t⁻¹ := by rw [h]; group
        rw [this]; exact mul_mem hv (inv_mem ht)
    · refine zpowers_le.mpr ?_
      have : P.V.D.w₁ = P.w₁N * P.cN⁻¹ := by rw [P.w₁N_eq]; group
      rw [this]; exact mul_mem ⟨MC.w₁, P.ι_w₁⟩ (inv_mem hcN)
    · refine zpowers_le.mpr ?_
      rcases P.w₂N_eq with h | h
      · rw [← h]; exact ⟨MC.w₂, P.ι_w₂⟩
      · have : P.V.D.w₂ = P.V.yi⁻¹ * P.w₂N := by rw [h]; group
        rw [this]; exact mul_mem (inv_mem hy) ⟨MC.w₂, P.ι_w₂⟩

theorem mem_range_of_mem_S₁ {g : X} (hg : g ∈ P.V.D.S₁) : ∃ x : MC, P.ι x = g := by
  rw [← P.range_ι] at hg
  exact hg

theorem w₂N_mem_Q0 : P.w₂N ∈ S.Q0 P.V.yi P.V.ki P.V.D.w₁ P.V.D.w₂ := by
  rcases P.w₂N_eq with h | h <;> rw [h]
  · exact P.V.w₂_mem_Q0'
  · exact mul_mem (P.V.E0_le_Q0 (yi_mem_E0 _ _)) P.V.w₂_mem_Q0'

theorem w₁N_mem_Q0 : P.w₁N ∈ S.Q0 P.V.yi P.V.ki P.V.D.w₁ P.V.D.w₂ := by
  rw [P.w₁N_eq]
  refine mul_mem P.V.w₁_mem_Q0 (P.V.E0_le_Q0 ?_)
  rcases P.cN_eq with h | h <;> rw [h]
  · exact one_mem _
  · exact ki_mem_E0 _ _

theorem ι_mem_Q0 {x : MC} (hx : MC.inQ0 x = true) :
    P.ι x ∈ S.Q0 P.V.yi P.V.ki P.V.D.w₁ P.V.D.w₂ := by
  refine map_mem_of_inSpan P.ι (MC.Q0_span x hx) fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · rw [P.ι_w₂]; exact P.w₂N_mem_Q0
  · rw [P.ι_w₁]; exact P.w₁N_mem_Q0
  · rw [P.ι_z]; exact P.V.E0_le_Q0 (z_mem_E0 _ _)
  · rw [P.ι_y]; exact P.V.E0_le_Q0 (yi_mem_E0 _ _)
  · rw [P.ι_k]; exact P.V.E0_le_Q0 (ki_mem_E0 _ _)

@[expose] noncomputable def Fside : Subgroup X := S.E0 P.V.yi P.V.ki ⊔ zpowers P.W.D.w₁

theorem m_comm_E0 {e : X} (he : e ∈ S.E0 P.V.yi P.V.ki) : P.W.D.w₁ * e = e * P.W.D.w₁ := by
  obtain ⟨c, hc, hm⟩ := P.exists_m_eq'
  have heE : e ∈ S.E P.V.yi := E0_le_E P.V.hki P.V.yi he
  have hyc : P.V.yi * c ∈ S.E P.V.yi := mul_mem (mem_E_self _) (B_le_E _ (zk_le_B P.V.hki hc))
  have h1 : P.V.vN * e = e * P.V.vN := by
    calc P.V.vN * e = (P.V.vN * e * P.V.vN⁻¹) * P.V.vN := by group
      _ = e * P.V.vN := by rw [P.V.vN_conj_E0 he]
  rw [hm]
  calc P.V.vN * P.V.yi * c * e = P.V.vN * ((P.V.yi * c) * e) := by group
    _ = P.V.vN * (e * (P.V.yi * c)) := by rw [P.V.hyi.elemAbelianTwo_E.comm _ hyc _ heE]
    _ = (P.V.vN * e) * (P.V.yi * c) := by group
    _ = e * (P.V.vN * P.V.yi * c) := by rw [h1]; group

theorem m_not_mem_E0 : P.W.D.w₁ ∉ S.E0 P.V.yi P.V.ki := by
  intro h
  have h1 := P.m_conj_t
  rw [S.data.commute_t (P.V.hyi.E_le_T (E0_le_E P.V.hki P.V.yi h)), mul_inv_cancel_right] at h1
  exact P.V.hki.ne_one (mul_eq_left.mp h1.symm)

theorem m_sq : P.W.D.w₁ ^ 2 = 1 := P.W.w₁_sq

theorem elemAbelianTwo_Fside : ElemAbelianTwo P.Fside :=
  elemAbelianTwo_sup (P.V.hyi.elemAbelianTwo_E0 P.V.hki) P.m_sq fun _ he => P.m_comm_E0 he

theorem card_Fside : Nat.card P.Fside = 16 := by
  rw [Fside, card_sup_of_not_mem (P.V.hyi.elemAbelianTwo_E0 P.V.hki) P.m_sq P.m_not_mem_E0
    fun _ he => P.m_comm_E0 he, P.V.hyi.card_E0 P.V.hki]

theorem not_conjTo_Fside (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
    (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)) {a : X} (ha : a ∈ P.Fside) :
    ¬ ConjTo S.t a := by
  refine not_conjTo_of_gens D₁ D₂ P.elemAbelianTwo_Fside P.card_Fside
    (s := (S.E0 P.V.yi P.V.ki : Set X) ∪ {P.W.D.w₁}) ?_ ?_ ?_ ha
  · rintro x (hx | hx)
    · exact mem_sup_left hx
    · rw [Set.mem_singleton_iff.mp hx]; exact mem_sup_right (mem_zpowers _)
  · refine sup_le ?_ (zpowers_le.mpr (subset_closure (Or.inr rfl)))
    intro x hx
    exact subset_closure (Or.inl hx)
  · rintro x (hx | hx)
    · exact P.V.not_conjTo_of_mem_Q0 (P.V.E0_le_Q0 hx)
    · rw [Set.mem_singleton_iff.mp hx]
      exact P.W.not_conjTo_of_mem_Q0 (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem ι_mem_Fside {x : MC} (hx : MC.inF1 x = true) : P.ι x ∈ P.Fside := by
  obtain ⟨c, hc, hm⟩ := P.exists_m_eq'
  refine map_mem_of_inSpan P.ι (MC.F1_span x hx) fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · rw [P.ι_v]
    have : P.V.vN = P.W.D.w₁ * (P.V.yi * c)⁻¹ := by rw [hm]; group
    rw [this]
    refine mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (inv_mem (mul_mem
      (yi_mem_E0 _ _) ?_)))
    rw [E0_eq]; exact mem_sup_left hc
  · rw [P.ι_z]; exact mem_sup_left (z_mem_E0 _ _)
  · rw [P.ι_y]; exact mem_sup_left (yi_mem_E0 _ _)
  · rw [P.ι_k]; exact mem_sup_left (ki_mem_E0 _ _)

@[expose] noncomputable def Fother : Subgroup X := S.E0 P.W.yi P.W.ki ⊔ zpowers P.V.D.w₁

theorem xyi_mem_E0W' : S.t * P.V.D.u ∈ S.E0 P.W.yi P.W.ki := by
  rw [P.V.u_eq, ← mul_assoc, t_mul_t, one_mul]
  exact P.xyi_mem_E0W

theorem ki_mem_E0W : P.V.ki ∈ S.E0 P.W.yi P.W.ki := by
  have : P.V.ki = S.z * P.W.ki := by rw [P.hkk, ← mul_assoc, z_mul_z, one_mul]
  rw [this]
  exact mul_mem (z_mem_E0 _ _) (ki_mem_E0 _ _)

theorem ι_mem_Fother {x : MC} (hx : MC.inF2 x = true) : P.ι x ∈ P.Fother := by
  refine map_mem_of_inSpan P.ι (MC.F2_span x hx) fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · rw [P.ι_w₁, P.w₁N_eq]
    refine mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left ?_)
    rcases P.cN_eq with h | h <;> rw [h]
    · exact one_mem _
    · exact P.ki_mem_E0W
  · rw [P.ι_z]; exact mem_sup_left (z_mem_E0 _ _)
  · rw [P.ι_k]; exact mem_sup_left P.ki_mem_E0W
  · rw [map_mul, P.ι_t, P.ι_u]; exact mem_sup_left P.xyi_mem_E0W'

theorem ι_mem_EW {x : MC} (hx : MC.inE2 x = true) : P.ι x ∈ S.E P.W.yi := by
  have hE0 : S.E0 P.W.yi P.W.ki ≤ S.E P.W.yi := E0_le_E P.W.hki P.W.yi
  refine map_mem_of_inSpan P.ι (MC.E2_span x hx) fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · rw [P.ι_u]
    have : P.V.D.u = S.t * (S.t * P.V.D.u) := by rw [← mul_assoc, t_mul_t, one_mul]
    rw [this]
    exact mul_mem (t_mem_E _) (hE0 P.xyi_mem_E0W')
  · rw [P.ι_z]; exact z_mem_E _
  · rw [P.ι_t]; exact t_mem_E _
  · rw [P.ι_k]; exact hE0 P.ki_mem_E0W

end CPair

end Sec8

end CFSG.ComponentClassification.HSFLit
