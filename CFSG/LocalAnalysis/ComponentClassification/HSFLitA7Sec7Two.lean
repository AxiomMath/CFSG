module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Basic

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem card_sup_zpowers_eq {H : Subgroup X} {g : X} (hg : g ∈ normalizer (H : Set X))
    (hg2 : g ^ 2 ∈ H) (hgH : g ∉ H) : Nat.card (H ⊔ zpowers g : Subgroup X) = 2 * Nat.card H := by
  set K := H ⊔ zpowers g with hK
  have hHK : H ≤ K := le_sup_left
  have hgK : g ∈ K := mem_sup_right (mem_zpowers g)
  have hidx : (H.subgroupOf K).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨g, hgK⟩, fun b => ?_⟩
    simp only [mem_subgroupOf, Subgroup.coe_mul]
    rcases mem_or_of_mem_sup_zpowers hg hg2 b.2 with h | h
    · refine Or.inr ⟨h, fun h' => hgH ?_⟩
      have := mul_mem (inv_mem h) h'
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, fun h' => hgH ?_⟩
      · have := mul_mem h hg2
        rwa [pow_two, show (b : X) * g⁻¹ * (g * g) = b * g by group] at this
      · have := mul_mem (inv_mem h') h
        rw [inv_mul_cancel_left] at this
        simpa using inv_mem this
  have hmul := Subgroup.relIndex_mul_card H K
  rw [inf_eq_left.mpr hHK] at hmul
  rw [← hmul]
  exact congrArg (· * Nat.card H) hidx

structure Setup (S : A7Base X) where
  F : S.Frame
  T₁ : Subgroup X
  h4 : S.Sec4 F T₁
  hnc : ¬ SubConj F.E₁ F.E₂
  u₁ : X
  u₂ : X
  hu₁ : u₁ = F.xF * F.yF ∨ u₁ = S.z * (F.xF * F.yF)
  hu₂ : u₂ = S.z * F.yF ∨ u₂ = F.yF
  D₁ : S.Sec6 T₁ F.yF F.kF u₁
  D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) u₂
  hq : D₁.q0 = .e4q8 ∨ D₁.q0 = .exceptional

namespace Setup

variable {S : A7Base X} (C : Setup S)

abbrev E₀ : Subgroup X := S.E0 C.F.yF C.F.kF

abbrev Q₀ : Subgroup X := S.Q0 C.F.yF C.F.kF C.D₁.w₁ C.D₁.w₂

theorem isRefl_y : IsRefl C.F C.F.yF := isRefl_yF C.F

theorem isK_k : IsK (S := S) C.F.kF := isK_kF C.F

theorem E0_le_Q0 : C.E₀ ≤ C.Q₀ := le_sup_left.trans le_sup_left

theorem w₁_mem_Q0 : C.D₁.w₁ ∈ C.Q₀ := mem_sup_left (mem_sup_right (mem_zpowers _))

theorem w₂_mem_Q0 : C.D₁.w₂ ∈ C.Q₀ := mem_sup_right (mem_zpowers _)

theorem centerEq : CenterEq C.Q₀ C.E₀ := by
  have h := C.D₁.q0_holds
  rcases C.hq with hq | hq <;> rw [hq] at h
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem comm_of_mem_E0 {a b : X} (ha : a ∈ C.E₀) (hb : b ∈ C.Q₀) : a * b = b * a :=
  ((C.centerEq a (C.E0_le_Q0 ha)).mpr ha) b hb

theorem act_one : C.D₁.act = .one := by
  cases hact : C.D₁.act with
  | one => rfl
  | two =>
    exfalso
    have h := C.D₁.act_holds
    rw [hact] at h
    have hy : C.F.yF ∈ C.E₀ := subset_closure (by simp)
    have hcomm := C.comm_of_mem_E0 hy C.w₁_mem_Q0
    have hwy : C.D₁.w₁ * C.F.yF * C.D₁.w₁⁻¹ = C.F.yF := by
      rw [← hcomm, mul_inv_cancel_right]
    rw [h.2.2.2.2.2.2.2.1] at hwy
    exact C.isK_k.ne_one (by simpa using hwy)

theorem hact : S.ActHolds C.F.yF C.F.kF C.D₁.v C.D₁.w₁ C.D₁.w₂ .one := by
  have h := C.D₁.act_holds
  rw [C.act_one] at h
  exact h

theorem w₁_sq_mem : C.D₁.w₁ ^ 2 ∈ C.E₀ := by
  have h := C.D₁.q0_holds
  rcases C.hq with hq | hq <;> rw [hq] at h
  · rw [h.1]; exact subset_closure (by simp)
  · rw [h.1]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem w₂_sq_mem : C.D₁.w₂ ^ 2 ∈ C.E₀ := by
  have h := C.D₁.q0_holds
  rcases C.hq with hq | hq <;> rw [hq] at h
  · rw [h.2.1]; exact subset_closure (by simp)
  · rw [h.2.1]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem w₁_normalizes : C.D₁.w₁ ∈ normalizer (C.E₀ : Set X) := by
  refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun e he => ?_)
  exact C.comm_of_mem_E0 he C.w₁_mem_Q0

theorem w₁_t : C.D₁.w₁ * S.t * C.D₁.w₁⁻¹ = S.t * S.z := C.hact.2.2.1

theorem w₂_t : C.D₁.w₂ * S.t * C.D₁.w₂⁻¹ = S.t * C.F.yF := C.hact.2.2.2

theorem v_t : C.D₁.v * S.t * C.D₁.v⁻¹ = S.t * C.F.kF := C.hact.2.1

theorem v_E0 {e : X} (he : e ∈ C.E₀) : C.D₁.v * e * C.D₁.v⁻¹ = e := (C.hact.1 e he).1

theorem w₁_E0 {e : X} (he : e ∈ C.E₀) : C.D₁.w₁ * e * C.D₁.w₁⁻¹ = e := (C.hact.1 e he).2.1

theorem w₂_E0 {e : X} (he : e ∈ C.E₀) : C.D₁.w₂ * e * C.D₁.w₂⁻¹ = e := (C.hact.1 e he).2.2

end Setup

omit [Finite X] in
theorem conj_mul_eq (g a b : X) : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group

omit [Finite X] in
theorem conj_inv_eq_of {g a b : X} (hga : g * a * g⁻¹ = a * b) (hgb : g * b * g⁻¹ = b)
    (hb2 : b * b = 1) : g⁻¹ * a * g = a * b := by
  have h1 : g⁻¹ * b * g = b := by
    calc g⁻¹ * b * g = g⁻¹ * (g * b * g⁻¹) * g := by rw [hgb]
      _ = b := by group
  calc g⁻¹ * a * g = g⁻¹ * a * g * (b * b) := by rw [hb2, mul_one]
    _ = (g⁻¹ * a * g * (g⁻¹ * b * g)) * b := by rw [h1]; group
    _ = (g⁻¹ * (a * b) * g) * b := by group
    _ = (g⁻¹ * (g * a * g⁻¹) * g) * b := by rw [hga]
    _ = a * b := by group

omit [Finite X] in
theorem conj_eq_of_comm {e a : X} (h : e * a = a * e) : e * a * e⁻¹ = a := by
  rw [h, mul_inv_cancel_right]

omit [Finite X] in
theorem comm_mul_of {e a b : X} (h1 : e * a = a * e) (h2 : e * b = b * e) :
    e * (a * b) = a * b * e := by
  rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem zz (S : A7Base X) : S.z * S.z = 1 := by rw [← pow_two, z_sq]

abbrev Bzt (S : A7Base X) : Subgroup X := zpowers S.z ⊔ zpowers S.t

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem z_mem_E0 : S.z ∈ C.E₀ := subset_closure (by simp)

theorem y_mem_E0 : C.F.yF ∈ C.E₀ := subset_closure (by simp)

theorem k_mem_E0 : C.F.kF ∈ C.E₀ := subset_closure (by simp)

theorem yy : C.F.yF * C.F.yF = 1 := by rw [← pow_two, C.F.yF_sq]

theorem y_ne_one : C.F.yF ≠ 1 := fun h => C.isRefl_y.not_mem_B (h ▸ one_mem _)

theorem zy_ne_one : S.z * C.F.yF ≠ 1 := by
  intro h
  apply C.isRefl_y.not_mem_B
  have : C.F.yF = S.z⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [this]
  exact inv_mem z_mem_B

theorem t_comm_E0 {e : X} (he : e ∈ C.E₀) : S.t * e = e * S.t :=
  C.isRefl_y.comm_E0_t C.isK_k he

theorem comm_E0 {a b : X} (ha : a ∈ C.E₀) (hb : b ∈ C.E₀) : a * b = b * a :=
  (C.isRefl_y.elemAbelianTwo_E0 C.isK_k).comm a ha b hb

theorem w₁_inv_t : C.D₁.w₁⁻¹ * S.t * C.D₁.w₁ = S.t * S.z :=
  conj_inv_eq_of C.w₁_t (C.w₁_E0 C.z_mem_E0) (zz S)

theorem w₂_inv_t : C.D₁.w₂⁻¹ * S.t * C.D₁.w₂ = S.t * C.F.yF :=
  conj_inv_eq_of C.w₂_t (C.w₂_E0 C.y_mem_E0) C.yy

theorem comm_w₁w₂_mem : C.D₁.w₁ * C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹ ∈ C.E₀ := by
  set c := C.D₁.w₁ * C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹ with hc
  have hQ₀ : Nat.card C.Q₀ = 32 := by
    have h := C.D₁.q0_holds
    rcases C.hq with hq | hq <;> rw [hq] at h
    · exact h.2.2.2
    · exact h.2.2.2.2
  have hw₁0 : C.D₁.w₁ ∉ C.E₀ := fun h => S.z_ne_one (by
    have h1 := C.w₁_t
    rw [conj_eq_of_comm (C.t_comm_E0 h).symm] at h1
    simpa using h1.symm)
  have hP : Nat.card (C.E₀ ⊔ zpowers C.D₁.w₁ : Subgroup X) = 16 := by
    rw [card_sup_zpowers_eq C.w₁_normalizes C.w₁_sq_mem hw₁0, C.isRefl_y.card_E0 C.isK_k]
  have hPQ : C.E₀ ⊔ zpowers C.D₁.w₁ ≤ C.Q₀ := sup_le C.E0_le_Q0 (zpowers_le.mpr C.w₁_mem_Q0)
  have hidx : (C.E₀ ⊔ zpowers C.D₁.w₁).relIndex C.Q₀ = 2 := by
    have hmul := Subgroup.relIndex_mul_card (C.E₀ ⊔ zpowers C.D₁.w₁) C.Q₀
    rw [inf_eq_left.mpr hPQ, hP, hQ₀] at hmul
    omega
  have hN := normal_of_index_eq_two hidx
  have hw : C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹ ∈ C.E₀ ⊔ zpowers C.D₁.w₁ := by
    have := hN.conj_mem ⟨C.D₁.w₁⁻¹, inv_mem C.w₁_mem_Q0⟩
      (mem_subgroupOf.mpr (inv_mem (mem_sup_right (mem_zpowers _)))) ⟨C.D₁.w₂, C.w₂_mem_Q0⟩
    exact mem_subgroupOf.mp this
  have hcS : c ∈ C.E₀ ⊔ zpowers C.D₁.w₁ := by
    rw [hc, show C.D₁.w₁ * C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹ =
      C.D₁.w₁ * (C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹) by group]
    exact mul_mem (mem_sup_right (mem_zpowers _)) hw
  rcases mem_or_of_mem_sup_zpowers C.w₁_normalizes C.w₁_sq_mem hcS with h | h
  · exact h
  · exfalso
    have hct : c * S.t * c⁻¹ = S.t := by
      have e1 : C.D₁.w₂⁻¹ * S.t * C.D₁.w₂ = S.t * C.F.yF := C.w₂_inv_t
      have e2 : C.D₁.w₁⁻¹ * (S.t * C.F.yF) * C.D₁.w₁ = S.t * S.z * C.F.yF := by
        have := conj_mul_eq C.D₁.w₁⁻¹ S.t C.F.yF
        rw [inv_inv] at this
        rw [this, C.w₁_inv_t]
        have hy : C.D₁.w₁⁻¹ * C.F.yF * C.D₁.w₁ = C.F.yF := by
          have := C.w₁_E0 C.y_mem_E0
          calc C.D₁.w₁⁻¹ * C.F.yF * C.D₁.w₁ = C.D₁.w₁⁻¹ * (C.D₁.w₁ * C.F.yF * C.D₁.w₁⁻¹) *
                C.D₁.w₁ := by rw [this]
            _ = C.F.yF := by group
        rw [hy]
      have e3 : C.D₁.w₂ * (S.t * S.z * C.F.yF) * C.D₁.w₂⁻¹ = S.t * S.z := by
        rw [conj_mul_eq, conj_mul_eq, C.w₂_t, C.w₂_E0 C.z_mem_E0, C.w₂_E0 C.y_mem_E0,
          show S.t * C.F.yF * S.z * C.F.yF = S.t * S.z * (C.F.yF * C.F.yF) by
            rw [mul_assoc S.t, mul_assoc S.t, C.comm_E0 C.y_mem_E0 C.z_mem_E0]; group,
          C.yy, mul_one]
      have e4 : C.D₁.w₁ * (S.t * S.z) * C.D₁.w₁⁻¹ = S.t := by
        rw [conj_mul_eq, C.w₁_t, C.w₁_E0 C.z_mem_E0, mul_assoc, (zz S), mul_one]
      calc c * S.t * c⁻¹ = C.D₁.w₁ * (C.D₁.w₂ * (C.D₁.w₁⁻¹ * (C.D₁.w₂⁻¹ * S.t * C.D₁.w₂) *
            C.D₁.w₁) * C.D₁.w₂⁻¹) * C.D₁.w₁⁻¹ := by rw [hc]; group
        _ = S.t := by rw [e1, e2, e3, e4]
    set e := c * C.D₁.w₁⁻¹ with he
    have hce : c = e * C.D₁.w₁ := by rw [he]; group
    have hcomm : e * (S.t * S.z) = S.t * S.z * e :=
      comm_mul_of (C.t_comm_E0 h).symm (C.comm_E0 h C.z_mem_E0)
    have : c * S.t * c⁻¹ = S.t * S.z := by
      calc c * S.t * c⁻¹ = e * (C.D₁.w₁ * S.t * C.D₁.w₁⁻¹) * e⁻¹ := by rw [hce]; group
        _ = S.t * S.z := by rw [C.w₁_t, conj_eq_of_comm hcomm]
    rw [hct] at this
    exact S.z_ne_one (by simpa using this)

abbrev P₀ : Subgroup X := C.E₀ ⊔ zpowers C.D₁.w₁

theorem w₂_conj_w₁ : C.D₁.w₂ * C.D₁.w₁ * C.D₁.w₂⁻¹ =
    (C.D₁.w₁ * C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹)⁻¹ * C.D₁.w₁ := by group

theorem w₂_normalizes_P₀ : C.D₁.w₂ ∈ normalizer (C.P₀ : Set X) := by
  have hle : C.P₀.map (MulAut.conj C.D₁.w₂).toMonoidHom ≤ C.P₀ := by
    rw [map_le_iff_le_comap]
    refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
    · show C.D₁.w₂ * e * C.D₁.w₂⁻¹ ∈ C.P₀
      rw [C.w₂_E0 he]
      exact mem_sup_left he
    · show C.D₁.w₂ * C.D₁.w₁ * C.D₁.w₂⁻¹ ∈ C.P₀
      rw [C.w₂_conj_w₁]
      exact mul_mem (mem_sup_left (inv_mem C.comm_w₁w₂_mem)) (mem_sup_right (mem_zpowers _))
  refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj C.D₁.w₂).injective]

theorem mem_Q₀ {a : X} (ha : a ∈ C.Q₀) :
    a ∈ C.E₀ ∨ a * C.D₁.w₁⁻¹ ∈ C.E₀ ∨ a * C.D₁.w₂⁻¹ ∈ C.E₀ ∨
      a * C.D₁.w₂⁻¹ * C.D₁.w₁⁻¹ ∈ C.E₀ := by
  rcases mem_or_of_mem_sup_zpowers C.w₂_normalizes_P₀ (mem_sup_left C.w₂_sq_mem) ha with h | h
  · rcases mem_or_of_mem_sup_zpowers C.w₁_normalizes C.w₁_sq_mem h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases mem_or_of_mem_sup_zpowers C.w₁_normalizes C.w₁_sq_mem h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

theorem conj_t_of_mem_E0 {e g : X} (he : e ∈ C.E₀) (hg : g * S.t * g⁻¹ = S.t * S.z ∨
    g * S.t * g⁻¹ = S.t * C.F.yF ∨ g * S.t * g⁻¹ = S.t * (S.z * C.F.yF)) :
    (e * g) * S.t * (e * g)⁻¹ = S.t * S.z ∨ (e * g) * S.t * (e * g)⁻¹ = S.t * C.F.yF ∨
      (e * g) * S.t * (e * g)⁻¹ = S.t * (S.z * C.F.yF) := by
  have hc : ∀ b ∈ C.E₀, e * (S.t * b) * e⁻¹ = S.t * b := fun b hb =>
    conj_eq_of_comm (comm_mul_of (C.t_comm_E0 he).symm (C.comm_E0 he hb))
  have : (e * g) * S.t * (e * g)⁻¹ = e * (g * S.t * g⁻¹) * e⁻¹ := by group
  rw [this]
  rcases hg with h | h | h <;> rw [h]
  · exact Or.inl (hc _ C.z_mem_E0)
  · exact Or.inr (Or.inl (hc _ C.y_mem_E0))
  · exact Or.inr (Or.inr (hc _ (mul_mem C.z_mem_E0 C.y_mem_E0)))

theorem mem_E0_of_mem_Q0 {a : X} (ha : a ∈ C.Q₀) (hat : a * S.t = S.t * a) : a ∈ C.E₀ := by
  have hfix : a * S.t * a⁻¹ = S.t := by rw [hat, mul_inv_cancel_right]
  have hne1 : S.t * S.z ≠ S.t := fun h => S.z_ne_one (by simpa using h)
  have hne2 : S.t * C.F.yF ≠ S.t := fun h => C.y_ne_one (by simpa using h)
  have hne3 : S.t * (S.z * C.F.yF) ≠ S.t := fun h => C.zy_ne_one (by simpa using h)
  rcases C.mem_Q₀ ha with h | h | h | h
  · exact h
  · exfalso
    have hd := C.conj_t_of_mem_E0 h (g := C.D₁.w₁) (Or.inl C.w₁_t)
    rw [show a * C.D₁.w₁⁻¹ * C.D₁.w₁ = a by group, hfix] at hd
    rcases hd with hd | hd | hd
    · exact hne1 hd.symm
    · exact hne2 hd.symm
    · exact hne3 hd.symm
  · exfalso
    have hd := C.conj_t_of_mem_E0 h (g := C.D₁.w₂) (Or.inr (Or.inl C.w₂_t))
    rw [show a * C.D₁.w₂⁻¹ * C.D₁.w₂ = a by group, hfix] at hd
    rcases hd with hd | hd | hd
    · exact hne1 hd.symm
    · exact hne2 hd.symm
    · exact hne3 hd.symm
  · exfalso
    have hw : (C.D₁.w₁ * C.D₁.w₂) * S.t * (C.D₁.w₁ * C.D₁.w₂)⁻¹ = S.t * (S.z * C.F.yF) := by
      calc (C.D₁.w₁ * C.D₁.w₂) * S.t * (C.D₁.w₁ * C.D₁.w₂)⁻¹ =
            C.D₁.w₁ * (C.D₁.w₂ * S.t * C.D₁.w₂⁻¹) * C.D₁.w₁⁻¹ := by group
        _ = S.t * (S.z * C.F.yF) := by
          rw [C.w₂_t, conj_mul_eq, C.w₁_t, C.w₁_E0 C.y_mem_E0, mul_assoc]
    have hd := C.conj_t_of_mem_E0 h (g := C.D₁.w₁ * C.D₁.w₂) (Or.inr (Or.inr hw))
    rw [show a * C.D₁.w₂⁻¹ * C.D₁.w₁⁻¹ * (C.D₁.w₁ * C.D₁.w₂) = a by group, hfix] at hd
    rcases hd with hd | hd | hd
    · exact hne1 hd.symm
    · exact hne2 hd.symm
    · exact hne3 hd.symm

theorem u_form : ∃ b ∈ Bzt S, C.D₁.u = b * (C.F.xF * C.F.yF) := by
  have hz : S.z ∈ Bzt S := mem_sup_left (mem_zpowers _)
  have ht : S.t ∈ Bzt S := mem_sup_right (mem_zpowers _)
  rcases C.D₁.u_eq with h | h <;> rcases C.hu₁ with h' | h'
  · exact ⟨1, one_mem _, by rw [h, h', one_mul]⟩
  · exact ⟨S.z, hz, by rw [h, h']⟩
  · exact ⟨S.t, ht, by rw [h, h']⟩
  · exact ⟨S.t * S.z, mul_mem ht hz, by rw [h, h', mul_assoc]⟩

theorem xy_mem_T : C.F.xF * C.F.yF ∈ S.data.T := (xyF_mem_R C.F).1

theorem u_mem_T : C.D₁.u ∈ S.data.T := by
  obtain ⟨b, hb, hu⟩ := C.u_form
  rw [hu]
  exact mul_mem (S.B_le_T (zt_le_B hb)) C.xy_mem_T

theorem u_mul_u : C.D₁.u * C.D₁.u = 1 := by
  obtain ⟨b, hb, hu⟩ := C.u_form
  have hbB := zt_le_B hb
  have hbc := S.central_of_mem_B hbB C.xy_mem_T
  rw [hu, show b * (C.F.xF * C.F.yF) * (b * (C.F.xF * C.F.yF)) =
      (b * b) * ((C.F.xF * C.F.yF) * (C.F.xF * C.F.yF)) by
    rw [mul_assoc, ← mul_assoc (C.F.xF * C.F.yF), ← hbc]; group,
    ← pow_two, ← pow_two, S.sq_of_mem_B hbB, xyF_sq, one_mul]

theorem u_inv : C.D₁.u⁻¹ = C.D₁.u := inv_eq_of_mul_eq_one_right C.u_mul_u

theorem u_comm_B {b : X} (hb : b ∈ S.B) : C.D₁.u * b = b * C.D₁.u :=
  (S.central_of_mem_B hb C.u_mem_T).symm

theorem u_y : C.D₁.u * C.F.yF * C.D₁.u⁻¹ = S.z * C.F.yF := by
  obtain ⟨b, hb, hu⟩ := C.u_form
  have hbB := zt_le_B hb
  rw [hu, show b * (C.F.xF * C.F.yF) * C.F.yF * (b * (C.F.xF * C.F.yF))⁻¹ =
      b * (C.F.xF * (C.F.yF * C.F.yF * C.F.yF⁻¹) * C.F.xF⁻¹) * b⁻¹ by group,
    mul_inv_cancel_right, xF_conj_yF]
  exact conj_eq_of_comm (S.central_of_mem_B hbB (mul_mem z_mem_T (yF_mem_T C.F)))

theorem u_conj_Q₀ {a : X} (ha : a ∈ C.Q₀) : C.D₁.u * a * C.D₁.u⁻¹ ∈ C.Q₀ := by
  have huS : C.D₁.u ∈ C.D₁.S₁ := by rw [C.D₁.S₁_eq]; exact mem_sup_right (mem_zpowers _)
  have hq : C.D₁.q0 = .homocyclic ∨ C.D₁.q0 = .e4q8 ∨ C.D₁.q0 = .exceptional :=
    Or.inr C.hq
  have hQ₁ : C.D₁.u ∈ normalizer (C.D₁.Q₁ : Set X) :=
    mem_normalizer_of_map_eq (C.D₁.Q₁_char hq C.D₁.u (le_normalizer huS))
  have hE : C.D₁.u ∈ normalizer (S.E C.F.yF : Set X) := C.D₁.S₁_le huS
  exact conj_mem_of_map_eq (C.D₁.Q0_invariant C.D₁.u ⟨hE, hQ₁⟩) ha

theorem mem_zk_of_mem_E0 {e : X} (he : e ∈ C.E₀) (hfix : C.D₁.u * e * C.D₁.u⁻¹ = e) :
    e ∈ (zpowers S.z ⊔ zpowers C.F.kF : Subgroup X) := by
  have he' : e ∈ S.E0 C.F.yF C.F.kF := he
  rw [E0_eq] at he'
  rcases mem_or_of_mem_sup (elemAbelianTwo_zk C.isK_k) C.F.yF_sq
      (fun _ hb => C.isRefl_y.comm_B (zk_le_B C.isK_k hb)) he' with h | h
  · exact h
  · exfalso
    set c := e * C.F.yF with hc
    have hcB := zk_le_B C.isK_k h
    have hec : e = c * C.F.yF := by rw [hc, mul_assoc, C.yy, mul_one]
    have : C.D₁.u * e * C.D₁.u⁻¹ = S.z * e := by
      rw [hec, show C.D₁.u * (c * C.F.yF) * C.D₁.u⁻¹ = (C.D₁.u * c * C.D₁.u⁻¹) *
          (C.D₁.u * C.F.yF * C.D₁.u⁻¹) by group, C.u_y, C.u_comm_B hcB, mul_inv_cancel_right,
        ← mul_assoc, (commute_of_mem_B hcB z_mem_B), mul_assoc]
    rw [hfix] at this
    exact S.z_ne_one (by simpa using this.symm)

theorem kk : C.F.kF * C.F.kF = 1 := by rw [← pow_two, C.F.kF_sq]

theorem u_conj_E0 {e : X} (he : e ∈ C.E₀) : C.D₁.u * e * C.D₁.u⁻¹ ∈ C.E₀ := by
  have he' : e ∈ S.E0 C.F.yF C.F.kF := he
  rw [E0_eq] at he'
  rcases mem_or_of_mem_sup (elemAbelianTwo_zk C.isK_k) C.F.yF_sq
      (fun _ hb => C.isRefl_y.comm_B (zk_le_B C.isK_k hb)) he' with h | h
  · rw [conj_eq_of_comm (C.u_comm_B (zk_le_B C.isK_k h))]; exact he
  · have hcB := zk_le_B C.isK_k h
    have hec : e = (e * C.F.yF) * C.F.yF := by rw [mul_assoc, C.yy, mul_one]
    rw [hec, conj_mul_eq, conj_eq_of_comm (C.u_comm_B hcB), C.u_y]
    exact mul_mem (mul_mem he C.y_mem_E0) (mul_mem C.z_mem_E0 C.y_mem_E0)

theorem mul_u_conj_mem {g : X} (hg : g ∈ C.E₀) :
    g * (C.D₁.u * g * C.D₁.u⁻¹) = 1 ∨ g * (C.D₁.u * g * C.D₁.u⁻¹) = S.z := by
  have hg' : g ∈ S.E0 C.F.yF C.F.kF := hg
  rw [E0_eq] at hg'
  rcases mem_or_of_mem_sup (elemAbelianTwo_zk C.isK_k) C.F.yF_sq
      (fun _ hb => C.isRefl_y.comm_B (zk_le_B C.isK_k hb)) hg' with h | h
  · left
    rw [conj_eq_of_comm (C.u_comm_B (zk_le_B C.isK_k h)), ← pow_two,
      (elemAbelianTwo_zk C.isK_k).sq_eq_one g h]
  · right
    set c := g * C.F.yF with hc
    have hcB := zk_le_B C.isK_k h
    have hgc : g = c * C.F.yF := by rw [hc, mul_assoc, C.yy, mul_one]
    rw [hgc, conj_mul_eq, conj_eq_of_comm (C.u_comm_B hcB), C.u_y]
    have hcy : C.F.yF * c = c * C.F.yF := (C.isRefl_y.comm_B hcB)
    have hzy : C.F.yF * S.z = S.z * C.F.yF := C.isRefl_y.comm_B z_mem_B
    calc c * C.F.yF * (c * (S.z * C.F.yF)) = (c * c) * S.z * (C.F.yF * C.F.yF) := by
          rw [show c * C.F.yF * (c * (S.z * C.F.yF)) = c * (C.F.yF * c) * S.z * C.F.yF by group,
            hcy, ← mul_assoc, mul_assoc (c * c) C.F.yF, hzy]
          group
      _ = S.z := by
          rw [← pow_two, (elemAbelianTwo_zk C.isK_k).sq_eq_one c h, C.yy, one_mul, mul_one]

theorem uw_eq_k {w : X} (hwQ : w ∈ C.Q₀) (hwE : ∀ e ∈ C.E₀, w * e * w⁻¹ = e)
    (hwt : w * S.t * w⁻¹ = S.t * S.z) (hw2 : w ^ 2 = C.D₁.w₁ ^ 2)
    (hf : C.D₁.u * w * C.D₁.u⁻¹ * w⁻¹ ∈ zpowers C.F.kF) :
    C.D₁.u * w * C.D₁.u⁻¹ * w⁻¹ = C.F.kF := by
  set u := C.D₁.u with hu
  set f := u * w * u⁻¹ * w⁻¹ with hfdef
  set g := (w * C.D₁.w₂)⁻¹ * (u * C.D₁.w₂ * u⁻¹) with hgdef
  have hut : u * S.t * u⁻¹ = S.t := conj_eq_of_comm (C.u_comm_B t_mem_B)
  have hA : (u * C.D₁.w₂ * u⁻¹) * S.t * (u * C.D₁.w₂ * u⁻¹)⁻¹ = S.t * (S.z * C.F.yF) := by
    calc (u * C.D₁.w₂ * u⁻¹) * S.t * (u * C.D₁.w₂ * u⁻¹)⁻¹ =
          u * (C.D₁.w₂ * (u⁻¹ * S.t * u) * C.D₁.w₂⁻¹) * u⁻¹ := by group
      _ = S.t * (S.z * C.F.yF) := by
        rw [show u⁻¹ * S.t * u = S.t by
            calc u⁻¹ * S.t * u = u⁻¹ * (u * S.t * u⁻¹) * u := by rw [hut]
              _ = S.t := by group,
          C.w₂_t, conj_mul_eq, hut, C.u_y]
  have hB : (w * C.D₁.w₂) * S.t * (w * C.D₁.w₂)⁻¹ = S.t * (S.z * C.F.yF) := by
    calc (w * C.D₁.w₂) * S.t * (w * C.D₁.w₂)⁻¹ = w * (C.D₁.w₂ * S.t * C.D₁.w₂⁻¹) * w⁻¹ := by
          group
      _ = S.t * (S.z * C.F.yF) := by rw [C.w₂_t, conj_mul_eq, hwt, hwE _ C.y_mem_E0, mul_assoc]
  have hgt : g * S.t = S.t * g := by
    have h1 : (w * C.D₁.w₂)⁻¹ * (u * C.D₁.w₂ * u⁻¹) * S.t * ((w * C.D₁.w₂)⁻¹ *
        (u * C.D₁.w₂ * u⁻¹))⁻¹ = S.t := by
      calc (w * C.D₁.w₂)⁻¹ * (u * C.D₁.w₂ * u⁻¹) * S.t * ((w * C.D₁.w₂)⁻¹ *
            (u * C.D₁.w₂ * u⁻¹))⁻¹ = (w * C.D₁.w₂)⁻¹ * ((u * C.D₁.w₂ * u⁻¹) * S.t *
            (u * C.D₁.w₂ * u⁻¹)⁻¹) * (w * C.D₁.w₂) := by group
        _ = (w * C.D₁.w₂)⁻¹ * ((w * C.D₁.w₂) * S.t * (w * C.D₁.w₂)⁻¹) * (w * C.D₁.w₂) := by
          rw [hA, hB]
        _ = S.t := by group
    calc g * S.t = g * S.t * g⁻¹ * g := by group
      _ = S.t * g := by rw [hgdef, h1]
  have hgQ : g ∈ C.Q₀ := mul_mem (inv_mem (mul_mem hwQ C.w₂_mem_Q0)) (C.u_conj_Q₀ C.w₂_mem_Q0)
  have hgE := C.mem_E0_of_mem_Q0 hgQ hgt
  have huw : u * w * u⁻¹ = f * w := by rw [hfdef]; group
  have huu : u * u = 1 := C.u_mul_u
  have hw₂ : C.D₁.w₂ = f * w * (w * C.D₁.w₂ * g) * (u * g * u⁻¹) := by
    calc C.D₁.w₂ = u * (u * C.D₁.w₂ * u⁻¹) * u⁻¹ := by
          rw [show u * (u * C.D₁.w₂ * u⁻¹) * u⁻¹ = (u * u) * C.D₁.w₂ * (u * u)⁻¹ by group,
            huu]
          group
      _ = (u * w * u⁻¹) * (u * C.D₁.w₂ * u⁻¹) * (u * g * u⁻¹) := by rw [hgdef]; group
      _ = f * w * (w * C.D₁.w₂ * g) * (u * g * u⁻¹) := by rw [huw, hgdef]; group
  have hfE : f ∈ C.E₀ := by
    have : f ∈ zpowers C.F.kF := hf
    exact (zpowers_le.mpr C.k_mem_E0) this
  have hguE := C.u_conj_E0 hgE
  have hw2E : w ^ 2 ∈ C.E₀ := hw2 ▸ C.w₁_sq_mem
  have hc1 : C.D₁.w₂ * (g * (u * g * u⁻¹)) = (g * (u * g * u⁻¹)) * C.D₁.w₂ :=
    (C.comm_of_mem_E0 (mul_mem hgE hguE) C.w₂_mem_Q0).symm
  have h2 : 1 * C.D₁.w₂ = (f * w ^ 2 * (g * (u * g * u⁻¹))) * C.D₁.w₂ := by
    rw [one_mul]
    conv_lhs => rw [hw₂]
    rw [pow_two]
    calc f * w * (w * C.D₁.w₂ * g) * (u * g * u⁻¹) = f * (w * w) * (C.D₁.w₂ *
          (g * (u * g * u⁻¹))) := by group
      _ = _ := by rw [hc1]; group
  have key : f * w ^ 2 * (g * (u * g * u⁻¹)) = 1 := (mul_right_cancel h2).symm
  have hfv : f = 1 ∨ f = C.F.kF := eq_one_or_eq_of_mem_zpowers C.F.kF_sq hf
  have hw1sq : C.D₁.w₁ ^ 2 = C.F.kF ∨ C.D₁.w₁ ^ 2 = S.z * C.F.kF := by
    have h := C.D₁.q0_holds
    rcases C.hq with hq | hq <;> rw [hq] at h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hk1 : C.F.kF ≠ 1 := C.isK_k.ne_one
  have hzk1 : S.z * C.F.kF ≠ 1 := (isK_zkF C.F).ne_one
  have hkz : C.F.kF * S.z = S.z * C.F.kF := commute_of_mem_B (kF_mem_B C.F) z_mem_B
  rw [hw2] at key
  have hf' : f = (C.D₁.w₁ ^ 2 * (g * (u * g * u⁻¹)))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact key)
  have hkk : C.F.kF⁻¹ = C.F.kF := inv_eq_of_mul_eq_one_right C.kk
  have hzkzk : (S.z * C.F.kF) * (S.z * C.F.kF) = 1 := by
    rw [mul_assoc, ← mul_assoc C.F.kF, hkz, mul_assoc, C.kk, mul_one, zz S]
  rcases C.mul_u_conj_mem hgE with hg1 | hg1 <;> rw [hg1] at hf' <;>
    rcases hw1sq with hs | hs <;> rw [hs] at hf'
  · rw [hf', mul_one, hkk]
  · exfalso
    rw [mul_one, inv_eq_of_mul_eq_one_right hzkzk] at hf'
    rcases hfv with hf1 | hf1 <;> rw [hf1] at hf'
    · exact hzk1 hf'.symm
    · exact S.z_ne_one (by simpa using hf'.symm)
  · exfalso
    rw [hkz, inv_eq_of_mul_eq_one_right hzkzk] at hf'
    rcases hfv with hf1 | hf1 <;> rw [hf1] at hf'
    · exact hzk1 hf'.symm
    · exact S.z_ne_one (by simpa using hf'.symm)
  · rw [hf', show S.z * C.F.kF * S.z = C.F.kF by
      rw [mul_assoc, hkz, ← mul_assoc, zz S, one_mul], hkk]

theorem uw₁_mem_E0 : C.D₁.u * C.D₁.w₁ * C.D₁.u⁻¹ * C.D₁.w₁⁻¹ ∈ C.E₀ := by
  refine C.mem_E0_of_mem_Q0 (mul_mem (C.u_conj_Q₀ C.w₁_mem_Q0) (inv_mem C.w₁_mem_Q0)) ?_
  exact ((mem_centralizer_iff.mp C.D₁.u_comm_w₁) S.t (t_mem_E _)).symm

theorem exists_w₁' : ∃ w : X, (w = C.D₁.w₁ ∨ w = C.F.yF * C.D₁.w₁) ∧
    C.D₁.u * w * C.D₁.u⁻¹ * w⁻¹ = C.F.kF := by
  set u := C.D₁.u with hu
  set w₁ := C.D₁.w₁ with hw₁
  set f := u * w₁ * u⁻¹ * w₁⁻¹ with hf
  have hfE : f ∈ C.E₀ := C.uw₁_mem_E0
  have hfix : u * f * u⁻¹ = f := by
    have huu : u * u = 1 := C.u_mul_u
    have hinv : u⁻¹ = u := C.u_inv
    have h1 : u * f * u⁻¹ = f⁻¹ := by
      calc u * f * u⁻¹ = (u * u) * w₁ * u⁻¹ * w₁⁻¹ * u⁻¹ := by rw [hf]; group
        _ = w₁ * u⁻¹ * w₁⁻¹ * u⁻¹ := by rw [huu, one_mul]
        _ = w₁ * u * w₁⁻¹ * u⁻¹ := by rw [hinv]
        _ = f⁻¹ := by rw [hf]; group
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (by
      rw [← pow_two]; exact (C.isRefl_y.elemAbelianTwo_E0 C.isK_k).sq_eq_one f hfE)
  have hfzk := C.mem_zk_of_mem_E0 hfE hfix
  rw [sup_comm] at hfzk
  have hkel : ElemAbelianTwo (zpowers C.F.kF) :=
    ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr (kF_mem_B C.F) ha)
        (zpowers_le.mpr (kF_mem_B C.F) hb),
      fun a ha => S.sq_of_mem_B (zpowers_le.mpr (kF_mem_B C.F) ha)⟩
  have hw1t := C.w₁_t
  rcases mem_or_of_mem_sup hkel z_sq (fun a ha => commute_of_mem_B z_mem_B
      (zpowers_le.mpr (kF_mem_B C.F) ha)) hfzk with h | h
  · exact ⟨w₁, Or.inl rfl, C.uw_eq_k C.w₁_mem_Q0 (fun e he => C.w₁_E0 he) hw1t rfl h⟩
  · refine ⟨C.F.yF * w₁, Or.inr rfl, C.uw_eq_k (mul_mem (C.E0_le_Q0 C.y_mem_E0) C.w₁_mem_Q0)
      (fun e he => ?_) ?_ ?_ ?_⟩
    · rw [show C.F.yF * w₁ * e * (C.F.yF * w₁)⁻¹ = C.F.yF * (w₁ * e * w₁⁻¹) * C.F.yF⁻¹ by
        group, C.w₁_E0 he]
      exact conj_eq_of_comm (C.comm_E0 C.y_mem_E0 he)
    · rw [show C.F.yF * w₁ * S.t * (C.F.yF * w₁)⁻¹ = C.F.yF * (w₁ * S.t * w₁⁻¹) * C.F.yF⁻¹ by
        group, hw1t]
      exact conj_eq_of_comm (comm_mul_of (C.t_comm_E0 C.y_mem_E0).symm
        (C.comm_E0 C.y_mem_E0 C.z_mem_E0))
    · rw [pow_two, pow_two, show C.F.yF * w₁ * (C.F.yF * w₁) = C.F.yF * (w₁ * C.F.yF) * w₁ by
        group, ← C.comm_of_mem_E0 C.y_mem_E0 C.w₁_mem_Q0, ← mul_assoc, C.yy, one_mul]
    · have hcalc : u * (C.F.yF * w₁) * u⁻¹ * (C.F.yF * w₁)⁻¹ = f * S.z := by
        calc u * (C.F.yF * w₁) * u⁻¹ * (C.F.yF * w₁)⁻¹ =
              (u * C.F.yF * u⁻¹) * f * C.F.yF⁻¹ := by rw [hf]; group
          _ = S.z * C.F.yF * f * C.F.yF⁻¹ := by rw [C.u_y]
          _ = f * S.z := by
            rw [mul_assoc S.z, C.comm_E0 C.y_mem_E0 hfE, ← mul_assoc, mul_assoc _ C.F.yF,
              mul_inv_cancel, mul_one, C.comm_E0 C.z_mem_E0 hfE]
      rw [hcalc]
      exact h

noncomputable def w₁' : X := Classical.choose C.exists_w₁'

theorem w₁'_eq : C.w₁' = C.D₁.w₁ ∨ C.w₁' = C.F.yF * C.D₁.w₁ :=
  (Classical.choose_spec C.exists_w₁').1

theorem u_w₁' : C.D₁.u * C.w₁' * C.D₁.u⁻¹ * C.w₁'⁻¹ = C.F.kF :=
  (Classical.choose_spec C.exists_w₁').2

theorem w₁'_mem_Q0 : C.w₁' ∈ C.Q₀ := by
  rcases C.w₁'_eq with h | h <;> rw [h]
  · exact C.w₁_mem_Q0
  · exact mul_mem (C.E0_le_Q0 C.y_mem_E0) C.w₁_mem_Q0

theorem w₁'_E0 {e : X} (he : e ∈ C.E₀) : C.w₁' * e * C.w₁'⁻¹ = e := by
  rcases C.w₁'_eq with h | h <;> rw [h]
  · exact C.w₁_E0 he
  · rw [show C.F.yF * C.D₁.w₁ * e * (C.F.yF * C.D₁.w₁)⁻¹ =
      C.F.yF * (C.D₁.w₁ * e * C.D₁.w₁⁻¹) * C.F.yF⁻¹ by group, C.w₁_E0 he]
    exact conj_eq_of_comm (C.comm_E0 C.y_mem_E0 he)

theorem w₁'_t : C.w₁' * S.t * C.w₁'⁻¹ = S.t * S.z := by
  rcases C.w₁'_eq with h | h <;> rw [h]
  · exact C.w₁_t
  · rw [show C.F.yF * C.D₁.w₁ * S.t * (C.F.yF * C.D₁.w₁)⁻¹ =
      C.F.yF * (C.D₁.w₁ * S.t * C.D₁.w₁⁻¹) * C.F.yF⁻¹ by group, C.w₁_t]
    exact conj_eq_of_comm (comm_mul_of (C.t_comm_E0 C.y_mem_E0).symm
      (C.comm_E0 C.y_mem_E0 C.z_mem_E0))

theorem w₁'_mem_T₁ : C.w₁' ∈ C.T₁ := by
  have hw : C.D₁.w₁ ∈ C.T₁ := C.D₁.T₁_eq.ge (mem_sup_right (mem_zpowers _))
  have hy : C.F.yF ∈ C.T₁ := C.h4.le (yF_mem_T C.F)
  rcases C.w₁'_eq with h | h <;> rw [h]
  · exact hw
  · exact mul_mem hy hw

theorem v_mem_T₁ : C.D₁.v ∈ C.T₁ :=
  C.D₁.T₁_eq.ge (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem v_mem_C : C.D₁.v ∈ C.D₁.Q₁ ⊓ centralizer (C.D₁.D₁₁ : Set X) := by
  rw [C.D₁.C_eq]; exact subset_closure (by simp)

theorem u_comm_v : C.D₁.u * C.D₁.v = C.D₁.v * C.D₁.u := C.D₁.u_comm_C _ C.v_mem_C

theorem w₁'_u : C.w₁' * C.D₁.u * C.w₁'⁻¹ = C.F.kF * C.D₁.u := by
  have h := C.u_w₁'
  have hkk : C.F.kF⁻¹ = C.F.kF := inv_eq_of_mul_eq_one_right C.kk
  calc C.w₁' * C.D₁.u * C.w₁'⁻¹ = (C.D₁.u * C.w₁' * C.D₁.u⁻¹ * C.w₁'⁻¹)⁻¹ * C.D₁.u := by group
    _ = C.F.kF * C.D₁.u := by rw [h, hkk]

theorem u_cases : (∃ c ∈ zpowers S.z, C.D₁.u = c * (C.F.xF * C.F.yF)) ∨
    (∃ c ∈ zpowers S.z, C.D₁.u = c * S.t * (C.F.xF * C.F.yF)) := by
  rcases C.D₁.u_eq with h | h <;> rcases C.hu₁ with h' | h'
  · exact Or.inl ⟨1, one_mem _, by rw [h, h', one_mul]⟩
  · exact Or.inl ⟨S.z, mem_zpowers _, by rw [h, h']⟩
  · exact Or.inr ⟨1, one_mem _, by rw [h, h', one_mul]⟩
  · refine Or.inr ⟨S.z, mem_zpowers _, ?_⟩
    rw [h, h', ← mul_assoc, (commute_of_mem_B t_mem_B z_mem_B)]

theorem zpow_z_mem_B {c : X} (hc : c ∈ zpowers S.z) : c ∈ S.B := zpowers_le.mpr z_mem_B hc

theorem w₁'_xy : (C.w₁' * (C.F.xF * C.F.yF) * C.w₁'⁻¹ = C.F.kF * (C.F.xF * C.F.yF) ∧
      ∃ c ∈ zpowers S.z, C.D₁.u = c * (C.F.xF * C.F.yF)) ∨
    (C.w₁' * (C.F.xF * C.F.yF) * C.w₁'⁻¹ = S.z * C.F.kF * (C.F.xF * C.F.yF) ∧
      ∃ c ∈ zpowers S.z, C.D₁.u = c * S.t * (C.F.xF * C.F.yF)) := by
  have hwu := C.w₁'_u
  have hcz : ∀ c ∈ zpowers S.z, C.w₁' * c * C.w₁'⁻¹ = c := fun c hc =>
    C.w₁'_E0 ((zpowers_le.mpr C.z_mem_E0) hc)
  rcases C.u_cases with ⟨c, hc, hu⟩ | ⟨c, hc, hu⟩
  · left
    refine ⟨?_, c, hc, hu⟩
    have hxy : C.F.xF * C.F.yF = c⁻¹ * C.D₁.u := by rw [hu]; group
    conv_lhs => rw [hxy]
    rw [conj_mul_eq, hwu, show C.w₁' * c⁻¹ * C.w₁'⁻¹ = (C.w₁' * c * C.w₁'⁻¹)⁻¹ by group,
      hcz c hc, ← mul_assoc, (S.central_of_mem_B (inv_mem (zpow_z_mem_B hc)) C.F.kF_mem),
      mul_assoc, ← hxy]
  · right
    refine ⟨?_, c, hc, hu⟩
    have hxy : C.F.xF * C.F.yF = (c * S.t)⁻¹ * C.D₁.u := by rw [hu]; group
    have hct : C.w₁' * (c * S.t) * C.w₁'⁻¹ = c * S.t * S.z := by
      rw [conj_mul_eq, hcz c hc, C.w₁'_t, mul_assoc]
    conv_lhs => rw [hxy]
    rw [conj_mul_eq, hwu, show C.w₁' * (c * S.t)⁻¹ * C.w₁'⁻¹ =
      (C.w₁' * (c * S.t) * C.w₁'⁻¹)⁻¹ by group, hct, hu]
    have hcB := zpow_z_mem_B hc
    have hkc : C.F.kF * c = c * C.F.kF := commute_of_mem_B (kF_mem_B C.F) hcB
    have hkt : C.F.kF * S.t = S.t * C.F.kF := commute_of_mem_B (kF_mem_B C.F) t_mem_B
    have hzk : S.z * C.F.kF = C.F.kF * S.z := commute_of_mem_B z_mem_B (kF_mem_B C.F)
    calc (c * S.t * S.z)⁻¹ * (C.F.kF * (c * S.t * (C.F.xF * C.F.yF))) =
          S.z⁻¹ * S.t⁻¹ * c⁻¹ * (C.F.kF * c * S.t) * (C.F.xF * C.F.yF) := by group
      _ = S.z⁻¹ * S.t⁻¹ * c⁻¹ * (c * S.t * C.F.kF) * (C.F.xF * C.F.yF) := by
          rw [hkc, mul_assoc c, hkt]; group
      _ = S.z⁻¹ * C.F.kF * (C.F.xF * C.F.yF) := by group
      _ = S.z * C.F.kF * (C.F.xF * C.F.yF) := by
          rw [inv_eq_of_mul_eq_one_right (zz S)]

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
