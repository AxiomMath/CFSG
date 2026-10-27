module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD7Frame
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Two

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD}

structure Setup (S : KDBase A C) where
  F : Frame S
  T₁ : Subgroup X
  ui : X
  hui : ui = F.xF * F.yF ∨ ui = S.z * (F.xF * F.yF)
  D : S.Sec6 T₁ F.yF F.kF ui
  hq : D.q0 = .e4q8 ∨ D.q0 = .exceptional

namespace Setup

variable {S : KDBase A C} (P : Setup S)

abbrev E₀ : Subgroup X := S.E0 P.F.yF P.F.kF

abbrev Q₀ : Subgroup X := S.Q0 P.F.yF P.F.kF P.D.w₁ P.D.w₂

theorem E0_le_Q0 : P.E₀ ≤ P.Q₀ := le_sup_left.trans le_sup_left

theorem w₁_mem_Q0 : P.D.w₁ ∈ P.Q₀ := mem_sup_left (mem_sup_right (mem_zpowers _))

theorem w₂_mem_Q0 : P.D.w₂ ∈ P.Q₀ := mem_sup_right (mem_zpowers _)

theorem centerEq : CenterEq P.Q₀ P.E₀ := by
  have h := P.D.q0_holds
  rcases P.hq with hq | hq <;> rw [hq] at h
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem card_Q0 : Nat.card P.Q₀ = 32 := by
  have h := P.D.q0_holds
  rcases P.hq with hq | hq <;> rw [hq] at h
  · exact h.2.2.2
  · exact h.2.2.2.2

theorem comm_of_mem_E0 {a b : X} (ha : a ∈ P.E₀) (hb : b ∈ P.Q₀) : a * b = b * a :=
  ((P.centerEq a (P.E0_le_Q0 ha)).mpr ha) b hb

theorem act_one : P.D.act = .one := by
  cases hact : P.D.act with
  | one => rfl
  | two =>
    exfalso
    have h := P.D.act_holds
    rw [hact] at h
    have hcomm := P.comm_of_mem_E0 P.F.yF_mem_E0 P.w₁_mem_Q0
    have hwy : P.D.w₁ * P.F.yF * P.D.w₁⁻¹ = P.F.yF := by
      rw [← hcomm, mul_inv_cancel_right]
    rw [h.2.2.2.2.2.2.2.1] at hwy
    exact P.F.kF_ne_one (by simpa using hwy)

theorem hact : S.ActHolds P.F.yF P.F.kF P.D.v P.D.w₁ P.D.w₂ .one := by
  have h := P.D.act_holds
  rw [P.act_one] at h
  exact h

theorem w₁_sq_mem : P.D.w₁ ^ 2 ∈ P.E₀ := by
  have h := P.D.q0_holds
  rcases P.hq with hq | hq <;> rw [hq] at h
  · rw [h.1]; exact P.F.kF_mem_E0
  · rw [h.1]; exact mul_mem P.F.z_mem_E0 P.F.kF_mem_E0

theorem w₂_sq_mem : P.D.w₂ ^ 2 ∈ P.E₀ := by
  have h := P.D.q0_holds
  rcases P.hq with hq | hq <;> rw [hq] at h
  · rw [h.2.1]; exact P.F.kF_mem_E0
  · rw [h.2.1]; exact mul_mem P.F.yF_mem_E0 P.F.kF_mem_E0

theorem w₁_normalizes : P.D.w₁ ∈ normalizer (P.E₀ : Set X) := by
  refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun e he => ?_)
  exact P.comm_of_mem_E0 he P.w₁_mem_Q0

theorem w₁_t : P.D.w₁ * t * P.D.w₁⁻¹ = t * S.z := P.hact.2.2.1

theorem w₂_t : P.D.w₂ * t * P.D.w₂⁻¹ = t * P.F.yF := P.hact.2.2.2

theorem w₁_E0 {e : X} (he : e ∈ P.E₀) : P.D.w₁ * e * P.D.w₁⁻¹ = e := (P.hact.1 e he).2.1

theorem w₂_E0 {e : X} (he : e ∈ P.E₀) : P.D.w₂ * e * P.D.w₂⁻¹ = e := (P.hact.1 e he).2.2

theorem zy_ne_one : S.z * P.F.yF ≠ 1 := by
  intro h
  apply P.F.yF_ne_z
  rw [eq_inv_of_mul_eq_one_right h, z_inv S]

theorem w₁_inv_t : P.D.w₁⁻¹ * t * P.D.w₁ = t * S.z :=
  Sec7.conj_inv_eq_of P.w₁_t (P.w₁_E0 P.F.z_mem_E0) (zz S)

theorem w₂_inv_t : P.D.w₂⁻¹ * t * P.D.w₂ = t * P.F.yF :=
  Sec7.conj_inv_eq_of P.w₂_t (P.w₂_E0 P.F.yF_mem_E0) P.F.yF_yF

theorem w₁_not_mem_E0 : P.D.w₁ ∉ P.E₀ := fun h => z_ne_one S (by
  have h1 := P.w₁_t
  rw [Sec7.conj_eq_of_comm (P.F.t_comm_E0 h).symm] at h1
  simpa using h1.symm)

theorem comm_w₁w₂_mem : P.D.w₁ * P.D.w₂ * P.D.w₁⁻¹ * P.D.w₂⁻¹ ∈ P.E₀ := by
  set c := P.D.w₁ * P.D.w₂ * P.D.w₁⁻¹ * P.D.w₂⁻¹ with hc
  have hP : Nat.card (P.E₀ ⊔ zpowers P.D.w₁ : Subgroup X) = 16 := by
    rw [Sec7.card_sup_zpowers_eq P.w₁_normalizes P.w₁_sq_mem P.w₁_not_mem_E0, P.F.card_E0]
  have hPQ : P.E₀ ⊔ zpowers P.D.w₁ ≤ P.Q₀ := sup_le P.E0_le_Q0 (zpowers_le.mpr P.w₁_mem_Q0)
  have hidx : (P.E₀ ⊔ zpowers P.D.w₁).relIndex P.Q₀ = 2 := by
    have hmul := Subgroup.relIndex_mul_card (P.E₀ ⊔ zpowers P.D.w₁) P.Q₀
    rw [inf_eq_left.mpr hPQ, hP, P.card_Q0] at hmul
    omega
  have hN := normal_of_index_eq_two hidx
  have hw : P.D.w₂ * P.D.w₁⁻¹ * P.D.w₂⁻¹ ∈ P.E₀ ⊔ zpowers P.D.w₁ := by
    have := hN.conj_mem ⟨P.D.w₁⁻¹, inv_mem P.w₁_mem_Q0⟩
      (mem_subgroupOf.mpr (inv_mem (mem_sup_right (mem_zpowers _)))) ⟨P.D.w₂, P.w₂_mem_Q0⟩
    exact mem_subgroupOf.mp this
  have hcS : c ∈ P.E₀ ⊔ zpowers P.D.w₁ := by
    rw [hc, show P.D.w₁ * P.D.w₂ * P.D.w₁⁻¹ * P.D.w₂⁻¹ =
      P.D.w₁ * (P.D.w₂ * P.D.w₁⁻¹ * P.D.w₂⁻¹) by group]
    exact mul_mem (mem_sup_right (mem_zpowers _)) hw
  rcases Sec7.mem_or_of_mem_sup_zpowers P.w₁_normalizes P.w₁_sq_mem hcS with h | h
  · exact h
  · exfalso
    have hct : c * t * c⁻¹ = t := by
      have e2 : P.D.w₁⁻¹ * (t * P.F.yF) * P.D.w₁ = t * S.z * P.F.yF := by
        have := Sec7.conj_mul_eq P.D.w₁⁻¹ t P.F.yF
        rw [inv_inv] at this
        rw [this, P.w₁_inv_t]
        have hy : P.D.w₁⁻¹ * P.F.yF * P.D.w₁ = P.F.yF := by
          have := P.w₁_E0 P.F.yF_mem_E0
          calc P.D.w₁⁻¹ * P.F.yF * P.D.w₁ = P.D.w₁⁻¹ * (P.D.w₁ * P.F.yF * P.D.w₁⁻¹) *
                P.D.w₁ := by rw [this]
            _ = P.F.yF := by group
        rw [hy]
      have e3 : P.D.w₂ * (t * S.z * P.F.yF) * P.D.w₂⁻¹ = t * S.z := by
        rw [Sec7.conj_mul_eq, Sec7.conj_mul_eq, P.w₂_t, P.w₂_E0 P.F.z_mem_E0,
          P.w₂_E0 P.F.yF_mem_E0,
          show t * P.F.yF * S.z * P.F.yF = t * S.z * (P.F.yF * P.F.yF) by
            rw [mul_assoc t, mul_assoc t, P.F.comm_E0 P.F.yF_mem_E0 P.F.z_mem_E0]; group,
          P.F.yF_yF, mul_one]
      have e4 : P.D.w₁ * (t * S.z) * P.D.w₁⁻¹ = t := by
        rw [Sec7.conj_mul_eq, P.w₁_t, P.w₁_E0 P.F.z_mem_E0, mul_assoc, zz S, mul_one]
      calc c * t * c⁻¹ = P.D.w₁ * (P.D.w₂ * (P.D.w₁⁻¹ * (P.D.w₂⁻¹ * t * P.D.w₂) *
            P.D.w₁) * P.D.w₂⁻¹) * P.D.w₁⁻¹ := by rw [hc]; group
        _ = t := by rw [P.w₂_inv_t, e2, e3, e4]
    set e := c * P.D.w₁⁻¹ with he
    have hce : c = e * P.D.w₁ := by rw [he]; group
    have hcomm : e * (t * S.z) = t * S.z * e :=
      Sec7.comm_mul_of (P.F.t_comm_E0 h).symm (P.F.comm_E0 h P.F.z_mem_E0)
    have : c * t * c⁻¹ = t * S.z := by
      calc c * t * c⁻¹ = e * (P.D.w₁ * t * P.D.w₁⁻¹) * e⁻¹ := by rw [hce]; group
        _ = t * S.z := by rw [P.w₁_t, Sec7.conj_eq_of_comm hcomm]
    rw [hct] at this
    exact z_ne_one S (by simpa using this)

abbrev P₀ : Subgroup X := P.E₀ ⊔ zpowers P.D.w₁

theorem w₂_conj_w₁ : P.D.w₂ * P.D.w₁ * P.D.w₂⁻¹ =
    (P.D.w₁ * P.D.w₂ * P.D.w₁⁻¹ * P.D.w₂⁻¹)⁻¹ * P.D.w₁ := by group

theorem w₂_normalizes_P₀ : P.D.w₂ ∈ normalizer (P.P₀ : Set X) := by
  have hle : P.P₀.map (MulAut.conj P.D.w₂).toMonoidHom ≤ P.P₀ := by
    rw [map_le_iff_le_comap]
    refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
    · show P.D.w₂ * e * P.D.w₂⁻¹ ∈ P.P₀
      rw [P.w₂_E0 he]
      exact mem_sup_left he
    · show P.D.w₂ * P.D.w₁ * P.D.w₂⁻¹ ∈ P.P₀
      rw [P.w₂_conj_w₁]
      exact mul_mem (mem_sup_left (inv_mem P.comm_w₁w₂_mem)) (mem_sup_right (mem_zpowers _))
  refine Sec7.mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj P.D.w₂).injective]

theorem mem_Q₀ {a : X} (ha : a ∈ P.Q₀) :
    a ∈ P.E₀ ∨ a * P.D.w₁⁻¹ ∈ P.E₀ ∨ a * P.D.w₂⁻¹ ∈ P.E₀ ∨
      a * P.D.w₂⁻¹ * P.D.w₁⁻¹ ∈ P.E₀ := by
  rcases Sec7.mem_or_of_mem_sup_zpowers P.w₂_normalizes_P₀ (mem_sup_left P.w₂_sq_mem) ha with
    h | h
  · rcases Sec7.mem_or_of_mem_sup_zpowers P.w₁_normalizes P.w₁_sq_mem h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases Sec7.mem_or_of_mem_sup_zpowers P.w₁_normalizes P.w₁_sq_mem h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

theorem conj_t_of_mem_E0 {e g : X} (he : e ∈ P.E₀) (hg : g * t * g⁻¹ = t * S.z ∨
    g * t * g⁻¹ = t * P.F.yF ∨ g * t * g⁻¹ = t * (S.z * P.F.yF)) :
    (e * g) * t * (e * g)⁻¹ = t * S.z ∨ (e * g) * t * (e * g)⁻¹ = t * P.F.yF ∨
      (e * g) * t * (e * g)⁻¹ = t * (S.z * P.F.yF) := by
  have hc : ∀ b ∈ P.E₀, e * (t * b) * e⁻¹ = t * b := fun b hb =>
    Sec7.conj_eq_of_comm (Sec7.comm_mul_of (P.F.t_comm_E0 he).symm (P.F.comm_E0 he hb))
  have : (e * g) * t * (e * g)⁻¹ = e * (g * t * g⁻¹) * e⁻¹ := by group
  rw [this]
  rcases hg with h | h | h <;> rw [h]
  · exact Or.inl (hc _ P.F.z_mem_E0)
  · exact Or.inr (Or.inl (hc _ P.F.yF_mem_E0))
  · exact Or.inr (Or.inr (hc _ (mul_mem P.F.z_mem_E0 P.F.yF_mem_E0)))

theorem mem_E0_of_mem_Q0 {a : X} (ha : a ∈ P.Q₀) (hat : a * t = t * a) : a ∈ P.E₀ := by
  have hfix : a * t * a⁻¹ = t := by rw [hat, mul_inv_cancel_right]
  have hne1 : t * S.z ≠ t := fun h => z_ne_one S (by simpa using h)
  have hne2 : t * P.F.yF ≠ t := fun h => P.F.yF_ne_one (by simpa using h)
  have hne3 : t * (S.z * P.F.yF) ≠ t := fun h => P.zy_ne_one (by simpa using h)
  rcases P.mem_Q₀ ha with h | h | h | h
  · exact h
  · exfalso
    have hd := P.conj_t_of_mem_E0 h (g := P.D.w₁) (Or.inl P.w₁_t)
    rw [show a * P.D.w₁⁻¹ * P.D.w₁ = a by group, hfix] at hd
    rcases hd with hd | hd | hd
    · exact hne1 hd.symm
    · exact hne2 hd.symm
    · exact hne3 hd.symm
  · exfalso
    have hd := P.conj_t_of_mem_E0 h (g := P.D.w₂) (Or.inr (Or.inl P.w₂_t))
    rw [show a * P.D.w₂⁻¹ * P.D.w₂ = a by group, hfix] at hd
    rcases hd with hd | hd | hd
    · exact hne1 hd.symm
    · exact hne2 hd.symm
    · exact hne3 hd.symm
  · exfalso
    have hw : (P.D.w₁ * P.D.w₂) * t * (P.D.w₁ * P.D.w₂)⁻¹ = t * (S.z * P.F.yF) := by
      calc (P.D.w₁ * P.D.w₂) * t * (P.D.w₁ * P.D.w₂)⁻¹ =
            P.D.w₁ * (P.D.w₂ * t * P.D.w₂⁻¹) * P.D.w₁⁻¹ := by group
        _ = t * (S.z * P.F.yF) := by
          rw [P.w₂_t, Sec7.conj_mul_eq, P.w₁_t, P.w₁_E0 P.F.yF_mem_E0, mul_assoc]
    have hd := P.conj_t_of_mem_E0 h (g := P.D.w₁ * P.D.w₂) (Or.inr (Or.inr hw))
    rw [show a * P.D.w₂⁻¹ * P.D.w₁⁻¹ * (P.D.w₁ * P.D.w₂) = a by group, hfix] at hd
    rcases hd with hd | hd | hd
    · exact hne1 hd.symm
    · exact hne2 hd.symm
    · exact hne3 hd.symm

end Setup

end KD7

end CFSG.ComponentClassification.HSFLit
