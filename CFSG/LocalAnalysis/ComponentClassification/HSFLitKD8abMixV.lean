module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD7Main

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem act_one_of_abelian {F : Frame S} {ui : X} (D : S.Sec6 T₁ F.yF F.kF ui)
    (hq : D.q0 = .elem ∨ D.q0 = .homocyclic) : D.act = .one := by
  have hcomm : ∀ a ∈ S.Q0 F.yF F.kF D.w₁ D.w₂, ∀ b ∈ S.Q0 F.yF F.kF D.w₁ D.w₂,
      a * b = b * a := by
    have h := D.q0_holds
    rcases hq with hq | hq <;> rw [hq] at h
    · exact h.1
    · exact h.2.2.1
  cases hact : D.act with
  | one => rfl
  | two =>
    exfalso
    have h := D.act_holds
    rw [hact] at h
    have hE : S.E0 F.yF F.kF ≤ S.Q0 F.yF F.kF D.w₁ D.w₂ := le_sup_left.trans le_sup_left
    have hy : F.yF ∈ S.Q0 F.yF F.kF D.w₁ D.w₂ := hE F.yF_mem_E0
    have hw : D.w₁ ∈ S.Q0 F.yF F.kF D.w₁ D.w₂ := mem_sup_left (mem_sup_right (mem_zpowers _))
    have hwy : D.w₁ * F.yF * D.w₁⁻¹ = F.yF := by rw [hcomm _ hw _ hy, mul_inv_cancel_right]
    rw [h.2.2.2.2.2.2.2.1] at hwy
    exact F.kF_ne_one (by simpa using hwy)

theorem w₂_conj_z_of_extra {yi ki ui : X} (D : S.Sec6 T₁ yi ki ui)
    (hq : D.q0 = .extraspecial) : D.w₂ * S.z * D.w₂⁻¹ = S.z * ki := by
  have h := D.q0_holds
  rw [hq] at h
  exact h.2.2.1.2.2.2.2.2.2.1

variable (S)

theorem false_of_v₁ (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (h₁ : D₁.q0 = .extraspecial)
    (h₂ : D₂.q0 = .elem ∨ D₂.q0 = .homocyclic) : False := by
  have hact := act_one_of_abelian (F := frame₂ S) D₂ h₂
  have hw : D₁.w₂ ∈ normalizer (S.E S.y : Set X) :=
    D₁.S₁_le (w₂_mem_S₁ (F := frame₁ S) D₁)
  have hdC : C.d ∈ centralizer ({t} : Set X) := L2KD.d_mem_C C
  have hn : ∀ e ∈ S.E (S.x * S.y), (C.d * D₁.w₂ * C.d⁻¹) * e * (C.d * D₁.w₂ * C.d⁻¹)⁻¹ ∈
      S.E (S.x * S.y) := by
    intro e he
    have h1 := (mem_normalizer_iff.mp hw _).mp (d_inv_conj_E₂ S he)
    have h2 := d_conj_E₁ S h1
    rwa [show C.d * (D₁.w₂ * (C.d⁻¹ * e * C.d) * D₁.w₂⁻¹) * C.d⁻¹ =
      (C.d * D₁.w₂ * C.d⁻¹) * e * (C.d * D₁.w₂ * C.d⁻¹)⁻¹ by group] at h2
  have hz := conj_mem_L_of_mem_E (F := frame₂ S) D₂ hact hn (Frame.z_mem_E _) (z_mem_L S)
  have hdz : C.d⁻¹ * S.z * C.d⁻¹⁻¹ = S.z := conj_z S (inv_mem C.d_mem)
  rw [show (C.d * D₁.w₂ * C.d⁻¹) * S.z * (C.d * D₁.w₂ * C.d⁻¹)⁻¹ =
      C.d * (D₁.w₂ * (C.d⁻¹ * S.z * C.d⁻¹⁻¹) * D₁.w₂⁻¹) * C.d⁻¹ by group, hdz,
    w₂_conj_z_of_extra D₁ h₁] at hz
  have := L2K.conj_mem_L (A := A) (inv_mem hdC) hz
  rw [show C.d⁻¹ * (C.d * (S.z * S.k) * C.d⁻¹) * C.d⁻¹⁻¹ = S.z * S.k by group] at this
  exact zk_not_mem_L S this

theorem false_of_v₂ (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (h₂ : D₂.q0 = .extraspecial)
    (h₁ : D₁.q0 = .elem ∨ D₁.q0 = .homocyclic) : False := by
  have hact := act_one_of_abelian (F := frame₁ S) D₁ h₁
  have hw : D₂.w₂ ∈ normalizer (S.E (S.x * S.y) : Set X) :=
    D₂.S₁_le (w₂_mem_S₁ (F := frame₂ S) D₂)
  have hdC : C.d ∈ centralizer ({t} : Set X) := L2KD.d_mem_C C
  have hn : ∀ e ∈ S.E S.y, (C.d⁻¹ * D₂.w₂ * C.d) * e * (C.d⁻¹ * D₂.w₂ * C.d)⁻¹ ∈ S.E S.y := by
    intro e he
    have h1 := (mem_normalizer_iff.mp hw _).mp (d_conj_E₁ S he)
    have h2 := d_inv_conj_E₂ S h1
    rwa [show C.d⁻¹ * (D₂.w₂ * (C.d * e * C.d⁻¹) * D₂.w₂⁻¹) * C.d =
      (C.d⁻¹ * D₂.w₂ * C.d) * e * (C.d⁻¹ * D₂.w₂ * C.d)⁻¹ by group] at h2
  have hz := conj_mem_L_of_mem_E (F := frame₁ S) D₁ hact hn (Frame.z_mem_E _) (z_mem_L S)
  have hdz : C.d * S.z * C.d⁻¹ = S.z := conj_z S C.d_mem
  rw [show (C.d⁻¹ * D₂.w₂ * C.d) * S.z * (C.d⁻¹ * D₂.w₂ * C.d)⁻¹ =
      C.d⁻¹ * (D₂.w₂ * (C.d * S.z * C.d⁻¹) * D₂.w₂⁻¹) * C.d by group, hdz,
    w₂_conj_z_of_extra D₂ h₂, show S.z * (S.z * S.k) = S.k by rw [← mul_assoc, zz S, one_mul]]
    at hz
  have := L2K.conj_mem_L (A := A) hdC hz
  rw [show C.d * (C.d⁻¹ * S.k * C.d) * C.d⁻¹ = S.k by group] at this
  exact k_not_mem_L (C := C) this

end KD8ab

end CFSG.ComponentClassification.HSFLit
