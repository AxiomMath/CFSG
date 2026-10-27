module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAD

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7 Sec8

@[expose] def inA2 (x : MA) : Bool := !MA.bit x 0 && !MA.bit x 5 && !MA.bit x 6

theorem A2_span : ∀ x : MA, inA2 x = true → InSpan [MA.u, MA.w₁, MA.v, MA.z, MA.k] x := by
  decide +kernel

theorem Kc_fact : ∀ x : MA, x * x = 1 → x ≠ 1 → MA.inQC x = false →
    (∀ s : MA, inA2 (s * x * s⁻¹) = false) → x ∈ MA.KcList := by decide +kernel

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace AD

variable (H : AD S T₁)

theorem not_conjTo_of_QC {x : MA} (hx : MA.inQC x = true) : ¬ ConjTo t (H.ι x) := by
  refine H.G.D₁.no_conj_of (Or.inl H.h₁) _
    (map_mem_of_inSpan H.ι (MA.QC_span x hx) fun g hg => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  have hE0 : ∀ e ∈ S.E0 S.y S.k,
      e ∈ S.Q0 S.y S.k H.G.D₁.w₁ H.G.D₁.w₂ ⊔ H.G.D₁.C₁ :=
    fun e he => mem_sup_left (H.G.V₁.E0_le_Q0 he)
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [H.ι_w₂]; exact mem_sup_left H.G.V₁.w₂_mem_Q0
  · rw [H.ι_w₁]; exact mem_sup_left H.G.V₁.w₁N_mem_Q0
  · rw [H.ι_v]; exact H.G.V₁.vN_mem_Q0C1 (H.G.P₁.option_of_elem H.h₁).1
  · rw [H.ι_z]; exact hE0 _ H.G.V₁.z_mem_E0
  · rw [H.ι_y]; exact hE0 _ H.G.V₁.yi_mem_E0
  · rw [H.ι_k]; exact hE0 _ H.G.V₁.ki_mem_E0

theorem not_conjTo_of_A2 {x : MA} (hx : inA2 x = true) : ¬ ConjTo t (H.ι x) := by
  set Q := S.Q0 (S.x * S.y) (S.z * S.k) H.G.D₂.w₁ H.G.D₂.w₂ ⊔ H.G.D₂.C₁ with hQ
  have hE0 : ∀ e ∈ S.E0 (S.x * S.y) (S.z * S.k), e ∈ Q :=
    fun e he => mem_sup_left (H.G.V₂.E0_le_Q0 he)
  have hzk : ∀ c ∈ (zpowers S.z ⊔ zpowers (S.z * S.k) : Subgroup X), c ∈ Q :=
    fun c hc => hE0 c (H.G.V₂.zk_le_E0 hc)
  have hw₂ : H.G.V₂.w₁c ∈ Q := by
    rw [ISide.w₁c_of_elem _ H.h₂]; exact mem_sup_left H.G.V₂.w₁N_mem_Q0
  have hw : H.G.V₁.w₁c ∈ Q := by
    obtain ⟨c, hc, hw⟩ := H.G.P₁.exists_w₁W_same (H.h₁.trans H.h₂.symm)
    change H.G.V₁.w₁c = H.G.V₂.w₁c * c at hw
    rw [hw]; exact mul_mem hw₂ (hzk c hc)
  have hv : H.G.V₁.vN ∈ Q := by
    obtain ⟨c, hc, hv⟩ := H.G.P₁.exists_vW_zk
    change H.G.V₁.vN * H.G.V₁.w₁c = H.G.V₂.vN * c at hv
    have hvW : H.G.V₂.vN ∈ Q := H.G.V₂.vN_mem_Q0C1 (H.G.P₂.option_of_elem H.h₂).1
    rw [show H.G.V₁.vN = H.G.V₂.vN * c * H.G.V₁.w₁c⁻¹ by rw [← hv]; group]
    exact mul_mem (mul_mem hvW (hzk c hc)) (inv_mem hw)
  refine H.G.D₂.no_conj_of (Or.inl H.h₂) _
    (map_mem_of_inSpan H.ι (A2_span x hx) fun g hg => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · rw [H.ι_u]; exact hE0 _ H.G.V₂.yi_mem_E0
  · rw [← H.ι_w₁_eq]; exact hw
  · rw [H.ι_v]; exact hv
  · rw [H.ι_z]; exact hE0 _ H.G.V₂.z_mem_E0
  · rw [H.ι_k]
    have h1 : S.z * (S.z * S.k) ∈ Q := mul_mem (hE0 _ H.G.V₂.z_mem_E0) (hE0 _ H.G.V₂.ki_mem_E0)
    rwa [← mul_assoc, zz S, one_mul] at h1

theorem mem_Kc_of_conjTo {x : MA} (hx : ConjTo t (H.ι x)) : x ∈ MA.KcList := by
  obtain ⟨c, hc⟩ := hx
  have hx2 : x * x = 1 := by
    apply H.ι_injective
    rw [map_mul, ← hc, map_one, show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group,
      tt (A := A), mul_one, mul_inv_cancel]
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hc
    exact L2K.t_ne_one (A := A) (by
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group)
  have hq : MA.inQC x = false := by
    by_contra h
    exact H.not_conjTo_of_QC (by simpa using h) ⟨c, hc⟩
  refine Kc_fact x hx2 hx1 hq fun s => ?_
  by_contra h
  apply H.not_conjTo_of_A2 (by simpa using h)
  refine ⟨H.ι s * c, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hc]
  group

end AD

end KD8ab

end CFSG.ComponentClassification.HSFLit
