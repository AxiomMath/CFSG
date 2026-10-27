module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD8ab

open KD7

theorem even_cases : ∀ e e₀ b : ZMod 8, dbit8 e = 0 → dbit8 e₀ = 0 → (b = 2 ∨ b = 6) →
    e = e₀ ∨ e = 4 + e₀ ∨ e = b + e₀ ∨ e = 4 + b + e₀ := by decide

theorem refl_inv_transl : ∀ e b : ZMod 8,
    aff8 (-1) e * aff8 1 b * (aff8 (-1) e)⁻¹ = (aff8 1 b)⁻¹ := by decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem refl_cases {r : X} (h : IsRefl S r) :
    r = S.y ∨ r = S.z * S.y ∨ r = S.x * S.y ∨ r = S.z * (S.x * S.y) := by
  obtain ⟨b, hb, hx⟩ := ψX_x S
  obtain ⟨e₀, he₀, hy⟩ := (isRefl_y S).ψX
  obtain ⟨e, he, hr⟩ := h.ψX
  have hxy : SD.ψX A (S.x * S.y) = aff8 (-1) (b + e₀) := by
    rw [SD.ψX_mul S.x_mem.1 S.y_mem.1, hx, hy, aff8_mul]; simp
  have hzy : SD.ψX A (S.z * S.y) = aff8 (-1) (4 + e₀) := by
    rw [SD.ψX_mul (z_mem_T S) S.y_mem.1, ψX_z S, hy, z8, aff8_mul]; simp
  have hzxy : SD.ψX A (S.z * (S.x * S.y)) = aff8 (-1) (4 + b + e₀) := by
    rw [SD.ψX_mul (z_mem_T S) (mul_mem S.x_mem.1 S.y_mem.1), ψX_z S, hxy, z8, aff8_mul]
    simp [add_assoc]
  have hyR := S.y_mem
  have hxyR : S.x * S.y ∈ A.R := mul_mem S.x_mem S.y_mem
  rcases even_cases e e₀ b he he₀ hb with h1 | h1 | h1 | h1 <;> rw [h1] at hr
  · exact Or.inl (SD.eq_of_ψX_eq h.mem hyR (hr.trans hy.symm))
  · exact Or.inr (Or.inl (SD.eq_of_ψX_eq h.mem (mul_mem (z_mem_R S) hyR) (hr.trans hzy.symm)))
  · exact Or.inr (Or.inr (Or.inl (SD.eq_of_ψX_eq h.mem hxyR (hr.trans hxy.symm))))
  · exact Or.inr (Or.inr (Or.inr
      (SD.eq_of_ψX_eq h.mem (mul_mem (z_mem_R S) hxyR) (hr.trans hzxy.symm))))

theorem E_z_mul (r : X) : S.E (S.z * r) = S.E r := by
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Frame.z_mem_E r
    · exact mul_mem (Frame.z_mem_E r) (Frame.yi_mem_E r)
    · exact Frame.t_mem_E r
    · exact Frame.k_mem_E r
  · refine (closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Frame.z_mem_E _
    · have h1 : S.z * (S.z * g) ∈ S.E (S.z * g) := mul_mem (Frame.z_mem_E _) (Frame.yi_mem_E _)
      rwa [← mul_assoc, zz S, one_mul] at h1
    · exact Frame.t_mem_E _
    · exact Frame.k_mem_E _

theorem E_refl {r : X} (h : IsRefl S r) : S.E r = S.E S.y ∨ S.E r = S.E (S.x * S.y) := by
  rcases refl_cases S h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl (E_z_mul S _)
  · exact Or.inr rfl
  · exact Or.inr (E_z_mul S _)

theorem isRefl_of_sq {r : X} (hr : r ∈ A.R) (h2 : r ^ 2 = 1) (h1 : r ≠ 1) (hz : r ≠ S.z) :
    IsRefl S r := by
  refine ⟨hr, h2, ?_⟩
  obtain ⟨b, hb, hx⟩ := ψX_x S
  obtain ⟨e, he, hψ⟩ := SDKD.refl_of_mem_R8 (SD.ψX_mem_R8 hr)
    (by rw [← SD.ψX_pow hr.1, h2, SD.ψX_one])
    (fun h => h1 (SD.eq_one_of_ψX hr h))
    (fun h => hz (SD.eq_of_ψX_eq hr (z_mem_R S) (h.trans (ψX_z S).symm)))
  refine SD.eq_of_ψX_eq ?_ (inv_mem S.x_mem) ?_
  · exact SD.conj_mem_R_of_mem_T hr.1 S.x_mem
  · rw [SD.ψX_conj hr.1 S.x_mem.1, SD.ψX_inv S.x_mem.1, hψ, hx, refl_inv_transl]

theorem card_B : Nat.card S.B = 8 := by
  have hz : Nat.card (zpowers S.z) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (z_sq S) (z_ne_one S)]
  have htz : t ∉ zpowers S.z := fun h => t_not_mem_L (A := A) (zpowers_le.mpr (z_mem_L S) h)
  have hzt : ElemAbelianTwo (zpowers S.z ⊔ zpowers t : Subgroup X) :=
    Sec7.elemAbelianTwo_sup (elemAbelianTwo_z S) (SD.t_sq (A := A))
      fun _ ha => comm_zpowers_z S A.t_mem_T ha
  have hk : S.k ∉ (zpowers S.z ⊔ zpowers t : Subgroup X) := by
    intro h
    rcases Sec7.mem_or_of_mem_sup (elemAbelianTwo_z S) (SD.t_sq (A := A))
      (fun _ ha => comm_zpowers_z S A.t_mem_T ha) h with h1 | h1
    · exact k_not_mem_L (C := C) (zpowers_le.mpr (z_mem_L S) h1)
    · apply t_mul_not_mem_L S (Or.inl rfl)
      rw [show t * C.k = S.k * t from (A.commute_t C.k_mem).symm]
      exact zpowers_le.mpr (z_mem_L S) h1
  have hk' : ∀ a ∈ (zpowers S.z ⊔ zpowers t : Subgroup X), S.k * a = a * S.k := fun a ha =>
    (B_comm_k S ((show (zpowers S.z ⊔ zpowers t : Subgroup X) ≤ S.B by
      rw [B_eq]; exact le_sup_left) ha)).symm
  rw [B_eq]
  show Nat.card (zpowers S.z ⊔ zpowers t ⊔ zpowers C.k : Subgroup X) = 8
  rw [Sec7.card_sup_of_not_mem hzt C.k_sq hk hk', Sec7.card_sup_of_not_mem
    (elemAbelianTwo_z S) (SD.t_sq (A := A)) htz (fun _ ha => comm_zpowers_z S A.t_mem_T ha), hz]

theorem B_le_E (r : X) : S.B ≤ S.E r := by
  rw [B_eq]
  exact sup_le (sup_le (zpowers_le.mpr (Frame.z_mem_E r)) (zpowers_le.mpr (Frame.t_mem_E r)))
    (zpowers_le.mpr (Frame.k_mem_E r))

variable {S} in
theorem frame_yF_not_mem_B (F : Frame S) : F.yF ∉ S.B := by
  intro h
  have hB : S.B ≤ (zpowers S.z ⊔ zpowers F.kF) ⊔ zpowers t := by
    rw [B_eq]
    refine sup_le (sup_le (zpowers_le.mpr (mem_sup_left (mem_sup_left (mem_zpowers _))))
      (zpowers_le.mpr (mem_sup_right (mem_zpowers _)))) (zpowers_le.mpr ?_)
    rcases F.k_eq with h' | h' <;> rw [h']
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_left (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)))
  rcases Sec7.mem_or_of_mem_sup F.elemAbelianTwo_zk (SD.t_sq (A := A))
    (fun a ha => (B_comm_B S Frame.t_mem_B ((sup_le (zpowers_le.mpr Frame.z_mem_B)
      (zpowers_le.mpr F.kF_mem_B)) ha))) (hB h) with h1 | h1
  · exact F.yF_not_mem_zk h1
  · rcases Sec7.mem_or_of_mem_sup (elemAbelianTwo_z S) F.kF_sq
      (fun a ha => comm_zpowers_z S F.kF_mem_T ha) h1 with h2 | h2
    · apply t_not_mem_L (A := A)
      have := mul_mem (inv_mem F.yF_mem_L) (zpowers_le.mpr (z_mem_L S) h2)
      rwa [inv_mul_cancel_left] at this
    · apply F.t_kF_not_mem_L
      have := mul_mem (inv_mem F.yF_mem_L) (zpowers_le.mpr (z_mem_L S) h2)
      rwa [mul_assoc, inv_mul_cancel_left] at this

theorem E_eq_B_sup (r : X) : S.E r = S.B ⊔ zpowers r := by
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left Frame.z_mem_B
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left Frame.t_mem_B
    · exact mem_sup_left Frame.k_mem_B
  · exact sup_le (B_le_E S r) (zpowers_le.mpr (Frame.yi_mem_E r))

theorem card_E {r : X} (h : IsRefl S r) : Nat.card (S.E r) = 16 := by
  rw [E_eq_B_sup, Sec7.card_sup_of_not_mem (elemAbelianTwo_B S) h.sq
    (frame_yF_not_mem_B (frameOf h (Or.inl rfl))) (fun b hb => (B_comm_R S hb h.mem).symm), card_B]

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
