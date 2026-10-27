module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C5

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fzl59c_facts {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
    {x₁ x₂ lam rho tau s u : G} {b : Fin 3 → Fin 2 → G} {T₃ : Subgroup G}
    (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) : Fz59T3Facts t x₁ x₂ s T₃ := by
  have hg := h.grid
  have hZ : fourGrp x₁ x₂ = closure {b 0 0 ^ 2, b 1 0 ^ 2} := h.hZ
  obtain ⟨-, hZe, hZc⟩ := h.ctx.wreath.fourGrp_eq_omega
  have hA : fzl59c_Abs (fourGrp x₁ x₂) s t := fzl59c_abs hg hZ hZe hZc
  have hbT : ∀ i k, b i k ∈ T₃ := by
    intro i k
    rw [h.hT₃, h.hT₂, h.hR]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (subset_closure ⟨(i, k), rfl⟩))
  have huT : u ∈ T₃ := by
    rw [h.hT₃]
    exact Subgroup.mem_sup_right (mem_zpowers u)
  have hle : T₃ ≤ fzl59c_modCent (fourGrp x₁ x₂)
        ((fourGrp x₁ x₂ ⊔ zpowers s : Subgroup G) : Set G) ⊓
      fzl59c_modCent (fourGrp x₁ x₂ ⊔ zpowers s) ({t} : Set G) := by
    have hmem : ∀ g, fzl59c_Gen (fourGrp x₁ x₂) s t g →
        g ∈ fzl59c_modCent (fourGrp x₁ x₂) ((fourGrp x₁ x₂ ⊔ zpowers s : Subgroup G) : Set G) ⊓
          fzl59c_modCent (fourGrp x₁ x₂ ⊔ zpowers s) ({t} : Set G) := fun g hgen =>
      Subgroup.mem_inf.mpr ⟨fzl59c_gen_mem_one hA hgen, fzl59c_gen_mem_two hA hgen⟩
    rw [h.hT₃, h.hT₂, h.hR]
    refine sup_le (sup_le ((closure_le _).mpr ?_) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_)
    · rintro _ ⟨⟨i, k⟩, rfl⟩
      show b i k ∈ _
      match k with
      | 0 => exact hmem _ (fzl59c_gen_p hg hZ i)
      | 1 => exact hmem _ (fzl59c_gen_q hg hZ i)
    · exact hmem _ (fzl59c_gen_lam hg hZ)
    · exact hmem _ (fzl59c_gen_u hg hZ h.u_cases)
  have hT1 : ∀ g ∈ T₃, ∀ x ∈ fourGrp x₁ x₂ ⊔ zpowers s, g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂ :=
    fun g hg x hx => (fzl59c_mem_modCent.mp (Subgroup.mem_inf.mp (hle hg)).1).2 x hx
  have hT2 : ∀ g ∈ T₃, g * t * g⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ ⊔ zpowers s :=
    fun g hg => (fzl59c_mem_modCent.mp (Subgroup.mem_inf.mp (hle hg)).2).2 t (Set.mem_singleton t)
  have hq_s : ∀ i, s * b i 1 = b i 1 * s := by
    intro i
    have h0 := fzl59c_q_s hg i
    rw [mul_inv_eq_iff_eq_mul] at h0
    exact h0.symm
  have hu_z : ∀ i, b i 0 ^ 2 * u = u * b i 0 ^ 2 := by
    intro i
    have h0 := fzl59c_u_z hg h.u_cases i
    rw [mul_inv_eq_iff_eq_mul] at h0
    exact h0.symm
  have hu_s : s * u = u * s := by
    have h0 := fzl59c_u_s hg h.u_cases
    rw [mul_inv_eq_iff_eq_mul] at h0
    exact h0.symm
  have hw₀ : ∃ y ∈ T₃, (∀ x ∈ fourGrp x₁ x₂ ⊔ zpowers s, y * x * y⁻¹ = x) ∧
      y * t * y⁻¹ = t * b 0 0 ^ 2 :=
    ⟨b 0 1, hbT 0 1, fzl59c_cent_B_of (fzl59c_Z_comm_b hg hZ 0 1) (hq_s 0), fzl59c_q_t hg 0⟩
  have hw₁ : ∃ y ∈ T₃, (∀ x ∈ fourGrp x₁ x₂ ⊔ zpowers s, y * x * y⁻¹ = x) ∧
      y * t * y⁻¹ = t * b 1 0 ^ 2 :=
    ⟨b 1 1, hbT 1 1, fzl59c_cent_B_of (fzl59c_Z_comm_b hg hZ 1 1) (hq_s 1), fzl59c_q_t hg 1⟩
  have hws : ∃ y ∈ T₃, (∀ x ∈ fourGrp x₁ x₂ ⊔ zpowers s, y * x * y⁻¹ = x) ∧
      y * t * y⁻¹ = t * s :=
    ⟨u, huT, fzl59c_cent_B_of (fzl59c_Z_comm_of hZ (hu_z 0) (hu_z 1)) hu_s,
      fzl59c_u_t h.u_cases⟩
  have horb : ∀ β ∈ fourGrp x₁ x₂ ⊔ zpowers s, ∃ g ∈ T₃, g * t * g⁻¹ = β * t :=
    fun β hβ => fzl59c_orbit_t hA hZ hw₀ hw₁ hws hβ
  refine ⟨fzl59c_card_B hA, fzl59c_card_F hA, fun g hg f hf => fzl59c_B_nrm hA hT1 hg hf,
    fun g hg f hf => fzl59c_F_nrm hA hT1 hT2 hg hf,
    fun f hf f' hf' => ⟨fzl59c_F_comm hA f hf f' hf', fzl59c_F_sq hA hf⟩, ?_,
    fun β hβ _ => fzl59c_cent_B hA hT1 h.card_T₃ hβ, fzl59c_cent_t hA hT2 h.card_T₃ horb⟩
  intro f hf hfB
  rcases fzl59c_mem_sup_zpowers (fun x hx => (fzl59c_B_comm_t hA hx).symm)
      (by rw [hA.t_sq]; exact one_mem _) hf with hf' | ⟨β, hβ, rfl⟩
  · exact absurd hf' hfB
  · exact horb β hβ

end CFSG.OddStandard.SmallF3.FritzII
