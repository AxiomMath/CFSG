module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma t_mem_ctxX (t tau x₁ x₂ : G) : t ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]; exact Subgroup.subset_closure (by simp)

private lemma y_mem_ctxX (t tau x₁ x₂ : G) : x₁ ^ 2 ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]; exact Subgroup.subset_closure (by simp)

private lemma z_mem_ctxX (t tau x₁ x₂ : G) : (x₁ * x₂) ^ 2 ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]; exact Subgroup.subset_closure (by simp)

private lemma tau_mem_ctxX (t tau x₁ x₂ : G) : tau ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]; exact Subgroup.subset_closure (by simp)

private lemma ctxE_le_ctxX' (t tau x₁ x₂ : G) : ctxE t x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [ctxE]
  refine (Subgroup.closure_le (K := ctxX t tau x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h
  · rw [h]; exact t_mem_ctxX t tau x₁ x₂
  · rw [h]; exact y_mem_ctxX t tau x₁ x₂
  · rw [h]; exact z_mem_ctxX t tau x₁ x₂

private lemma ctxE_le_Pl' (h : Ctx0 t L S x₁ x₂ lam rho) : ctxE t x₁ x₂ ≤ twoCore t ⊔ L := by
  rw [ctxE]
  refine (Subgroup.closure_le (K := twoCore t ⊔ L)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  · exact Subgroup.mem_sup_right (y_z_mem_L h).1
  · exact Subgroup.mem_sup_right (y_z_mem_L h).2

private lemma x1x2_commute_ctxE (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ g ∈ ctxE t x₁ x₂, Commute (x₁ * x₂) g := by
  have hx1x2_L : x₁ * x₂ ∈ L :=
    Subgroup.mul_mem L (generators_mem_L h.toCtx0).1 (generators_mem_L h.toCtx0).2.1
  have ht_comm : Commute (x₁ * x₂) t := mem_invCent_iff.mp (L_le_invCent h.hyp hx1x2_L)
  have hy_comm : Commute (x₁ * x₂) (x₁ ^ 2) :=
    (((Commute.refl x₁).mul_right h.wreath.comm).symm).pow_right 2
  have hz_comm : Commute (x₁ * x₂) ((x₁ * x₂) ^ 2) :=
    (Commute.refl (x₁ * x₂)).pow_right 2
  intro g hg
  rw [ctxE] at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ht_comm
      · exact hy_comm
      · exact hz_comm
  | one => exact Commute.one_right _
  | mul a b ha hb iha ihb => exact iha.mul_right ihb
  | inv a ha iha => exact iha.inv_right

theorem false_of_swap_elem (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1)
    {E : Subgroup G} (hEe : CFSG.Open.IsElemAbelian 2 E) {β : G} (hβ : β ∈ E)
    (hτβ : tau⁻¹ * β * tau ∈ E)
    (hswap : ∀ x ∈ ctxX t tau x₁ x₂, β * x * β⁻¹ ∈ ctxYt t tau x₁ x₂) : False := by
  have hβsq : β * β = 1 := by
    have h := hEe.2 β hβ
    rwa [pow_two] at h
  have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβsq
  have htau_not_Y : tau ∉ ctxYt t tau x₁ x₂ := by
    intro htauY
    rcases mem_ctxYt_cases h h44 htauY with hE | ⟨a, haE, haeq⟩
    · exact h.tau_not_mem (ctxE_le_Pl' h.toCtx0 hE)
    ·
      have h1 : (x₁ * x₂) * a = 1 := by
        have h := congrArg (fun g => tau⁻¹ * g) haeq
        rw [show tau⁻¹ * tau = 1 from inv_mul_cancel tau] at h
        rw [show tau⁻¹ * (tau * (x₁ * x₂) * a) = (x₁ * x₂) * a from by group] at h
        exact h.symm
      have hp_eq : x₁ * x₂ = a⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hpE : x₁ * x₂ ∈ ctxE t x₁ x₂ := by
        rw [hp_eq]; exact Subgroup.inv_mem _ haE
      exact (z_mul_self_ne_one h.toCtx0).2 (h.m2_PT_attained.1.2 (x₁ * x₂) hpE)
  have hτ'_not_E : β * tau * β⁻¹ ∉ ctxE t x₁ x₂ := by
    intro hτ'E
    have hmem : β * (β * tau * β⁻¹) * β⁻¹ ∈ ctxYt t tau x₁ x₂ :=
      hswap (β * tau * β⁻¹) (ctxE_le_ctxX' t tau x₁ x₂ hτ'E)
    have hconj : β * (β * tau * β⁻¹) * β⁻¹ = tau := by
      rw [hβinv]
      calc β * (β * tau * β) * β = (β * β) * tau * (β * β) := by group
        _ = tau := by rw [hβsq]; group
    rw [hconj] at hmem
    exact htau_not_Y hmem
  rcases mem_ctxYt_cases h h44 (hswap tau (tau_mem_ctxX t tau x₁ x₂)) with hτ'E | ⟨a, haE, haeq⟩
  · exact hτ'_not_E hτ'E
  · have hτβ' : tau⁻¹ * β * tau * β⁻¹ = (x₁ * x₂) * a := by
      have h2 : tau⁻¹ * (β * tau * β⁻¹) = (x₁ * x₂) * a := by
        rw [haeq]; group
      calc tau⁻¹ * β * tau * β⁻¹ = tau⁻¹ * (β * tau * β⁻¹) := by group
        _ = (x₁ * x₂) * a := h2
    have hdE : tau⁻¹ * β * tau * β⁻¹ ∈ E :=
      Subgroup.mul_mem E hτβ (Subgroup.inv_mem E hβ)
    have hD1 : (tau⁻¹ * β * tau * β⁻¹) * (tau⁻¹ * β * tau * β⁻¹) = 1 := by
      have h := hEe.2 (tau⁻¹ * β * tau * β⁻¹) hdE
      rwa [pow_two] at h
    have haa : a * a = 1 := by
      have h := h.m2_PT_attained.1.2 a haE
      rwa [pow_two] at h
    have hdd : (tau⁻¹ * β * tau * β⁻¹) * (tau⁻¹ * β * tau * β⁻¹) =
        (x₁ * x₂) ^ 2 * (a * a) := by
      rw [hτβ']
      calc ((x₁ * x₂) * a) * ((x₁ * x₂) * a)
          = ((x₁ * x₂) * a) ^ 2 := by rw [pow_two]
        _ = (x₁ * x₂) ^ 2 * a ^ 2 := (x1x2_commute_ctxE h a haE).mul_pow 2
        _ = (x₁ * x₂) ^ 2 * (a * a) := by rw [show a ^ 2 = a * a from pow_two a]
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      rw [hdd, haa, mul_one] at hD1
      exact hD1
    exact (z_mul_self_ne_one h.toCtx0).2 hz1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
