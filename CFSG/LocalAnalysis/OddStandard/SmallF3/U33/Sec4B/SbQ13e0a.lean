module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma e0a_closure_pair_iff {a b u : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    u ∈ closure ({a, b} : Set G) ↔ u = 1 ∨ u = a ∨ u = b ∨ u = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private lemma e0a_y_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) : x₁ ^ 2 * x₁ ^ 2 = 1 := by
  have h4 : x₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₁
    rwa [h.c11.wreath.ord_x₁] at this
  rw [← pow_add, show (2 : ℕ) + 2 = 4 from rfl, h4]

private lemma e0a_y_z_comm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 :=
  CFSG.Open.IsElemAbelian.comm (WreathRel.fourGrp_eq_omega h.c11.wreath).2.1
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private lemma e0a_conj_tau_eq_sq_mul_tau {a : G} (hinv : tau * a * tau⁻¹ = a⁻¹) :
    a * tau * a⁻¹ = a ^ 2 * tau := by
  calc a * tau * a⁻¹
      = a * (tau * a⁻¹ * tau⁻¹) * tau := by group
    _ = a * (tau * a * tau⁻¹)⁻¹ * tau := by
          rw [show tau * a⁻¹ * tau⁻¹ = (tau * a * tau⁻¹)⁻¹ by group]
    _ = a * (a⁻¹)⁻¹ * tau := by rw [hinv]
    _ = a ^ 2 * tau := by rw [inv_inv, pow_two]

theorem q13e_t_mem_L : t ∈ q13L t tau x₁ x₂ rho om := by
  change t ∈ normalizer ((q13E0 t tau x₁ x₂ rho om : Subgroup G) : Set G)
  exact Subgroup.le_normalizer (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem q13e_lam_mem_L (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    lam ∈ q13L t tau x₁ x₂ rho om :=
  hD.M_le_L (q13a_mem_M h).2.2.2.1

theorem q13e_f_mem_L (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    (t * lam) ∈ q13L t tau x₁ x₂ rho om :=
  mul_mem q13e_t_mem_L (q13e_lam_mem_L h hD)

theorem q13e_f_inv (h : Q13Om t L S x₁ x₂ lam rho tau om) : (t * lam)⁻¹ = (t * lam) :=
  inv_eq_of_mul_eq_one_right (q13c_tlam_sq h)

theorem q13e_f_t (h : Q13Om t L S x₁ x₂ lam rho tau om) : (t * lam) * t = t * (t * lam) := by
  rw [mul_assoc, (q13a_t_comm h).1.symm]

theorem q13e_lam_gam (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om) :
    lam * (t * om) * lam⁻¹ = (t * om) := by
  have ht : lam * t * lam⁻¹ = t := by
    rw [← (q13a_t_comm h).1]
    group
  calc lam * (t * om) * lam⁻¹
      = (lam * t * lam⁻¹) * (lam * om * lam⁻¹) := by group
    _ = t * om := by rw [ht, hC.lam_om]

theorem q13e_f_gam (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om) :
    (t * lam) * (t * om) * (t * lam)⁻¹ = (t * om)⁻¹ := by
  have ht2 : t * t = 1 := q13a_t_mul_self h
  have hom2 : om * om = 1 := h.om_sq
  have hkey : t * (t * om) * t⁻¹ = om * t := by
    calc t * (t * om) * t⁻¹ = (t * t) * (om * t⁻¹) := by group
      _ = 1 * (om * t) := by
            rw [ht2, show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht2]
      _ = om * t := by rw [one_mul]
  have hrinv : (t * om)⁻¹ = om * t := by
    rw [mul_inv_rev, show om⁻¹ = om from inv_eq_of_mul_eq_one_right hom2,
      show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht2]
  calc (t * lam) * (t * om) * (t * lam)⁻¹
      = t * (lam * (t * om) * lam⁻¹) * t⁻¹ := by group
    _ = t * (t * om) * t⁻¹ := by rw [q13e_lam_gam h hC]
    _ = (t * om)⁻¹ := by rw [hkey, hrinv]

theorem q13e_f_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, (t * lam) * a * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ := by
  intro a ha
  have hla : lam * a * lam⁻¹ ∈ q13A t tau x₁ x₂ rho := (q13a_A_inv h a ha).2.1
  calc (t * lam) * a * (t * lam)⁻¹ = t * (lam * a * lam⁻¹) * t⁻¹ := by group
    _ = (lam * a * lam⁻¹)⁻¹ := q13a_t_inv_A h (lam * a * lam⁻¹) hla

theorem q13e_f_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (t * lam) * tau * (t * lam)⁻¹ = tau := by
  have ht : t * tau = tau * t := (q13a_t_comm h).2.2
  have hl : lam * tau = tau * lam := q13c_lam_cent_tau h
  have hcomm : (t * lam) * tau = tau * (t * lam) := by
    calc (t * lam) * tau = t * (lam * tau) := by group
      _ = t * (tau * lam) := by rw [hl]
      _ = (t * tau) * lam := by group
      _ = (tau * t) * lam := by rw [ht]
      _ = tau * (t * lam) := by group
  rw [hcomm]
  group

theorem q13e_f_V (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ v ∈ fourGrp x₁ x₂, (t * lam) * v * (t * lam)⁻¹ ∈ fourGrp x₁ x₂ := by
  have hfM : t * lam ∈ ctxM t tau x₁ x₂ :=
    mul_mem (q13a_mem_M h).1 (q13a_mem_M h).2.2.2.1
  exact h.c11.normal_V.2 (t * lam) hfM

theorem q13e_mem_V (h : Q13Om t L S x₁ x₂ lam rho tau om) {v : G} :
    v ∈ fourGrp x₁ x₂ ↔ v = 1 ∨ v = x₁ ^ 2 ∨ v = (x₁ * x₂) ^ 2 ∨ v = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  rw [fourGrp]
  exact e0a_closure_pair_iff (e0a_y_sq h) h.c11.wreath.sq_x₁x₂_mul_self (e0a_y_z_comm h)

theorem q13e_x_mem_M (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ∈ ctxM t tau x₁ x₂ ∧ x₂ ∈ ctxM t tau x₁ x₂ := by
  obtain ⟨-, -, hx₁, hx₂, -, -⟩ := p0_gens_mem_M h.c11.toCtx10.toCtx4
  exact ⟨hx₁, hx₂⟩

theorem q13e_x_mem_L (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    x₁ ∈ q13L t tau x₁ x₂ rho om ∧ x₂ ∈ q13L t tau x₁ x₂ rho om := by
  obtain ⟨hx₁, hx₂⟩ := q13e_x_mem_M h
  exact ⟨hD.M_le_L hx₁, hD.M_le_L hx₂⟩

theorem q13e_x₂_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) : x₂ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 :=
  h.c11.wreath.x₂_sq

theorem q13e_x_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ * tau * x₁⁻¹ = x₁ ^ 2 * tau ∧ x₂ * tau * x₂⁻¹ = x₂ ^ 2 * tau := by
  obtain ⟨-, -, -, htau₁, -, -⟩ := q13a_x₁_facts h
  have htau₂ : tau * x₂ * tau⁻¹ = x₂⁻¹ := (Ctx4.m12Rel h.c11.toCtx10.toCtx4).tau_x₂
  exact ⟨e0a_conj_tau_eq_sq_mul_tau htau₁, e0a_conj_tau_eq_sq_mul_tau htau₂⟩

theorem q13e_x_cent_V (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ v ∈ fourGrp x₁ x₂, x₁ * v = v * x₁ ∧ x₂ * v = v * x₂ := by
  have hcomm : Commute x₁ x₂ := h.c11.wreath.comm
  have hx₁_cent : x₁ ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [fourGrp, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases hu with rfl | rfl
    · rw [← pow_succ, ← pow_succ']
    · exact ((Commute.refl x₁).mul_right hcomm).pow_right 2 |>.eq.symm
  have hx₂_cent : x₂ ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [fourGrp, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases hu with rfl | rfl
    · exact (hcomm.symm.pow_right 2).eq.symm
    · exact ((hcomm.mul_left (Commute.refl x₂)).symm.pow_right 2).eq.symm
  intro v hv
  exact ⟨(Subgroup.mem_centralizer_iff.mp hx₁_cent v hv).symm,
    (Subgroup.mem_centralizer_iff.mp hx₂_cent v hv).symm⟩

theorem q13e_x_sq_mem_V (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ^ 2 ∈ fourGrp x₁ x₂ ∧ x₂ ^ 2 ∈ fourGrp x₁ x₂ := by
  refine ⟨Subgroup.subset_closure (by simp), ?_⟩
  rw [q13e_x₂_sq h]
  exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
