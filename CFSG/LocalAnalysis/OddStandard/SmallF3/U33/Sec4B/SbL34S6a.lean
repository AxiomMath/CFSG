module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4B0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section General

variable {a b : G}

theorem mem_closure_pair_iff (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (u : G) :
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
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem elemAbelian_closure_pair (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    CFSG.Open.IsElemAbelian 2 (closure ({a, b} : Set G)) := by
  refine ⟨Subgroup.isMulCommutative_closure ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hab
    · exact hab.symm
    · exact absurd rfl hxy
  · intro x hx
    rcases (mem_closure_pair_iff ha hb hab x).mp hx with rfl | rfl | rfl | rfl
    · simp
    · rw [pow_two]; exact ha
    · rw [pow_two]; exact hb
    · rw [pow_two]
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]

theorem card_closure_pair (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (closure ({a, b} : Set G)) = 4 := by
  have hab1 : a * b ≠ 1 := by
    intro h
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right ha] at h1
    exact hne h1.symm
  have hab_a : a * b ≠ a := fun h => hb1 (mul_left_cancel (h.trans (mul_one a).symm))
  have hab_b : a * b ≠ b := fun h => ha1 (mul_right_cancel (h.trans (one_mul b).symm))
  have hsub : (closure ({a, b} : Set G) : Set G) ⊆ ({1, a, b, a * b} : Set G) := by
    intro x hx
    rcases (mem_closure_pair_iff ha hb hab x).mp hx with h | h | h | h <;> simp [h]
  have hsub' : ({1, a, b, a * b} : Set G) ⊆ (closure ({a, b} : Set G) : Set G) := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hset : ((closure ({a, b} : Set G) : Set G)) = ({1, a, b, a * b} : Set G) :=
    Set.Subset.antisymm hsub hsub'
  have hncard : ({1, a, b, a * b} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1⟩),
      Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hne, Ne.symm hab_a⟩),
      Set.ncard_insert_of_notMem (by
          simp only [Set.mem_singleton_iff]
          exact Ne.symm hab_b),
      Set.ncard_singleton]
  calc Nat.card (closure ({a, b} : Set G))
      = Nat.card ((closure ({a, b} : Set G) : Set G)) := rfl
    _ = ((closure ({a, b} : Set G) : Set G)).ncard := Nat.card_coe_set_eq _
    _ = ({1, a, b, a * b} : Set G).ncard := by rw [hset]
    _ = 4 := hncard

end General

section Basic

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

private theorem lam_mem_L : lam ∈ L := by
  have h : lam ∈ S ⊓ L := by rw [hc.inf_eq]; exact subset_closure (by simp)
  exact h.2

private theorem fourGrp_le_L : fourGrp x₁ x₂ ≤ L := by
  have hV : fourGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
    rw [fourGrp, wreathGrp, closure_le]
    rintro _ (rfl | rfl)
    · exact pow_mem (subset_closure (by simp)) 2
    · exact pow_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) 2
  intro a ha
  have h' : a ∈ S ⊓ L := by rw [hc.inf_eq]; exact hV ha
  exact h'.2

theorem lam_mul_self : lam * lam = 1 := by
  have h1 := pow_orderOf_eq_one lam
  rw [hc.wreath.ord_lam] at h1
  simpa [pow_two] using h1

private theorem lam_conj_x₂ : lam * x₂ * lam⁻¹ = x₁ :=
  calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [hc.wreath.conj_x₁]
    _ = (lam * lam) * x₁ * (lam * lam)⁻¹ := by group
    _ = x₁ := by rw [lam_mul_self hc]; group

theorem t_comm_lam : t * lam = lam * t :=
  (mem_centralizer_iff.mp hc.hyp.mem_centralizer lam (lam_mem_L hc)).symm

theorem lam_comm_tau : lam * tau = tau * lam :=
  hc.tau_lam.symm

theorem q_mul_self : (t * lam) * (t * lam) = 1 := by
  calc (t * lam) * (t * lam) = t * (lam * t) * lam := by group
    _ = t * (t * lam) * lam := by rw [← t_comm_lam hc]
    _ = (t * t) * (lam * lam) := by group
    _ = 1 := by rw [hc.t_mul_self, lam_mul_self hc, one_mul]

theorem q_comm_tau : (t * lam) * tau = tau * (t * lam) := by
  calc (t * lam) * tau = t * (lam * tau) := by group
    _ = t * (tau * lam) := by rw [lam_comm_tau hc]
    _ = (t * tau) * lam := by group
    _ = (tau * t) * lam := by rw [hc.t_comm_tau]
    _ = tau * (t * lam) := by group

theorem q_comm_ttau : (t * lam) * (t * tau) = (t * tau) * (t * lam) := by
  calc (t * lam) * (t * tau) = t * (lam * (t * tau)) := by group
    _ = t * (lam * (tau * t)) := by rw [hc.t_comm_tau]
    _ = t * ((lam * tau) * t) := by group
    _ = t * ((tau * lam) * t) := by rw [lam_comm_tau hc]
    _ = (t * tau) * (lam * t) := by group
    _ = (t * tau) * (t * lam) := by rw [← t_comm_lam hc]

theorem V_comm_t : ∀ a ∈ fourGrp x₁ x₂, t * a = a * t := by
  intro a ha
  exact (mem_centralizer_iff.mp hc.hyp.mem_centralizer a (fourGrp_le_L hc ha)).symm

theorem y_mul_self : x₁ ^ 2 * x₁ ^ 2 = 1 := by
  rw [← pow_two]; exact hc.y_sq

theorem z_mul_self : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
  rw [← pow_two]; exact hc.z_sq

theorem y_comm_z : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 :=
  ((Commute.refl x₁).mul_right hc.x₁_comm_x₂).pow_pow 2 2

theorem z_ne_one : (x₁ * x₂) ^ 2 ≠ 1 := fun h => by
  apply hc.y_ne_x₂_sq
  rw [hc.x₂_sq, h, mul_one]

theorem y_ne_z : x₁ ^ 2 ≠ (x₁ * x₂) ^ 2 := fun h => by
  apply hc.x₂_sq_ne_one
  rw [hc.x₂_sq, ← h, ← pow_two]; exact hc.y_sq

theorem mem_fourGrp_iff (u : G) : u ∈ fourGrp x₁ x₂ ↔
    u = 1 ∨ u = x₁ ^ 2 ∨ u = (x₁ * x₂) ^ 2 ∨ u = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  show u ∈ closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) ↔ _
  exact mem_closure_pair_iff (y_mul_self hc) (z_mul_self hc) (y_comm_z hc) u

theorem card_fourGrp : Nat.card (fourGrp x₁ x₂) = 4 := by
  rw [fourGrp]
  exact card_closure_pair (y_mul_self hc) (z_mul_self hc) (y_comm_z hc) hc.y_ne_one
    (z_ne_one hc) (y_ne_z hc)

theorem fourGrp_elemAbelian : CFSG.Open.IsElemAbelian 2 (fourGrp x₁ x₂) := by
  rw [fourGrp]
  exact elemAbelian_closure_pair (y_mul_self hc) (z_mul_self hc) (y_comm_z hc)

theorem q_conj_y : (t * lam) * x₁ ^ 2 * (t * lam)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  have hw : x₂ ^ 2 ∈ fourGrp x₁ x₂ := by
    rw [hc.x₂_sq]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  calc (t * lam) * x₁ ^ 2 * (t * lam)⁻¹ = t * (lam * x₁ ^ 2 * lam⁻¹) * t⁻¹ := by group
    _ = t * x₂ ^ 2 * t⁻¹ := by rw [conj_pow.symm, hc.wreath.conj_x₁]
    _ = x₂ ^ 2 := by rw [V_comm_t hc _ hw]; group
    _ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := hc.x₂_sq

theorem q_conj_z : (t * lam) * (x₁ * x₂) ^ 2 * (t * lam)⁻¹ = (x₁ * x₂) ^ 2 := by
  have hz : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  calc (t * lam) * (x₁ * x₂) ^ 2 * (t * lam)⁻¹
      = t * (lam * (x₁ * x₂) ^ 2 * lam⁻¹) * t⁻¹ := by group
    _ = t * (x₁ * x₂) ^ 2 * t⁻¹ := by
        rw [conj_pow.symm,
          show lam * (x₁ * x₂) * lam⁻¹ =
            (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) by group,
          hc.wreath.conj_x₁, lam_conj_x₂ hc, hc.x₁_comm_x₂]
    _ = (x₁ * x₂) ^ 2 := by rw [V_comm_t hc _ hz]; group

theorem CV_q {u : G} (hu : u ∈ fourGrp x₁ x₂) (h : (t * lam) * u * (t * lam)⁻¹ = u) :
    u = 1 ∨ u = (x₁ * x₂) ^ 2 := by
  have hqy := q_conj_y hc
  have hqz := q_conj_z hc
  rcases (mem_fourGrp_iff hc u).mp hu with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso
    rw [hqy] at h
    exact z_ne_one hc (mul_left_cancel (h.trans (mul_one _).symm))
  · exact Or.inr rfl
  · exfalso
    have hq : (t * lam) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (t * lam)⁻¹ =
        (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by
      rw [show (t * lam) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (t * lam)⁻¹ =
            ((t * lam) * x₁ ^ 2 * (t * lam)⁻¹) *
              ((t * lam) * (x₁ * x₂) ^ 2 * (t * lam)⁻¹) by group,
        hqy, hqz]
    exact z_ne_one hc
      (mul_left_cancel (((h.symm.trans hq).symm).trans (mul_one _).symm))

end Basic

end CFSG.OddStandard.SmallF3.HarrisU33.L34
