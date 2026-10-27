module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrW
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

namespace FzCSy3bStr

variable {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

theorem t_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : t ∈ Wp := by
  rw [hs.Wp_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem a_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a ∈ F := by
  rw [hs.F_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)

theorem b_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : b ∈ P := by
  rw [hs.P_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)

theorem c_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : c ∈ M₂ := by
  rw [hs.M₂_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

private theorem fzc_sy3_h_x1_mem : x₁ ∈ baseGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

private theorem fzc_sy3_h_x2_mem : x₂ ∈ baseGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

private theorem fzc_sy3_h_t_mul_E (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U)
    {g : G} (hg : g * t ∈ baseGrp x₁ x₂) : t * g ∈ baseGrp x₁ x₂ := by
  have hc : Commute t (g * t) := hs.fzc_commute_t_E (g * t) hg
  have h : t * (g * t) = (g * t) * t := hc.eq
  rw [← mul_assoc] at h
  have h' : t * g = g * t := mul_right_cancel h
  rw [h']
  exact hg

private theorem fzc_sy3_h_aU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a ∈ U :=
  hs.chain.2.2.1 (hs.chain.2.1 (a_mem hs))

private theorem fzc_sy3_h_bU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : b ∈ U :=
  hs.chain.2.2.1 (b_mem hs)

private theorem fzc_sy3_h_cU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : c ∈ U :=
  hs.chain.2.2.2.2.1 (c_mem hs)

theorem sq_tE (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    t * (a * a) ∈ baseGrp x₁ x₂ ∧ t * (b * b) ∈ baseGrp x₁ x₂ ∧ t * (c * c) ∈ baseGrp x₁ x₂ ∧
      t * ((a * b) * (a * b)) ∈ baseGrp x₁ x₂ ∧ t * ((a * c) * (a * c)) ∈ baseGrp x₁ x₂ := by
  have ht2 : t * t = 1 := by simpa [pow_two] using hs.t_sq
  have ha : a * a * t ∈ baseGrp x₁ x₂ := by
    rw [show a * a = a ^ 2 by rw [pow_two]]
    rcases hs.e₀ with h | h <;> rw [h]
    · exact mul_mem fzc_sy3_h_x1_mem (pow_mem fzc_sy3_h_x2_mem 3)
    · exact mul_mem (pow_mem fzc_sy3_h_x1_mem 3) fzc_sy3_h_x2_mem
  have hb : b * b * t ∈ baseGrp x₁ x₂ := by
    rw [show b * b = b ^ 2 by rw [pow_two]]
    exact hs.b_sq
  have hcc : c * c * t ∈ baseGrp x₁ x₂ := by
    have hct : c * c = t := by rw [← pow_two, hs.c_sq]
    rw [hct, ht2]
    exact (baseGrp x₁ x₂).one_mem
  have hab : (a * b) * (a * b) * t ∈ baseGrp x₁ x₂ := by
    rw [show (a * b) * (a * b) = (a * b) ^ 2 by rw [pow_two]]
    exact hs.ab_sq
  have hac : (a * c) * (a * c) * t ∈ baseGrp x₁ x₂ := by
    rw [show (a * c) * (a * c) = (a * c) ^ 2 by rw [pow_two]]
    exact hs.ac_sq
  exact ⟨fzc_sy3_h_t_mul_E hs ha, fzc_sy3_h_t_mul_E hs hb, fzc_sy3_h_t_mul_E hs hcc,
    fzc_sy3_h_t_mul_E hs hab, fzc_sy3_h_t_mul_E hs hac⟩

theorem sq_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    a * a ∈ Wp ∧ b * b ∈ Wp ∧ c * c ∈ Wp ∧ (a * b) * (a * b) ∈ Wp ∧
      (a * c) * (a * c) ∈ Wp := by
  obtain ⟨ha, hb, hc, hab, hac⟩ := sq_tE hs
  exact ⟨(Wp_mem hs).mpr (Or.inr ha), (Wp_mem hs).mpr (Or.inr hb),
    (Wp_mem hs).mpr (Or.inr hc), (Wp_mem hs).mpr (Or.inr hab),
    (Wp_mem hs).mpr (Or.inr hac)⟩

theorem F_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G} :
    g ∈ F ↔ ∃ w ∈ Wp, g = w ∨ g = w * a := by
  rw [hs.F_eq]
  exact CFSG.GH74.GLS.Stage1.Thm6.Sec13.mem_sup_zpowers_sq (sq_mem hs).1
    (fun q hq => hs.nrm a (fzc_sy3_h_aU hs) q hq)

theorem b_norm_F (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ q ∈ F, b * q * b⁻¹ ∈ F := by
  intro q hq
  rw [F_mem hs] at hq
  obtain ⟨w, hw, hq | hq⟩ := hq
  · rw [hq]
    exact hs.chain.1 (hs.nrm b (fzc_sy3_h_bU hs) w hw)
  · rw [hq]
    have h1 : b * w * b⁻¹ ∈ Wp := hs.nrm b (fzc_sy3_h_bU hs) w hw
    have h2 : b * a * b⁻¹ * a⁻¹ ∈ Wp := hs.b_a
    have heq : b * (w * a) * b⁻¹ =
        (b * w * b⁻¹) * (b * a * b⁻¹ * a⁻¹) * a := by group
    rw [heq]
    exact mul_mem (hs.chain.1 (mul_mem h1 h2)) (a_mem hs)

theorem c_norm_F (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ q ∈ F, c * q * c⁻¹ ∈ F := by
  intro q hq
  rw [F_mem hs] at hq
  obtain ⟨w, hw, hq | hq⟩ := hq
  · rw [hq]
    exact hs.chain.1 (hs.nrm c (fzc_sy3_h_cU hs) w hw)
  · rw [hq]
    have h1 : c * w * c⁻¹ ∈ Wp := hs.nrm c (fzc_sy3_h_cU hs) w hw
    have h2 : c * a * c⁻¹ * a⁻¹ ∈ Wp := hs.c_a
    have heq : c * (w * a) * c⁻¹ =
        (c * w * c⁻¹) * (c * a * c⁻¹ * a⁻¹) * a := by group
    rw [heq]
    exact mul_mem (hs.chain.1 (mul_mem h1 h2)) (a_mem hs)

theorem P_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G} :
    g ∈ P ↔ ∃ f ∈ F, g = f ∨ g = f * b := by
  rw [hs.P_eq]
  exact CFSG.GH74.GLS.Stage1.Thm6.Sec13.mem_sup_zpowers_sq (hs.chain.1 (sq_mem hs).2.1)
    (b_norm_F hs)

theorem c_norm_P (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ q ∈ P, c * q * c⁻¹ ∈ P := by
  intro q hq
  rw [P_mem hs] at hq
  obtain ⟨f, hf, hq | hq⟩ := hq
  · rw [hq]
    exact hs.chain.2.1 (c_norm_F hs f hf)
  · rw [hq]
    have h1 : c * f * c⁻¹ ∈ F := c_norm_F hs f hf
    have h2 : c * b * c⁻¹ * (a * b)⁻¹ ∈ Wp := hs.c_b
    have h3 : a * b ∈ P := mul_mem (hs.chain.2.1 (a_mem hs)) (b_mem hs)
    have heq : c * (f * b) * c⁻¹ =
        (c * f * c⁻¹) * (c * b * c⁻¹ * (a * b)⁻¹) * (a * b) := by group
    rw [heq]
    exact mul_mem (mul_mem (hs.chain.2.1 h1) (hs.chain.2.1 (hs.chain.1 h2))) h3

end FzCSy3bStr

end CFSG.OddStandard.SmallF3.FritzII
