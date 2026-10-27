module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrM

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

namespace FzCSy3bStr

variable {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private theorem fzc_sy3_q_aU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a ∈ U :=
  hs.chain.2.2.1 (hs.chain.2.1 hs.a_mem)

private theorem fzc_sy3_q_bU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : b ∈ U :=
  hs.chain.2.2.1 hs.b_mem

private theorem fzc_sy3_q_cU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : c ∈ U :=
  hs.chain.2.2.2.2.1 hs.c_mem

private theorem fzc_sy3_q_abU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a * b ∈ U :=
  mul_mem (fzc_sy3_q_aU hs) (fzc_sy3_q_bU hs)

private theorem fzc_sy3_q_acU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a * c ∈ U :=
  mul_mem (fzc_sy3_q_aU hs) (fzc_sy3_q_cU hs)

private theorem fzc_sy3_q_bcU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : b * c ∈ U :=
  mul_mem (fzc_sy3_q_bU hs) (fzc_sy3_q_cU hs)

private theorem fzc_sy3_q_sq_eq (n u : G) :
    (n * u) ^ 2 = (n * (u * n * u⁻¹)) * (u * u) := by
  rw [pow_two]; group

private theorem fzc_sy3_q_sq {N : Subgroup G} {n u : G} (hn : n ∈ N)
    (hconj : u * n * u⁻¹ ∈ N) (hu2 : u * u ∈ N) : (n * u) ^ 2 ∈ N := by
  rw [fzc_sy3_q_sq_eq]
  exact mul_mem (mul_mem hn hconj) hu2

private theorem fzc_sy3_q_comm_eq (g h : G) :
    ⁅g, h⁆ = (g * h) ^ 2 * (h⁻¹ * (g ^ 2)⁻¹ * h) * (h ^ 2)⁻¹ := by
  rw [commutatorElement_def]
  simp only [pow_two]
  group

private theorem fzc_sy3_q_comm {N : Subgroup G} {g h : G} (hgh : (g * h) ^ 2 ∈ N)
    (hg2 : g ^ 2 ∈ N) (hh2 : h ^ 2 ∈ N) (hnorm : ∀ n ∈ N, h⁻¹ * n * h ∈ N) :
    ⁅g, h⁆ ∈ N := by
  rw [fzc_sy3_q_comm_eq]
  exact mul_mem (mul_mem hgh (hnorm _ (inv_mem hg2))) (inv_mem hh2)

theorem P_elem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    (∀ g ∈ P, g ^ 2 ∈ Wp) ∧ ∀ g ∈ P, ∀ h ∈ P, ⁅g, h⁆ ∈ Wp := by
  have hPU : P ≤ U := hs.chain.2.2.1
  have hsq : ∀ g ∈ P, g ^ 2 ∈ Wp := by
    intro g hg
    obtain ⟨f, hf, hg_eq | hg_eq⟩ := (hs.P_mem).mp hg
    · rw [hg_eq]
      obtain ⟨w, hw, hf_eq | hf_eq⟩ := (hs.F_mem).mp hf
      · rw [hf_eq]; exact pow_mem hw 2
      · rw [hf_eq]
        exact fzc_sy3_q_sq (N := Wp) hw (hs.nrm a (fzc_sy3_q_aU hs) w hw) hs.sq_mem.1
    · rw [hg_eq]
      obtain ⟨w, hw, hf_eq | hf_eq⟩ := (hs.F_mem).mp hf
      · rw [hf_eq]
        exact fzc_sy3_q_sq (N := Wp) hw (hs.nrm b (fzc_sy3_q_bU hs) w hw) hs.sq_mem.2.1
      · rw [hf_eq]
        have heq : (w * a) * b = w * (a * b) := by group
        rw [heq]
        exact fzc_sy3_q_sq (N := Wp) hw (hs.nrm (a * b) (fzc_sy3_q_abU hs) w hw)
          hs.sq_mem.2.2.2.1
  refine ⟨hsq, ?_⟩
  intro g hg h hh
  have hgh : (g * h) ^ 2 ∈ Wp := hsq (g * h) (mul_mem hg hh)
  have hg2 : g ^ 2 ∈ Wp := hsq g hg
  have hh2 : h ^ 2 ∈ Wp := hsq h hh
  exact fzc_sy3_q_comm hgh hg2 hh2 (fun n hn => by
    simpa using hs.nrm h⁻¹ (inv_mem (hPU hh)) n hn)

theorem M₂_elem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    (∀ g ∈ M₂, g ^ 2 ∈ Wp) ∧ ∀ g ∈ M₂, ∀ h ∈ M₂, ⁅g, h⁆ ∈ Wp := by
  have hM₂U : M₂ ≤ U := hs.chain.2.2.2.2.1
  have hsq : ∀ g ∈ M₂, g ^ 2 ∈ Wp := by
    intro g hg
    obtain ⟨f, hf, hg_eq | hg_eq⟩ := (hs.M₂_mem).mp hg
    · rw [hg_eq]
      obtain ⟨w, hw, hf_eq | hf_eq⟩ := (hs.F_mem).mp hf
      · rw [hf_eq]; exact pow_mem hw 2
      · rw [hf_eq]
        exact fzc_sy3_q_sq (N := Wp) hw (hs.nrm a (fzc_sy3_q_aU hs) w hw) hs.sq_mem.1
    · rw [hg_eq]
      obtain ⟨w, hw, hf_eq | hf_eq⟩ := (hs.F_mem).mp hf
      · rw [hf_eq]
        exact fzc_sy3_q_sq (N := Wp) hw (hs.nrm c (fzc_sy3_q_cU hs) w hw) hs.sq_mem.2.2.1
      · rw [hf_eq]
        have heq : (w * a) * c = w * (a * c) := by group
        rw [heq]
        exact fzc_sy3_q_sq (N := Wp) hw (hs.nrm (a * c) (fzc_sy3_q_acU hs) w hw)
          hs.sq_mem.2.2.2.2
  refine ⟨hsq, ?_⟩
  intro g hg h hh
  have hgh : (g * h) ^ 2 ∈ Wp := hsq (g * h) (mul_mem hg hh)
  have hg2 : g ^ 2 ∈ Wp := hsq g hg
  have hh2 : h ^ 2 ∈ Wp := hsq h hh
  exact fzc_sy3_q_comm hgh hg2 hh2 (fun n hn => by
    simpa using hs.nrm h⁻¹ (inv_mem (hM₂U hh)) n hn)

theorem U_elem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    (∀ g ∈ U, g ^ 2 ∈ F) ∧ (∀ g ∈ U, ∀ h ∈ U, ⁅g, h⁆ ∈ F) ∧
      ∀ g ∈ U, ∀ f ∈ F, g * f * g⁻¹ ∈ F := by
  have hPU : P ≤ U := hs.chain.2.2.1
  have hWF : Wp ≤ F := hs.chain.1
  have hbcF : (b * c) * (b * c) ∈ F := by
    obtain ⟨w, hw, hw_eq⟩ := hs.bc_sq
    rw [hw_eq]
    exact mul_mem (hWF hw) hs.a_mem
  have hsq : ∀ g ∈ U, g ^ 2 ∈ F := by
    intro g hg
    obtain ⟨p, hp, hg_eq | hg_eq⟩ := (hs.U_mem).mp hg
    · rw [hg_eq]
      obtain ⟨f, hf, hp_eq | hp_eq⟩ := (hs.P_mem).mp hp
      · rw [hp_eq]; exact pow_mem hf 2
      · rw [hp_eq]
        exact fzc_sy3_q_sq (N := F) hf (hs.norm_F b (fzc_sy3_q_bU hs) f hf)
          (hWF hs.sq_mem.2.1)
    · rw [hg_eq]
      obtain ⟨f, hf, hp_eq | hp_eq⟩ := (hs.P_mem).mp hp
      · rw [hp_eq]
        exact fzc_sy3_q_sq (N := F) hf (hs.norm_F c (fzc_sy3_q_cU hs) f hf)
          (hWF hs.sq_mem.2.2.1)
      · rw [hp_eq]
        have heq : (f * b) * c = f * (b * c) := by group
        rw [heq]
        exact fzc_sy3_q_sq (N := F) hf (hs.norm_F (b * c) (fzc_sy3_q_bcU hs) f hf) hbcF
  refine ⟨hsq, ?_, hs.norm_F⟩
  intro g hg h hh
  have hgh : (g * h) ^ 2 ∈ F := hsq (g * h) (mul_mem hg hh)
  have hg2 : g ^ 2 ∈ F := hsq g hg
  have hh2 : h ^ 2 ∈ F := hsq h hh
  exact fzc_sy3_q_comm hgh hg2 hh2 (fun n hn => by
    simpa using hs.norm_F h⁻¹ (inv_mem hh) n hn)

end FzCSy3bStr

end CFSG.OddStandard.SmallF3.FritzII
