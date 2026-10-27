module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAKN1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAKN2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAGL6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CANo3b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

theorem y7c_no_three (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) {g₁ g₂ g₃ : Γ} (h12 : conjSub g₁ K ≠ conjSub g₂ K)
    (h13 : conjSub g₁ K ≠ conjSub g₃ K) (h23 : conjSub g₂ K ≠ conjSub g₃ K) : False := by
  have hc : ∀ g : Γ, CFSG.IsComponent (conjSub g K) := fun g => y7c_isComponent_conjSub hK g
  have hN : ∀ g : Γ, conjSub g K ≤ Subgroup.normalClosure (J : Set Γ) :=
    fun g => y7c_conjSub_K_le_N c hK hJK g
  have hker : ∀ g : Γ, ∀ n ∈ Subgroup.normalClosure (J : Set Γ), ρ n = 1 →
      ∀ k ∈ conjSub g K, n * k = k * n :=
    fun g n _ hn k hk => y7c_ker_cent_N c hK hJK hn (hN g hk)
  have hdvd := y7c_seven_cube_dvd ρ (hN g₁) (hN g₂) (hN g₃)
    (y7c_comm_of_components (hc g₁) (hc g₂) h12) (y7c_comm_of_components (hc g₁) (hc g₃) h13)
    (y7c_comm_of_components (hc g₂) (hc g₃) h23) (hker g₁) (hker g₂) (hker g₃)
    (y7c_exists_y7_conj c hK hJK g₁) (y7c_exists_y7_conj c hK hJK g₂)
    (y7c_exists_y7_conj c hK hJK g₃)
  exact y7c_not_dvd_seven_cube c.M_E hdvd

theorem y7c_conj_cases (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) {g₂ : Γ} (hne : conjSub g₂ K ≠ K) (g : Γ) :
    conjSub g K = K ∨ conjSub g K = conjSub g₂ K := by
  by_contra h
  push_neg at h
  refine y7c_no_three c hK hJK (g₁ := 1) (g₂ := g₂) (g₃ := g) ?_ ?_ ?_
  · rw [y7c_conjSub_one]
    exact hne.symm
  · rw [y7c_conjSub_one]
    exact h.1.symm
  · exact h.2.symm

end CFSG.OddStandard.HigherRank.YamadaG23
