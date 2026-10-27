module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b3b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13b_E8_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 F : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) (hF : NormalIn F 𝒮)
    (hFe : CFSG.Open.IsElemAbelian 2 F) (hFc : Nat.card F = 8) :
    fourGrp x₁ x₂ ≤ F ∧ F ≤ ctxU t tau x₁ x₂ lam := by
  have ht𝒮 : t ∈ 𝒮 := hU (q13b_O_le_U h (q13b_t_mem_O h))
  have hD4 : 4 ≤ Nat.card ↥(F ⊓ centralizer ({t} : Set G)) :=
    S4A.four_le_card_inf_centralizer hF.1
      ((Subgroup.normal_subgroupOf_iff hF.1).mpr (fun h k hh hk => hF.2 k hk h hh))
      hFe hFc ht𝒮 (q13a_t_mul_self h)
  have hDdvd : Nat.card ↥(F ⊓ centralizer ({t} : Set G)) ∣ 8 := by
    have h := Subgroup.card_dvd_of_le
      (show F ⊓ centralizer ({t} : Set G) ≤ F from inf_le_left)
    rwa [hFc] at h
  have hcases : Nat.card ↥(F ⊓ centralizer ({t} : Set G)) = 4 ∨
      Nat.card ↥(F ⊓ centralizer ({t} : Set G)) = 8 := by
    have hle : Nat.card ↥(F ⊓ centralizer ({t} : Set G)) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hDdvd
    interval_cases Nat.card ↥(F ⊓ centralizer ({t} : Set G))
    · exact Or.inl rfl
    · norm_num at hDdvd
    · norm_num at hDdvd
    · norm_num at hDdvd
    · exact Or.inr rfl
  rcases hcases with h4 | h8
  · have hDeq := q13b_E8_cent_four h h𝒮 hU hF hFe hFc h4
    refine ⟨?_, ?_⟩
    · rw [← hDeq]; exact inf_le_left
    · exact (q13b_le_N_S h h𝒮 hU hF hFe hFc hDeq).trans (q13b_N_S_le_U h h𝒮 hU)
  · have hDF : F ⊓ centralizer ({t} : Set G) = F :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hFt : F ≤ centralizer ({t} : Set G) := by rw [← hDF]; exact inf_le_right
    exact q13b_E8_V_le_of_le_cent h h𝒮 hU hF hFe hFc hFt

theorem q13b_N_unique (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 F : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) (hF : NormalIn F 𝒮)
    (hFe : CFSG.Open.IsElemAbelian 2 F) (hFc : Nat.card F = 8) :
    F = ctxN tau x₁ x₂ := by
  obtain ⟨hfour, hFU⟩ := q13b_E8_aux h h𝒮 hU hF hFe hFc
  have hVU : NormalIn F (ctxU t tau x₁ x₂ lam) :=
    ⟨hFU, fun g hg k hk => hF.2 g (hU hg) k hk⟩
  exact q13b_V_eq_N h hVU hFe hFc hfour

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
