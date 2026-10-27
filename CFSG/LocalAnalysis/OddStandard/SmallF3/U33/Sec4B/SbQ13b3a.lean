module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13b_N_S_le_U (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    normalizer (S : Set G) ⊓ 𝒮 ≤ ctxU t tau x₁ x₂ lam := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨𝒯, h𝒮𝒯⟩ := h𝒮.exists_le_sylow
  have hS_lt : S < (𝒯 : Subgroup G) :=
    lt_of_lt_of_le (q13b_S_lt_U h) (hU.trans h𝒮𝒯)
  have hS1M : ctxS1 S (𝒯 : Subgroup G) ≤ ctxM t tau x₁ x₂ := h.c11.l49.1 𝒯 hS_lt
  intro x hx
  obtain ⟨hxN, hx𝒮⟩ := Subgroup.mem_inf.mp hx
  have hx𝒯 : x ∈ (𝒯 : Subgroup G) := h𝒮𝒯 hx𝒮
  have hxS1 : x ∈ ctxS1 S (𝒯 : Subgroup G) := by
    rw [ctxS1]
    exact Subgroup.mem_inf.mpr ⟨hxN, hx𝒯⟩
  have hxM : x ∈ ctxM t tau x₁ x₂ := hS1M hxS1
  have hxMS : x ∈ ctxM t tau x₁ x₂ ⊓ 𝒮 := Subgroup.mem_inf.mpr ⟨hxM, hx𝒮⟩
  have hEq : ctxM t tau x₁ x₂ ⊓ 𝒮 = ctxU t tau x₁ x₂ lam :=
    S4A.eq_of_isPGroup_of_odd_relIndex (H := ctxM t tau x₁ x₂)
      (S := ctxU t tau x₁ x₂ lam) (Q := ctxM t tau x₁ x₂ ⊓ 𝒮)
      (le_inf (q13b_U_le_M h) hU) inf_le_left (h𝒮.to_le inf_le_right) h.c11.U_sylow.2.2
  rw [hEq] at hxMS
  exact hxMS

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
