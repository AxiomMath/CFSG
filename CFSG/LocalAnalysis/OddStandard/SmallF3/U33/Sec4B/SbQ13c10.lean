module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c9

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13c_card_C_le (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau) :
    ∀ 𝒮 : Subgroup G, IsPGroup 2 𝒮 → ctxU t tau x₁ x₂ lam ≤ 𝒮 →
      Nat.card ↥(𝒮 ⊓ centralizer ({t * lam} : Set G)) ≤ 2 ^ 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  suffices H : ∀ n, ∀ 𝒮 : Subgroup G, Nat.card 𝒮 = n → IsPGroup 2 𝒮 →
      ctxU t tau x₁ x₂ lam ≤ 𝒮 →
      Nat.card ↥(𝒮 ⊓ centralizer ({t * lam} : Set G)) ≤ 2 ^ 6 by
    intro 𝒮 h𝒮 hU
    exact H (Nat.card 𝒮) 𝒮 rfl h𝒮 hU
  intro n
  refine Nat.strong_induction_on n ?_
  intro k ih 𝒮 hcard h𝒮 hU
  by_cases hEq : ctxU t tau x₁ x₂ lam = 𝒮
  · rw [← hEq]
    exact le_of_eq (q13c_card_CU h hB)
  · haveI : Finite (Subgroup G) :=
      Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
    have hltU : ctxU t tau x₁ x₂ lam < 𝒮 := lt_of_le_of_ne hU hEq
    let s : Set (Subgroup G) := {K | ctxU t tau x₁ x₂ lam ≤ K ∧ K < 𝒮}
    have hsne : s.Nonempty := ⟨ctxU t tau x₁ x₂ lam, le_rfl, hltU⟩
    obtain ⟨𝒮₁, hS1mem, hmax⟩ := (Set.toFinite s).exists_maximal hsne
    have hS1lt : 𝒮₁ < 𝒮 := hS1mem.2
    have hcov : 𝒮₁ ⋖ 𝒮 := by
      refine ⟨hS1lt, ?_⟩
      intro K hS1K hKlt
      have hKs : K ∈ s := ⟨hS1mem.1.trans hS1K.le, hKlt⟩
      exact absurd (hmax hKs hS1K.le) (not_le_of_gt hS1K)
    have h𝒮₁ : IsPGroup 2 𝒮₁ := h𝒮.to_le hS1lt.le
    have hcardlt : Nat.card 𝒮₁ < Nat.card 𝒮 := Subgroup.card_lt_of_lt hS1lt
    have hIH : Nat.card ↥(𝒮₁ ⊓ centralizer ({t * lam} : Set G)) ≤ 2 ^ 6 :=
      ih (Nat.card 𝒮₁) (by rw [← hcard]; exact hcardlt) 𝒮₁ rfl h𝒮₁ hS1mem.1
    have hrel : 𝒮₁.relIndex 𝒮 = 2 := relIndex_eq_two_of_covBy h𝒮 hcov
    have hbound : Nat.card ↥(𝒮 ⊓ centralizer ({t * lam} : Set G)) ≤ 2 ^ 7 := by
      calc Nat.card ↥(𝒮 ⊓ centralizer ({t * lam} : Set G))
          ≤ 2 * Nat.card ↥((𝒮 ⊓ centralizer ({t * lam} : Set G)) ⊓ 𝒮₁) :=
            card_le_two_mul_card_inf inf_le_left hrel
        _ ≤ 2 * Nat.card ↥(𝒮₁ ⊓ centralizer ({t * lam} : Set G)) := by
            refine Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le ?_)
            exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
        _ ≤ 2 * 2 ^ 6 := Nat.mul_le_mul_left 2 hIH
        _ = 2 ^ 7 := by norm_num
    have hSC : IsPGroup 2 (𝒮 ⊓ centralizer ({t * lam} : Set G) : Subgroup G) :=
      h𝒮.to_le inf_le_left
    obtain ⟨m, hm⟩ := hSC.exists_card_eq
    have hle7 : 2 ^ m ≤ 2 ^ 7 := by rw [← hm]; exact hbound
    have hne7 : 2 ^ m ≠ 2 ^ 7 := by
      intro hh
      exact q13c_key h hB h𝒮 hU (by rw [hm, hh])
    have hmle : m ≤ 7 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle7
    have hmne : m ≠ 7 := fun hh => hne7 (by rw [hh])
    have hm6 : m ≤ 6 := by omega
    rw [hm]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hm6

theorem q13c_C_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau) :
    ∀ 𝒮 : Subgroup G, IsPGroup 2 𝒮 → ctxU t tau x₁ x₂ lam ≤ 𝒮 →
      𝒮 ⊓ centralizer ({t * lam} : Set G) =
        ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) := by
  intro 𝒮 h𝒮 hU
  refine (Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hU) ?_).symm
  rw [q13c_card_CU h hB]
  exact q13c_card_C_le h hB 𝒮 h𝒮 hU

theorem q13c_famC : Q13FamC := by
  intro G _ _ t L S x₁ x₂ lam rho tau om hq hA hB
  have hom_mem : om ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hA.CO_eq]
    exact Subgroup.subset_closure (by simp)
  have h : Q13Om t L S x₁ x₂ lam rho tau om :=
    { toQ13Ctx := hq
      om_mem := hom_mem
      om_sq := by rw [← pow_two]; exact hA.om_sq
      om_not_mem := hA.om_not_mem
      t_om := hA.t_om
      CO_eq := hA.CO_eq }
  exact ⟨q13c_lam_om_eq h hB, q13c_card_CU h hB, q13c_C_dih h hB, q13c_C_eq h hB⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
