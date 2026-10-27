module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Core
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2BigCell
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Entry
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldPlanes

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section Final


theorem d4F2_subfieldMaximal_of_card_two {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p) (hk : Nat.card (fixSubfield σ) = 2)
    (M : Subgroup ↥(adjointGroup Tag.D4 K)) (hRM : subfieldGroup Tag.D4 σ ≤ M) :
    M = subfieldGroup Tag.D4 σ ∨ M = ⊤ := by
  by_cases hM : M = subfieldGroup Tag.D4 σ
  · exact Or.inl hM
  right
  obtain ⟨g, hgM, hgR⟩ : ∃ g ∈ M, g ∉ subfieldGroup Tag.D4 σ := by
    by_contra h
    push Not at h
    exact hM (le_antisymm (fun g hg => h g hg) hRM)
  have hKcard : Nat.card K = Nat.card (fixSubfield σ) ^ p :=
    (CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ).trans (by rw [hσ])
  have h2 : (2 : K) = 0 := by
    have h11 : (1 : K) + 1 ∈ fixSubfield σ :=
      (fixSubfield σ).add_mem (fixSubfield σ).one_mem (fixSubfield σ).one_mem
    rcases zero_or_one_of_mem_card_two hk h11 with h | h
    · rw [one_add_one_eq_two] at h; exact h
    · exfalso
      have : (1 : K) = 0 := by
        have := congrArg (fun x => x - 1) h
        simpa using this
      exact one_ne_zero this
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKcard, hk]
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp3
  have hR : ∀ γ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily Tag.D4) γ c ∈ M :=
    fun γ _ c hc => hRM (xPar_mem_subfieldGroup Tag.D4 σ γ hc)
  obtain ⟨r, hr, r', hr', hbad⟩ := d4F2_exists_bad_entry σ hK3 d4F2_theta_isMax g hgR
  have hg'M : r * g * r' ∈ M := M.mul_mem (M.mul_mem (hRM hr) hgM) (hRM hr')
  have hne0 : entry (r * g * r') (negLabel d4F2_theta_isMax.1) (rootLabel d4F2_theta_isMax.1) ≠ 0 :=
    fun h => hbad (h ▸ (fixSubfield σ).zero_mem)
  obtain ⟨q, hq, ε, hε, hconj⟩ := d4F2_bigCell_conj_Q (r * g * r') hne0
  have hy : q * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta)
      ((ε : K) * entry (r * g * r') (negLabel d4F2_theta_isMax.1) (rootLabel d4F2_theta_isMax.1)) *
        q⁻¹ ∈ M := by
    have h := hconj 1
    rw [mul_one] at h
    rw [← h]
    exact M.mul_mem (M.mul_mem hg'M (hRM (xPar_mem_subfieldGroup Tag.D4 σ d4F2Theta
      (fixSubfield σ).one_mem))) (M.inv_mem hg'M)
  have hμ : (ε : K) * entry (r * g * r') (negLabel d4F2_theta_isMax.1) (rootLabel d4F2_theta_isMax.1) ∉
      fixSubfield σ := by
    intro hm
    apply hbad
    rcases hε with rfl | rfl
    · simpa using hm
    · simpa using (fixSubfield σ).neg_mem hm
  obtain ⟨s, hs, hsM⟩ := d4F2_core hk hp hp2 hKcard M hR hq hμ hy
  have hmax : ∀ F : Subfield K, fixSubfield σ ≤ F → F = fixSubfield σ ∨ F = ⊤ :=
    fun F hF => subfield_eq_or_top σ hp hσ F hF
  exact eq_top_of_irrational_rootElt_D4 (fixSubfield σ) hmax M hR d4F2Theta d4F2_isRoot_theta s hs hsM

theorem d4SubfieldMaximalEight_holds : D4SubfieldMaximalEight := by
  intro K _ _ hK8 σ hσ3 M hRM
  have hKcard : Nat.card K = Nat.card (fixSubfield σ) ^ 3 :=
    (CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ).trans (by rw [hσ3])
  have hk : Nat.card (fixSubfield σ) = 2 := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card (fixSubfield σ) = m := ⟨_, rfl⟩
    rw [hm] at hKcard ⊢
    rw [hK8] at hKcard
    have hm3 : m < 3 := by
      by_contra h
      push Not at h
      have : 3 ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left h 3
      omega
    interval_cases m <;> first | rfl | (norm_num at hKcard)
  exact d4F2_subfieldMaximal_of_card_two σ Nat.prime_three (by norm_num) hσ3 hk M hRM

theorem d4ThreeFieldPlanes_holds : D4ThreeFieldPlanes :=
  d4ThreeFieldPlanes_of_eight d4SubfieldMaximalEight_holds

end Final

end CFSG.LieType.SeitzGeneration.ExcWideThree
