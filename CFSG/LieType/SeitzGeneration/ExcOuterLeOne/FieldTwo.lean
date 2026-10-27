module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.F2Core
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.F2Entry
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Generic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.IrrationalRootF4
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.QBorel

open CFSG.LieType.SeitzGeneration
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



theorem subfieldMaximal_of_card_two {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hσ : orderOf σ = p) (hpK : p ≠ ringChar K)
    (hk : Nat.card (fixSubfield σ) = 2)
    (M : Subgroup ↥(adjointGroup τ K)) (hRM : subfieldGroup τ σ ≤ M) :
    M = subfieldGroup τ σ ∨ M = ⊤ := by
  by_cases hM : M = subfieldGroup τ σ
  · exact Or.inl hM
  right
  obtain ⟨g, hgM, hgR⟩ : ∃ g ∈ M, g ∉ subfieldGroup τ σ := by
    by_contra h
    push Not at h
    exact hM (le_antisymm (fun g hg => h g hg) hRM)
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hθ := hiRoot_isMax hτ
  have hKcard : Nat.card K = Nat.card (fixSubfield σ) ^ p :=
    (CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ).trans (by rw [hσ])
  have h2 : (2 : K) = 0 := by
    have h11 : (1 : K) + 1 ∈ fixSubfield σ := (fixSubfield σ).add_mem (fixSubfield σ).one_mem
      (fixSubfield σ).one_mem
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
  have hR : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily τ) γ c ∈ M :=
    fun γ _ c hc => hRM (xPar_mem_subfieldGroup τ σ γ hc)
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry_f2 hτ' σ hk hK3 hθ g hgR
  have hg'M : r * g * r' ∈ M := M.mul_mem (M.mul_mem (hRM hr) hgM) (hRM hr')
  have hne0 : entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ≠ 0 := fun h =>
    hbad (h ▸ (fixSubfield σ).zero_mem)
  obtain ⟨q, hq, ε, hε, hconj⟩ := bigCell_conj_Q hτ (r * g * r') hne0
  have hy : q * xPar (rootOperatorFamily τ) (-hiRoot τ)
      ((ε : K) * entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1)) * q⁻¹ ∈ M := by
    have h := hconj 1
    rw [mul_one] at h
    rw [← h]
    exact M.mul_mem (M.mul_mem hg'M (hRM (xPar_mem_subfieldGroup τ σ (hiRoot τ)
      (fixSubfield σ).one_mem))) (M.inv_mem hg'M)
  have hμ : (ε : K) * entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield σ := by
    intro hm
    apply hbad
    rcases hε with rfl | rfl
    · simpa using hm
    · simpa using (fixSubfield σ).neg_mem hm
  obtain ⟨s, hs, hsM⟩ := core_f2 hτ (k := fixSubfield σ) hk hp hp2 hKcard M hR hq hμ hy
  have hmax : ∀ F : Subfield K, fixSubfield σ ≤ F → F = fixSubfield σ ∨ F = ⊤ :=
    fun F hF => subfield_eq_or_top σ hp hσ F hF
  rcases hτ with rfl | rfl | rfl | rfl
  · refine eq_top_of_irrational_longRootElt (fixSubfield σ) hmax M hR (hiRoot .F4) ?_ s hs hsM
    exact ⟨hθ.1, (CFSG.LieType.Ree.ReeTag.lengthParam_eq_prime_iff
      (t := CFSG.LieType.Ree.ReeTag.F4) (α := hiRoot .F4)).2 (hθ.rootNorm_F4.trans (by decide))⟩
  · exact eq_top_of_irrational_rootElt (Or.inl rfl) (fixSubfield σ) hmax M hR (hiRoot .E6) hθ.1 s hs hsM
  · exact eq_top_of_irrational_rootElt (Or.inr (Or.inl rfl)) (fixSubfield σ) hmax M hR (hiRoot .E7)
      hθ.1 s hs hsM
  · exact eq_top_of_irrational_rootElt (Or.inr (Or.inr rfl)) (fixSubfield σ) hmax M hR (hiRoot .E8)
      hθ.1 s hs hsM

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
