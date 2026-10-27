module

public import CFSG.CGT.Timmesfeld75.Sec4TwoSix
public import CFSG.CGT.Timmesfeld75.Sec5OutDefs
public import CFSG.CGT.Timmesfeld75.AschbacherNoPolarDischarge

public section

namespace CFSG.CGT.Timmesfeld75

open scoped commutatorElement

@[expose] def Sec4CaseI : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    2 * Nat.card (normIn T T₁) < Nat.card T → Nat.card T ≠ 16 →
      ∀ a ∈ normD T, a ∉ T ⊔ normIn T₁ T → ¬ ∀ l ∈ normIn T₁ T, ⁅a, l⁆ ∈ T

@[expose] def Sec4CaseIII : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    Nat.card T = 2 * Nat.card (normIn T T₁) →
      ∀ a ∈ normD T, a ∉ T ⊔ normIn T₁ T → ¬ ∀ l ∈ normIn T₁ T, ⁅a, l⁆ ∈ T

theorem card_normIn_lt_card_of_maxPair {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
    (hP : MaxPair T T₁) : Nat.card (normIn T T₁) < Nat.card T := by
  obtain ⟨x, hx⟩ := hP.conj
  have hc : Cfg T T₁ := by
    subst hx
    exact Cfg.of_conj hP.wc hP.ne hP.nontriv
  exact Subgroup.card_lt_of_lt (hc.normIn_lt ⟨x, hx⟩)

theorem sec4NoA_of_cases
    (hI : Sec4CaseI) (hIII : Sec4CaseIII) : Sec4NoA := by
  intro G _ T T₁ hy hS hSI a ha haL
  have : Finite G := hy.finite
  have hlt := card_normIn_lt_card_of_maxPair hy.pair
  have hdvd : Nat.card (normIn T T₁) ∣ Nat.card T :=
    Subgroup.card_dvd_of_le (normIn_le T T₁)
  have hpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have h2 : 2 * Nat.card (normIn T T₁) ≤ Nat.card T := by
    obtain ⟨k, hk⟩ := hdvd
    rcases k with _ | _ | k
    · simp at hk
      omega
    · simp at hk
      omega
    · rw [hk]
      nlinarith
  rcases h2.eq_or_lt with h | h
  · exact hIII G T T₁ hy hS hSI h.symm a ha haL
  · by_cases h16 : Nat.card T = 16
    · intro hcomm
      obtain ⟨g, t, htT, ht1, hg⟩ := ha.1
      exact sec4_two_six aschbacherNoPolarInput_of_repo hy.pair hS hSI ha haL hcomm
        (T₂ := conjSubgroup g⁻¹ T) ⟨g⁻¹, rfl⟩
        (mem_conjSubgroup.mpr (by
          rw [inv_inv, hg]
          have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
          rw [e]
          exact htT)) h h16
    · exact hI G T T₁ hy hS hSI h h16 a ha haL

end CFSG.CGT.Timmesfeld75
