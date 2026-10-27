module

public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G]

theorem strongWC_of_normIn_eq_bot {T : Subgroup G} (hT : IsWC T)
    (h : ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) = ⊥) : StrongWC T := by
  refine ⟨hT.1, fun t ht ht1 a ha g hg => ?_⟩
  by_contra hnot
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hnot (by simp)
  set T' := conjSubgroup g⁻¹ T with hT'
  have hyT' : g⁻¹ * a * g ∈ T' := by
    have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [hT', mem_conjSubgroup, inv_inv, e]
    exact ha
  have hne : T' ≠ T := fun heq => hnot (heq ▸ hyT')
  have hy1 : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have hcomm : t ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ((Subgroup.mem_centralizer_iff.1 hg t (Set.mem_singleton t)).symm)
  have htN : t ∈ Subgroup.normalizer (T' : Set G) :=
    (hT.conj g⁻¹).centralizer_le_normalizer hyT' hy1 hcomm
  have : t ∈ normIn T T' := mem_normIn.2 ⟨ht, htN⟩
  rw [h g⁻¹ hne, Subgroup.mem_bot] at this
  exact ht1 this

theorem exists_maxPair_or_strongWC [Finite G] {T : Subgroup G} (hT : IsWC T) :
    (∃ T₁ : Subgroup G, MaxPair T T₁) ∨ StrongWC T := by
  by_cases h : ∃ g : G, conjSubgroup g T ≠ T ∧ normIn T (conjSubgroup g T) ≠ ⊥
  · left
    obtain ⟨g₁, hg₁, hL₁⟩ := h
    have hS : ({g : G | conjSubgroup g T ≠ T} : Set G).Nonempty := ⟨g₁, hg₁⟩
    obtain ⟨g₀, hg₀, hmax⟩ := Set.exists_max_image {g : G | conjSubgroup g T ≠ T}
      (fun g => Nat.card (normIn T (conjSubgroup g T))) (Set.toFinite _) hS
    refine ⟨conjSubgroup g₀ T, hT, ⟨g₀, rfl⟩, hg₀, ?_, fun g hg => hmax g hg⟩
    have h1 : 1 < Nat.card (normIn T (conjSubgroup g₁ T)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 hL₁
    have h2 := hmax g₁ hg₁
    intro hbot
    rw [hbot, Subgroup.card_bot] at h2
    omega
  · right
    push Not at h
    exact strongWC_of_normIn_eq_bot hT h

end CFSG.CGT.Timmesfeld75
