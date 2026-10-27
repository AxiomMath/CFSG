module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.PartOneAux

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G]

@[expose] def kleinOf (u u' : G) : Subgroup G := zpowers u ⊔ zpowers u'

@[expose] def eightOf (u u' t : G) : Subgroup G := kleinOf u u' ⊔ zpowers t

theorem u_mem_klein (u u' : G) : u ∈ kleinOf u u' := mem_sup_left (mem_zpowers u)

theorem klein_le {L : Subgroup G} {u u' : G} (hu : u ∈ L) (hu' : u' ∈ L) : kleinOf u u' ≤ L :=
  sup_le (zpowers_le.2 hu) (zpowers_le.2 hu')

theorem u_mem_eight (u u' t : G) : u ∈ eightOf u u' t :=
  mem_sup_left (u_mem_klein u u')

theorem t_mem_eight (u u' t : G) : t ∈ eightOf u u' t := mem_sup_right (mem_zpowers t)

theorem zpowers_cases {a : G} (ha : a * a = 1) {y : G} (hy : y ∈ zpowers a) : y = 1 ∨ y = a := by
  by_cases ha1 : a = 1
  · subst ha1
    left
    simpa using hy
  · have ho : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have hk := zpow_mod_orderOf a k
    rw [ho] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [← hk]; simp [h0]
    · right; rw [← hk]; simp [h1]

theorem klein_facts {u u' : G} (hu2 : u * u = 1) (hu'2 : u' * u' = 1) (hcomm : u * u' = u' * u)
    (hne : u ≠ u') (hu1 : u ≠ 1) (hu'1 : u' ≠ 1) :
    Nat.card (kleinOf u u') = 4 ∧ ∀ x ∈ kleinOf u u', x * x = 1 := by
  have hle : zpowers u' ≤ centralizer (zpowers u : Set G) := by
    rw [zpowers_le]
    refine mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (hcomm : Commute u u') k).eq
  have ho : ∀ {x : G}, x * x = 1 → x ≠ 1 → orderOf x = 2 := fun hx hx1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hdisj : Disjoint (zpowers u) (zpowers u') := by
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    rcases zpowers_cases hu2 hx with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hx'
      rcases zpowers_cases hu'2 hx' with h2 | h2
      · exact hu1 h2
      · exact hne h2
  refine ⟨?_, sq_one_sup hle (sq_one_zpowers hu2) (sq_one_zpowers hu'2)⟩
  rw [kleinOf, card_sup_of_commute hle hdisj, Nat.card_zpowers, Nat.card_zpowers,
    ho hu2 hu1, ho hu'2 hu'1]

theorem eight_facts {L : Subgroup G} {t u u' : G} (hc : Config G L t) (hu : u ∈ L)
    (hu' : u' ∈ L) (hK : Nat.card (kleinOf u u') = 4 ∧ ∀ x ∈ kleinOf u u', x * x = 1) :
    Nat.card (eightOf u u' t) = 8 ∧ (∀ x ∈ eightOf u u' t, x * x = 1) ∧ t ∉ kleinOf u u' := by
  have hUL : kleinOf u u' ≤ L := klein_le hu hu'
  have hle : zpowers t ≤ centralizer (kleinOf u u' : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun x hx => hc.comm x (hUL hx)
  have hdisj : Disjoint (kleinOf u u') (zpowers t) := hc.disjoint.mono_left hUL
  refine ⟨?_, ?_, fun ht => hc.z_not_mem (hUL ht)⟩
  · rw [eightOf, card_sup_of_commute hle hdisj, hK.1, Nat.card_zpowers, hc.orderOf_z]
  · exact sq_one_sup hle hK.2 (sq_one_zpowers hc.z_sq)

theorem U1_facts {L₁ E : Subgroup G} {u : G} (hc₁ : Config G L₁ u) (hE8 : Nat.card E = 8)
    (huE : u ∈ E) (hEc : E ≤ centralizer ({u} : Set G)) :
    Nat.card ↥(E ⊓ L₁) = 4 ∧ u ∉ E ⊓ L₁ ∧ E = (E ⊓ L₁) ⊔ zpowers u := by
  have hEeq : E = (E ⊓ L₁) ⊔ zpowers u := by
    apply le_antisymm
    · intro e he
      rcases hc₁.mem_cases (hEc he) with h1 | ⟨l, hl, rfl⟩
      · exact mem_sup_left ⟨he, h1⟩
      · have hlE : l ∈ E := by
          have := mul_mem (E.inv_mem huE) he
          simpa using this
        exact mul_mem (mem_sup_right (mem_zpowers u)) (mem_sup_left ⟨hlE, hl⟩)
    · exact sup_le inf_le_left (zpowers_le.2 huE)
  have hle : zpowers u ≤ centralizer ((E ⊓ L₁ : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun x hx => hc₁.comm x hx.2
  have hdisj : Disjoint (E ⊓ L₁) (zpowers u) := hc₁.disjoint.mono_left inf_le_right
  refine ⟨?_, fun h => hc₁.z_not_mem h.2, hEeq⟩
  have h8 : Nat.card E = Nat.card ↥(E ⊓ L₁) * 2 := by
    conv_lhs => rw [hEeq]
    rw [card_sup_of_commute hle hdisj, Nat.card_zpowers, hc₁.orderOf_z]
  omega

end CFSG.EvenSporadicStandard.RuStd.S2
