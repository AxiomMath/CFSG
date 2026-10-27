module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.Asc75.Basic
public import CFSG.Open.FusionDefs

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

@[expose] def genSet (A₁ A₂ : Subgroup G) : Set G :=
  {g : G | conjugate A₁ g ⊓ A₁ ≠ ⊥ ∨ conjugate A₁ g ⊓ A₂ ≠ ⊥ ∨
    conjugate A₂ g ⊓ A₁ ≠ ⊥ ∨ conjugate A₂ g ⊓ A₂ ≠ ⊥}

@[expose] def uSet (A₁ A₂ : Subgroup G) : Set G := (A₁ : Set G) ∪ (A₂ : Set G)

structure Hyp [Finite G] (S A₁ A₂ H : Subgroup G) : Prop where
  pgroup : IsPGroup 2 S
  odd_index : ¬ 2 ∣ S.index
  le₁ : A₁ ≤ S
  le₂ : A₂ ≤ S
  comm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a
  rank₁ : 1 < CFSG.Open.pRank 2 A₁
  rank₂ : 1 < CFSG.Open.pRank 2 A₂
  hdef : H = Subgroup.closure (genSet A₁ A₂)
  closed_H : ∀ a ∈ uSet A₁ A₂, ∀ h ∈ H, h⁻¹ * a * h ∈ S → h⁻¹ * a * h ∈ uSet A₁ A₂
  closed₁ : fusionStronglyClosed (uSet A₁ A₂) (S ⊓ Subgroup.normalizer (A₁ : Set G))
  closed₂ : fusionStronglyClosed (uSet A₁ A₂) (S ⊓ Subgroup.normalizer (A₂ : Set G))

section Basic

variable [Finite G] {S A₁ A₂ H : Subgroup G}

theorem four_le_card_of_one_lt_pRank {A : Subgroup G} (h : 1 < CFSG.Open.pRank 2 A) : 4 ≤ Nat.card A := by
  obtain ⟨E, hEA, -, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two A
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 A := Nat.pow_le_pow_right (by norm_num) h
  exact h4.trans (Subgroup.card_le_of_le hEA)

theorem ne_bot_of_one_lt_pRank {A : Subgroup G} (h : 1 < CFSG.Open.pRank 2 A) : A ≠ ⊥ := by
  intro hA
  have := four_le_card_of_one_lt_pRank h
  rw [hA, Subgroup.card_bot] at this
  omega

theorem Hyp.ne_bot₁ (h : Hyp S A₁ A₂ H) : A₁ ≠ ⊥ := ne_bot_of_one_lt_pRank h.rank₁

theorem Hyp.ne_bot₂ (h : Hyp S A₁ A₂ H) : A₂ ≠ ⊥ := ne_bot_of_one_lt_pRank h.rank₂

theorem Hyp.four_le₁ (h : Hyp S A₁ A₂ H) : 4 ≤ Nat.card A₁ :=
  four_le_card_of_one_lt_pRank h.rank₁

theorem Hyp.four_le₂ (h : Hyp S A₁ A₂ H) : 4 ≤ Nat.card A₂ :=
  four_le_card_of_one_lt_pRank h.rank₂

theorem Hyp.mem_of_conjugate_inf_ne_bot (h : Hyp S A₁ A₂ H) {Ai Aj : Subgroup G}
    (hi : Ai = A₁ ∨ Ai = A₂) (hj : Aj = A₁ ∨ Aj = A₂) {g : G}
    (hne : conjugate Ai g ⊓ Aj ≠ ⊥) : g ∈ H := by
  rw [h.hdef]
  refine Subgroup.subset_closure ?_
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact Or.inl hne
  · exact Or.inr (Or.inl hne)
  · exact Or.inr (Or.inr (Or.inl hne))
  · exact Or.inr (Or.inr (Or.inr hne))

theorem Hyp.mem_of_conj_mem (h : Hyp S A₁ A₂ H) {Ai Aj : Subgroup G}
    (hi : Ai = A₁ ∨ Ai = A₂) (hj : Aj = A₁ ∨ Aj = A₂) {g x : G} (hx : x ∈ Ai) (hx1 : x ≠ 1)
    (hxg : g⁻¹ * x * g ∈ Aj) : g ∈ H := by
  refine h.mem_of_conjugate_inf_ne_bot hi hj (g := g) ?_
  intro hbot
  have hmem : g⁻¹ * x * g ∈ conjugate Ai g ⊓ Aj := ⟨conj_mem_conjugate hx g, hxg⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hx1
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [hmem]; group

theorem Hyp.le_H₁ (h : Hyp S A₁ A₂ H) : A₁ ≤ H := by
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]; exact H.one_mem
  · refine h.mem_of_conj_mem (Or.inl rfl) (Or.inl rfl) ha ha1 (g := a) ?_
    have : a⁻¹ * a * a = a := by group
    rw [this]; exact ha

theorem Hyp.le_H₂ (h : Hyp S A₁ A₂ H) : A₂ ≤ H := by
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]; exact H.one_mem
  · refine h.mem_of_conj_mem (Or.inr rfl) (Or.inr rfl) ha ha1 (g := a) ?_
    have : a⁻¹ * a * a = a := by group
    rw [this]; exact ha

theorem Hyp.uSet_subset_H (h : Hyp S A₁ A₂ H) : uSet A₁ A₂ ⊆ (H : Set G) := by
  rintro x (hx | hx)
  · exact h.le_H₁ hx
  · exact h.le_H₂ hx

end Basic

end CFSG.Asc75
