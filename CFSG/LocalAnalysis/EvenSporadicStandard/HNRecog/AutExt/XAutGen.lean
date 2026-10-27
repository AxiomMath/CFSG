module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Subgroup CFSG.EvenSporadicStandard.HNRecog.Section3
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

private theorem commutator_le_of_gen_two_sided {C X : Subgroup Γ} {cg : Set Γ}
    (hC : C = closure cg)
    (hnorm : ∀ c ∈ cg, ∀ x ∈ X, c * x * c⁻¹ ∈ X ∧ c⁻¹ * x * c ∈ X)
    (hcomm : ∀ c ∈ cg, ∀ c' ∈ cg, ⁅c, c'⁆ ∈ X) : ⁅C, C⁆ ≤ X := by
  subst hC
  have hnormC : ∀ g ∈ closure cg, ∀ x ∈ X, g * x * g⁻¹ ∈ X ∧ g⁻¹ * x * g ∈ X := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem c hc => exact hnorm c hc
    | one => intro x hx; exact ⟨by simpa using hx, by simpa using hx⟩
    | mul a b _ _ ha hb =>
      intro x hx
      refine ⟨?_, ?_⟩
      · have e : (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
        rw [e]; exact (ha _ (hb x hx).1).1
      · have e : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
        rw [e]; exact (hb _ (ha x hx).2).2
    | inv a _ ha =>
      intro x hx
      simpa using ⟨(ha x hx).2, (ha x hx).1⟩
  have hA : ∀ c ∈ cg, ∀ g' ∈ closure cg, ⁅c, g'⁆ ∈ X := by
    intro c hc g' hg'
    induction hg' using Subgroup.closure_induction with
    | mem c' hc' => exact hcomm c hc c' hc'
    | one => simp
    | mul a b ha hb iha ihb =>
      have e : ⁅c, a * b⁆ = ⁅c, a⁆ * (a * ⁅c, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact X.mul_mem iha (hnormC a ha _ ihb).1
    | inv a ha iha =>
      have e : ⁅c, a⁻¹⁆ = a⁻¹ * ⁅c, a⁆⁻¹ * a := by
        simp only [commutatorElement_def]; group
      rw [e]
      have := (hnormC a⁻¹ (inv_mem ha) _ (X.inv_mem iha)).1
      simpa [mul_assoc] using this
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  induction hg using Subgroup.closure_induction with
  | mem c hc => exact hA c hc g' hg'
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : ⁅a * b, g'⁆ = a * ⁅b, g'⁆ * a⁻¹ * ⁅a, g'⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact X.mul_mem (hnormC a ha _ ihb).1 iha
  | inv a ha iha =>
    have e : ⁅a⁻¹, g'⁆ = a⁻¹ * ⁅a, g'⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (hnormC a⁻¹ (inv_mem ha) _ (X.inv_mem iha)).1
    simpa [mul_assoc] using this

theorem normalized_of_gen {u₁ u₂ c₁ c₂ : Γ}
    (h : ∀ u ∈ ({u₁, u₂} : Set Γ), ∀ c ∈ ({c₁, c₂} : Set Γ),
      u * c * u⁻¹ ∈ closure ({c₁, c₂} : Set Γ) ∧ u⁻¹ * c * u ∈ closure ({c₁, c₂} : Set Γ)) :
    ∀ g ∈ closure ({u₁, u₂} : Set Γ), ∀ n ∈ closure ({c₁, c₂} : Set Γ),
      g * n * g⁻¹ ∈ closure ({c₁, c₂} : Set Γ) := by
  have hgen : ∀ u ∈ ({u₁, u₂} : Set Γ), ∀ n ∈ closure ({c₁, c₂} : Set Γ),
      u * n * u⁻¹ ∈ closure ({c₁, c₂} : Set Γ) ∧
      u⁻¹ * n * u ∈ closure ({c₁, c₂} : Set Γ) := by
    intro u hu n hn
    induction hn using Subgroup.closure_induction with
    | mem c hc => exact h u hu c hc
    | one => simp
    | mul a b _ _ ha hb =>
      refine ⟨?_, ?_⟩
      · have e : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
        rw [e]; exact mul_mem ha.1 hb.1
      · have e : u⁻¹ * (a * b) * u = (u⁻¹ * a * u) * (u⁻¹ * b * u) := by group
        rw [e]; exact mul_mem ha.2 hb.2
    | inv a _ ha =>
      refine ⟨?_, ?_⟩
      · have e : u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
        rw [e]; exact inv_mem ha.1
      · have e : u⁻¹ * a⁻¹ * u = (u⁻¹ * a * u)⁻¹ := by group
        rw [e]; exact inv_mem ha.2
  have hnormC : ∀ g ∈ closure ({u₁, u₂} : Set Γ), ∀ n ∈ closure ({c₁, c₂} : Set Γ),
      g * n * g⁻¹ ∈ closure ({c₁, c₂} : Set Γ) ∧
      g⁻¹ * n * g ∈ closure ({c₁, c₂} : Set Γ) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem u hu => exact hgen u hu
    | one => intro n hn; exact ⟨by simpa using hn, by simpa using hn⟩
    | mul a b _ _ ha hb =>
      intro n hn
      refine ⟨?_, ?_⟩
      · have e : (a * b) * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        rw [e]; exact (ha _ (hb n hn).1).1
      · have e : (a * b)⁻¹ * n * (a * b) = b⁻¹ * (a⁻¹ * n * a) * b := by group
        rw [e]; exact (hb _ (ha n hn).2).2
    | inv a _ ha =>
      intro n hn
      simpa using ⟨(ha n hn).2, (ha n hn).1⟩
  intro g hg n hn
  exact (hnormC g hg n hn).1

theorem derivedOf_le_of_gen {u₁ u₂ c₁ c₂ : Γ}
    (h : ∀ u ∈ ({u₁, u₂} : Set Γ), ∀ c ∈ ({c₁, c₂} : Set Γ),
      u * c * u⁻¹ ∈ closure ({c₁, c₂} : Set Γ) ∧ u⁻¹ * c * u ∈ closure ({c₁, c₂} : Set Γ))
    (hu : u₁ * u₂ * u₁⁻¹ * u₂⁻¹ ∈ closure ({c₁, c₂} : Set Γ)) :
    derivedOf (closure ({u₁, u₂} : Set Γ)) ≤ closure ({c₁, c₂} : Set Γ) := by
  unfold derivedOf
  rw [Subgroup.map_subtype_commutator]
  have hnormX : ∀ g ∈ closure ({u₁, u₂} : Set Γ), ∀ x ∈ closure ({c₁, c₂} : Set Γ),
      g * x * g⁻¹ ∈ closure ({c₁, c₂} : Set Γ) ∧
      g⁻¹ * x * g ∈ closure ({c₁, c₂} : Set Γ) := by
    intro g hg x hx
    exact ⟨normalized_of_gen h g hg x hx, by
      have := normalized_of_gen h g⁻¹ (inv_mem hg) x hx
      simpa using this⟩
  refine commutator_le_of_gen_two_sided (C := closure ({u₁, u₂} : Set Γ))
    (X := closure ({c₁, c₂} : Set Γ)) (cg := ({u₁, u₂} : Set Γ)) rfl ?_ ?_
  · intro c hc x hx
    exact hnormX c (subset_closure hc) x hx
  · intro c hc c' hc'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc hc'
    rcases hc with hc | hc
    · rcases hc' with hc' | hc'
      · rw [hc, hc']; simp
      · rw [hc, hc']; simpa only [commutatorElement_def] using hu
    · rcases hc' with hc' | hc'
      · rw [hc, hc']
        have h21 : ⁅u₂, u₁⁆ = ⁅u₁, u₂⁆⁻¹ := by simp
        rw [h21]
        simpa only [commutatorElement_def] using inv_mem hu
      · rw [hc, hc']; simp

theorem exists_mul_of_gen {u₁ u₂ : Γ} {N C : Subgroup Γ}
    (hN : ∀ g ∈ closure ({u₁, u₂} : Set Γ), ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hC : C ≤ closure ({u₁, u₂} : Set Γ))
    (h₁ : ∃ n ∈ N, ∃ c ∈ C, u₁ = n * c) (h₂ : ∃ n ∈ N, ∃ c ∈ C, u₂ = n * c) :
    ∀ y ∈ closure ({u₁, u₂} : Set Γ), ∃ n ∈ N, ∃ c ∈ C, y = n * c := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem u hu =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact h₁
    · exact h₂
  | one => exact ⟨1, N.one_mem, 1, C.one_mem, by simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := iha
    obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := ihb
    refine ⟨n₁ * (c₁ * n₂ * c₁⁻¹), N.mul_mem hn₁ (hN c₁ (hC hc₁) n₂ hn₂),
      c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
    group
  | inv a _ iha =>
    obtain ⟨n, hn, c, hc, rfl⟩ := iha
    refine ⟨c⁻¹ * n⁻¹ * c, ?_, c⁻¹, C.inv_mem hc, ?_⟩
    · simpa only [inv_inv] using hN c⁻¹ (hC (C.inv_mem hc)) n⁻¹ (N.inv_mem hn)
    · group

end CFSG.EvenSporadicStandard.HNRecog.Section4
