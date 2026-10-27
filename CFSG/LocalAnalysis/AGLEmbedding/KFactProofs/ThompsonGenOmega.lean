module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenLine
import Mathlib.Data.Set.Finite.Lemmas

public section

namespace CFSG.AGLEmbedding.ThompsonGen

open scoped commutatorElement
open Subgroup

theorem exists_larger_normalizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) {E : Subgroup P} [E.Normal]
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEp : ∀ a ∈ E, a ^ p = 1) {x : P}
    (hxC : x ∈ centralizer (E : Set P)) (hxp : x ^ p = 1) (hxE : x ∉ E)
    (hN : normalizer ((E ⊔ zpowers x : Subgroup P) : Set P) ≠ ⊤) :
    ∃ z ∈ centralizer (E : Set P), z ^ p = 1 ∧ z ∉ E ∧
      Nat.card (normalizer ((E ⊔ zpowers x : Subgroup P) : Set P)) <
        Nat.card (normalizer ((E ⊔ zpowers z : Subgroup P) : Set P)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨F, hF⟩ : ∃ F : Subgroup P, F = E ⊔ zpowers x := ⟨_, rfl⟩
  rw [← hF] at hN ⊢
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup P, N = normalizer (F : Set P) := ⟨_, rfl⟩
  rw [← hNdef] at hN ⊢
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hNlt : N < normalizer (N : Set P) :=
    Group.normalizerCondition_of_isNilpotent N (lt_top_iff_ne_top.2 hN)
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup P, M = normalizer (N : Set P) := ⟨_, rfl⟩
  rw [← hMdef] at hNlt
  have hxF : x ∈ F := hF ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hFN : F ≤ N := hNdef ▸ Subgroup.le_normalizer
  have hxN : x ∈ N := hFN hxF
  have hNF : ∀ n ∈ N, ∀ f ∈ E ⊔ zpowers x, n * f * n⁻¹ ∈ E ⊔ zpowers x := by
    intro n hn f hf
    rw [← hF] at hf ⊢
    rw [hNdef] at hn
    exact ((Subgroup.mem_normalizer_iff.1 hn) f).1 hf
  let G₀ : Set P := (E : Set P) ∪ {q | ∃ m ∈ M, q = m * x * m⁻¹}
  have hG₀cent : G₀ ⊆ centralizer (E : Set P) := by
    rintro g (hg | ⟨m, hm, rfl⟩)
    · exact mem_centralizer_iff.2 fun e he => hEc e he g hg
    · exact conj_mem_centralizer hxC m
  have hG₀pow : ∀ g ∈ G₀, g ^ p = 1 := by
    rintro g (hg | ⟨m, hm, rfl⟩)
    · exact hEp g hg
    · rw [conj_pow, hxp]; simp
  have hG₀comm : ∀ g₁ ∈ G₀, ∀ g₂ ∈ G₀, ⁅g₁, g₂⁆ ∈ E := by
    rintro g₁ (h₁ | ⟨m₁, hm₁, rfl⟩) g₂ (h₂ | ⟨m₂, hm₂, rfl⟩)
    · simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    · have : ⁅g₁, m₂ * x * m₂⁻¹⁆ = g₁ * ((m₂ * x * m₂⁻¹) * g₁⁻¹ * (m₂ * x * m₂⁻¹)⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem h₁ (Normal.conj_mem ‹E.Normal› _ (inv_mem h₁) _)
    · have : ⁅m₁ * x * m₁⁻¹, g₂⁆ = ((m₁ * x * m₁⁻¹) * g₂ * (m₁ * x * m₁⁻¹)⁻¹) * g₂⁻¹ := by
        simp only [commutatorElement_def]
      rw [this]
      exact mul_mem (Normal.conj_mem ‹E.Normal› _ h₂ _) (inv_mem h₂)
    · rw [hMdef] at hm₁ hm₂
      exact commutator_conj_mem hp hEc hxC hxp hxN hNF hm₁ hm₂
  have hexp := closure_pow_eq_one hp hp2 hEp hG₀cent hG₀pow hG₀comm
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup P, R = closure G₀ := ⟨_, rfl⟩
  rw [← hRdef] at hexp
  have hER : E ≤ R := fun e he => hRdef ▸ Subgroup.subset_closure (Or.inl he)
  have hxR : x ∈ R := hRdef ▸ Subgroup.subset_closure (Or.inr ⟨1, one_mem _, by simp⟩)
  have hlt : E < R := lt_of_le_of_ne hER (fun h => hxE (h ▸ hxR))
  have hRcent : R ≤ centralizer (E : Set P) := hRdef ▸ (Subgroup.closure_le _).2 hG₀cent
  have hMR : M ≤ normalizer (R : Set P) := by
    rw [hRdef, Subgroup.le_normalizer_closure_iff]
    intro m hm g hg
    rcases hg with hg | ⟨m', hm', rfl⟩
    · exact Subgroup.subset_closure (Or.inl (Normal.conj_mem ‹E.Normal› g hg m))
    · exact Subgroup.subset_closure (Or.inr ⟨m * m', mul_mem hm hm', by group⟩)
  obtain ⟨z, hzR, hzE, hzcomm⟩ := exists_mem_relative_center hP hlt
  refine ⟨z, hRcent hzR, hexp z hzR, hzE, ?_⟩
  have hMz : M ≤ normalizer ((E ⊔ zpowers z : Subgroup P) : Set P) := by
    rw [Subgroup.le_normalizer_iff]
    intro m hm k hk
    apply conj_mem_sup_zpowers m _ k hk
    have hc : ⁅m, z⁆ ∈ E := hzcomm m (hMR hm)
    have : m * z * m⁻¹ = ⁅m, z⁆ * z := by simp only [commutatorElement_def]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  calc Nat.card N < Nat.card M := Subgroup.card_lt_of_lt hNlt
    _ ≤ Nat.card (normalizer ((E ⊔ zpowers z : Subgroup P) : Set P)) :=
      Subgroup.card_le_of_le hMz

theorem mem_of_pow_eq_one_of_mem_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup p P) {E : Subgroup P} [E.Normal]
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEp : ∀ a ∈ E, a ^ p = 1)
    (hmax : ∀ F : Subgroup P, F.Normal → (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) →
      (∀ a ∈ F, a ^ p = 1) → E ≤ F → F ≤ E)
    {x : P} (hxC : x ∈ centralizer (E : Set P)) (hxp : x ^ p = 1) : x ∈ E := by
  by_contra hxE
  let X : Set P := {z | z ∈ centralizer (E : Set P) ∧ z ^ p = 1 ∧ z ∉ E}
  obtain ⟨z₀, ⟨hz₀C, hz₀p, hz₀E⟩, hmaxz⟩ := Set.exists_max_image X
    (fun z => Nat.card (normalizer ((E ⊔ zpowers z : Subgroup P) : Set P))) (Set.toFinite X)
    ⟨x, hxC, hxp, hxE⟩
  by_cases hN : normalizer ((E ⊔ zpowers z₀ : Subgroup P) : Set P) = ⊤
  · have hnorm : (E ⊔ zpowers z₀).Normal := Subgroup.normalizer_eq_top_iff.1 hN
    have hF := hmax (E ⊔ zpowers z₀) hnorm (line_mul_comm hEc hz₀C)
      (line_pow_eq_one hEp hz₀C hz₀p) le_sup_left
    exact hz₀E (hF (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀)))
  · obtain ⟨z, hzC, hzp, hzE, hlt⟩ := exists_larger_normalizer hp2 hP hEc hEp hz₀C hz₀p hz₀E hN
    exact absurd (hmaxz z ⟨hzC, hzp, hzE⟩) (not_le.2 hlt)

end CFSG.AGLEmbedding.ThompsonGen
