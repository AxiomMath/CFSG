module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module

section Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_inf_eq_one_of_ne {L M : Submodule K V} (hL : finrank K L = 2)
    (hM : finrank K M = 2) (hne : L ≠ M) (hmeet : L ⊓ M ≠ ⊥) : finrank K ↥(L ⊓ M) = 1 := by
  have h1 : 1 ≤ finrank K ↥(L ⊓ M) := Submodule.one_le_finrank_iff.mpr hmeet
  have h2 := Submodule.finrank_mono (inf_le_left : L ⊓ M ≤ L)
  by_contra h3
  apply hne
  have e1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : L ⊓ M ≤ L) (by omega)
  have e2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : L ⊓ M ≤ M) (by omega)
  rw [← e1, e2]

theorem eq_of_finrank_sup_le_one {A B : Submodule K V} (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (h : finrank K ↥(A ⊔ B) ≤ 1) : A = B := by
  have hA1 : 1 ≤ finrank K A := Submodule.one_le_finrank_iff.mpr hA
  have hB1 : 1 ≤ finrank K B := Submodule.one_le_finrank_iff.mpr hB
  have e1 := Submodule.eq_of_le_of_finrank_le (le_sup_left : A ≤ A ⊔ B) (by omega)
  have e2 := Submodule.eq_of_le_of_finrank_le (le_sup_right : B ≤ A ⊔ B) (by omega)
  exact e1.trans e2.symm

theorem le_sup_of_meet_of_not_le {L L₁ L₂ : Submodule K V} (hL : finrank K L = 2)
    (hL₁ : finrank K L₁ = 2) (hL₂ : finrank K L₂ = 2) (hne : L₁ ≠ L₂) (h₁₂ : L₁ ⊓ L₂ ≠ ⊥)
    (h₁ : L ⊓ L₁ ≠ ⊥) (h₂ : L ⊓ L₂ ≠ ⊥) (hnot : ¬ L₁ ⊓ L₂ ≤ L) : L ≤ L₁ ⊔ L₂ := by
  have hle : (L ⊓ L₁) ⊔ (L ⊓ L₂) ≤ L := sup_le inf_le_left inf_le_left
  by_cases h2 : 2 ≤ finrank K ↥((L ⊓ L₁) ⊔ (L ⊓ L₂))
  · have e := Submodule.eq_of_le_of_finrank_le hle (by omega)
    rw [← e]
    exact sup_le_sup inf_le_right inf_le_right
  · exfalso
    have e := eq_of_finrank_sup_le_one h₁ h₂ (by omega)
    have hpt : L ⊓ L₁ ≤ L₁ ⊓ L₂ := le_inf inf_le_right (e ▸ inf_le_right)
    have h1 := finrank_inf_eq_one_of_ne hL₁ hL₂ hne h₁₂
    have hA1 : 1 ≤ finrank K ↥(L ⊓ L₁) := Submodule.one_le_finrank_iff.mpr h₁
    have e' := Submodule.eq_of_le_of_finrank_le hpt (by omega)
    exact hnot (e' ▸ inf_le_left)

theorem le_sup_of_le_of_meet {L L₃ p : Submodule K V} (hL : finrank K L = 2)
    (hp : finrank K p = 1) (hpL : p ≤ L) (h₃ : L ⊓ L₃ ≠ ⊥) (hnot : ¬ p ≤ L₃) :
    L ≤ p ⊔ L₃ := by
  have hle : p ⊔ (L ⊓ L₃) ≤ L := sup_le hpL inf_le_left
  by_cases h2 : 2 ≤ finrank K ↥(p ⊔ (L ⊓ L₃))
  · have e := Submodule.eq_of_le_of_finrank_le hle (by omega)
    rw [← e]
    exact sup_le_sup le_rfl inf_le_right
  · exfalso
    have hp0 : p ≠ ⊥ := fun h => by rw [h, finrank_bot] at hp; exact zero_ne_one hp
    have e := eq_of_finrank_sup_le_one hp0 h₃ (by omega)
    exact hnot (e ▸ inf_le_right)

theorem concurrent_or_coplanar {𝓛 : Set (Submodule K V)} (h2 : ∀ L ∈ 𝓛, finrank K L = 2)
    (hmeet : ∀ L ∈ 𝓛, ∀ M ∈ 𝓛, L ⊓ M ≠ ⊥) :
    (∃ P : V, P ≠ 0 ∧ ∀ L ∈ 𝓛, P ∈ L) ∨
      ∃ W : Submodule K V, finrank K W ≤ 3 ∧ ∀ L ∈ 𝓛, L ≤ W := by
  by_cases hconc : ∃ P : V, P ≠ 0 ∧ ∀ L ∈ 𝓛, P ∈ L
  · exact Or.inl hconc
  right
  push Not at hconc
  rcases 𝓛.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · exact ⟨⊥, by rw [finrank_bot]; omega, by simp [h0]⟩
  have hL₁0 : L₁ ≠ ⊥ := fun h => by have := h2 L₁ hL₁; rw [h, finrank_bot] at this; omega
  obtain ⟨P₁, hP₁L₁, hP₁0⟩ := (Submodule.ne_bot_iff _).mp hL₁0
  obtain ⟨L₂, hL₂, hP₁L₂⟩ := hconc P₁ hP₁0
  have hne : L₁ ≠ L₂ := fun h => hP₁L₂ (h ▸ hP₁L₁)
  have h₁₂ := hmeet L₁ hL₁ L₂ hL₂
  obtain ⟨P₀, hP₀, hP₀0⟩ := (Submodule.ne_bot_iff _).mp h₁₂
  obtain ⟨L₃, hL₃, hP₀L₃⟩ := hconc P₀ hP₀0
  have hnot₃ : ¬ L₁ ⊓ L₂ ≤ L₃ := fun h => hP₀L₃ (h hP₀)
  have hmiss : ∀ L ∈ 𝓛, ¬ L₁ ⊓ L₂ ≤ L → L ≤ L₁ ⊔ L₂ := fun L hL hnot =>
    le_sup_of_meet_of_not_le (h2 L hL) (h2 L₁ hL₁) (h2 L₂ hL₂) hne h₁₂ (hmeet L hL L₁ hL₁)
      (hmeet L hL L₂ hL₂) hnot
  have hL₃le := hmiss L₃ hL₃ hnot₃
  have hpt := finrank_inf_eq_one_of_ne (h2 L₁ hL₁) (h2 L₂ hL₂) hne h₁₂
  refine ⟨L₁ ⊔ L₂, ?_, fun L hL => ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq L₁ L₂
    rw [h2 L₁ hL₁, h2 L₂ hL₂, hpt] at h
    omega
  · by_cases hpL : L₁ ⊓ L₂ ≤ L
    · refine (le_sup_of_le_of_meet (h2 L hL) hpt hpL (hmeet L hL L₃ hL₃) hnot₃).trans ?_
      exact sup_le (inf_le_left.trans le_sup_left) hL₃le
    · exact hmiss L hL hpL

end Field

section ZModTwo

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem eq_of_mem_inf_of_ne {L M : Submodule (ZMod 2) V} (hL : finrank (ZMod 2) L = 2)
    (hM : finrank (ZMod 2) M = 2) (hne : L ≠ M) {P P' : V} (hP : P ∈ L ⊓ M) (hP' : P' ∈ L ⊓ M)
    (hP0 : P ≠ 0) (hP'0 : P' ≠ 0) : P = P' := by
  have h1 := finrank_inf_eq_one_of_ne hL hM hne ((Submodule.ne_bot_iff _).mpr ⟨P, hP, hP0⟩)
  have hle : (ZMod 2) ∙ P ≤ L ⊓ M := (Submodule.span_singleton_le_iff_mem P _).mpr hP
  have e := Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hP0, h1])
  rw [← e] at hP'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hP'
  have hc' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc' c with rfl | rfl
  · rw [zero_smul] at hc
    exact absurd hc.symm hP'0
  · rw [one_smul] at hc
    exact hc

theorem ncard_le_seven_of_forall_le {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W ≤ 3)
    {𝓛 : Set (Submodule (ZMod 2) V)} (h𝓛 : ∀ L ∈ 𝓛, L ≤ W ∧ finrank (ZMod 2) L = 2) :
    𝓛.ncard ≤ 7 := by
  classical
  rcases Nat.lt_or_ge (finrank (ZMod 2) W) 3 with hlt | h3
  ·
    have hsub : 𝓛 ⊆ {W} := fun L hL =>
      Submodule.eq_of_le_of_finrank_le (h𝓛 L hL).1 (by have := (h𝓛 L hL).2; omega)
    exact (Set.ncard_le_ncard hsub (Set.finite_singleton W)).trans
      (by rw [Set.ncard_singleton]; omega)
  have hW3 : finrank (ZMod 2) W = 3 := by omega
  let f : Submodule (ZMod 2) V → Module.Dual (ZMod 2) W := fun L =>
    if h : L.comap W.subtype < ⊤ then (Submodule.exists_le_ker_of_lt_top _ h).choose else 0
  have hcomap : ∀ L, L ≤ W → finrank (ZMod 2) L = 2 →
      finrank (ZMod 2) (L.comap W.subtype) = 2 := by
    intro L hLW hL2
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_eq_right.mpr hLW,
      hL2]
  have hlt : ∀ L, L ≤ W → finrank (ZMod 2) L = 2 → L.comap W.subtype < ⊤ := by
    intro L hLW hL2
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have := hcomap L hLW hL2
    rw [h, finrank_top, hW3] at this
    omega
  have hf : ∀ L, L ≤ W → finrank (ZMod 2) L = 2 →
      f L ≠ 0 ∧ L.comap W.subtype ≤ LinearMap.ker (f L) := by
    intro L hLW hL2
    have h := hlt L hLW hL2
    simp only [f, h, ↓reduceDIte]
    exact (Submodule.exists_le_ker_of_lt_top _ h).choose_spec
  have hker : ∀ L, L ≤ W → finrank (ZMod 2) L = 2 →
      L.comap W.subtype = LinearMap.ker (f L) := by
    intro L hLW hL2
    obtain ⟨hf0, hle⟩ := hf L hLW hL2
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have hrank := LinearMap.finrank_range_add_finrank_ker (f L)
    have hr1 : 1 ≤ finrank (ZMod 2) (LinearMap.range (f L)) :=
      Submodule.one_le_finrank_iff.mpr (fun h => hf0 (LinearMap.range_eq_bot.mp h))
    rw [hW3] at hrank
    rw [hcomap L hLW hL2]
    omega
  have hmaps : ∀ L ∈ 𝓛, f L ∈ {φ : Module.Dual (ZMod 2) W | φ ≠ 0} := fun L hL =>
    (hf L (h𝓛 L hL).1 (h𝓛 L hL).2).1
  have hinj : Set.InjOn f 𝓛 := by
    intro L hL L' hL' heq
    obtain ⟨hLW, hL2⟩ := h𝓛 L hL
    obtain ⟨hL'W, hL'2⟩ := h𝓛 L' hL'
    have e : L.comap W.subtype = L'.comap W.subtype := by
      rw [hker L hLW hL2, hker L' hL'W hL'2, heq]
    rw [← inf_eq_right.mpr hLW, ← inf_eq_right.mpr hL'W, ← Submodule.map_comap_subtype,
      ← Submodule.map_comap_subtype, e]
  have hfin : Finite (Module.Dual (ZMod 2) W) := Module.finite_of_finite (ZMod 2)
  refine (Set.ncard_le_ncard_of_injOn f hmaps hinj).trans ?_
  have hset : {φ : Module.Dual (ZMod 2) W | φ ≠ 0} = Set.univ \ {0} := by
    ext φ
    simp
  rw [hset, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq, hW3, Nat.card_zmod]
  norm_num

theorem concurrent_of_eight_le_ncard {𝓛 : Set (Submodule (ZMod 2) V)}
    (h2 : ∀ L ∈ 𝓛, finrank (ZMod 2) L = 2) (hmeet : ∀ L ∈ 𝓛, ∀ M ∈ 𝓛, L ⊓ M ≠ ⊥)
    (h8 : 8 ≤ 𝓛.ncard) : ∃ P : V, P ≠ 0 ∧ ∀ L ∈ 𝓛, P ∈ L := by
  rcases concurrent_or_coplanar h2 hmeet with h | ⟨W, hW, hle⟩
  · exact h
  · have := ncard_le_seven_of_forall_le hW fun L hL => ⟨hle L hL, h2 L hL⟩
    omega

end ZModTwo

end CFSG.LargeExtraspecial.A2Mod
