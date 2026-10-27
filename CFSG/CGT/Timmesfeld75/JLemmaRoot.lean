module

public import CFSG.CGT.Timmesfeld75.Lemma26
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def Lemma26Hyp (K : Type) [Group K] (T : Subgroup K) : Prop :=
  IsWC T ∧ 2 < Nat.card T ∧ (∃ d₀ : K, classD T = {g | IsConj d₀ g}) ∧
    CFSG.Timmesfeld.IsRootInvolutionSet (classD T) ∧ Subgroup.closure (classD T) = ⊤

@[expose] def Lemma26Concl (K : Type) [Group K] (T : Subgroup K) : Prop :=
  ((∃ n m : ℕ, 2 ≤ n ∧ 1 ≤ m ∧ StatedClassicalModel (K ⧸ Subgroup.center K) .PSL n 2 m) ∨
      (∃ m : ℕ, 2 ≤ m ∧ StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 2 m) ∨
      (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedB2 0 2 s) ∨
      Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6))) ∧
    (¬ Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) →
      ∀ U₁ U₂ V₁ V₂ : Subgroup K, (∃ x : K, U₁ = conjSubgroup x T) →
        (∃ x : K, U₂ = conjSubgroup x T) → (∃ x : K, V₁ = conjSubgroup x T) →
        (∃ x : K, V₂ = conjSubgroup x T) → U₁ ≠ U₂ → V₁ ≠ V₂ →
          ∃ g : K, conjSubgroup g U₁ = V₁ ∧ conjSubgroup g U₂ = V₂)

theorem Lemma26Input.apply (h : Lemma26Input) {K : Type} [Group K] [Finite K] {T : Subgroup K}
    (hK : Lemma26Hyp K T) : Lemma26Concl K T :=
  h K T hK.1 hK.2.1 hK.2.2.1 hK.2.2.2.1 hK.2.2.2.2

section Map

variable {R K : Type*} [Group R] [Group K]

theorem classD_ne_one {T : Subgroup R} {x : R} (hx : x ∈ classD T) : x ≠ 1 := by
  obtain ⟨g, t, -, ht1, rfl⟩ := hx
  intro h
  apply ht1
  calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem map_mem_classD_map (π : R →* K) {T : Subgroup R} {x : R} (hx : x ∈ classD T)
    (h1 : π x ≠ 1) : π x ∈ classD (T.map π) := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hx
  refine ⟨π g, π t, Subgroup.mem_map_of_mem π ht, fun h => h1 ?_, by simp [map_mul, map_inv]⟩
  rw [map_mul, map_mul, map_inv, h]
  simp

theorem exists_mem_classD_of_mem_classD_map {π : R →* K} (hπ : Function.Surjective π)
    {T : Subgroup R} {y : K} (hy : y ∈ classD (T.map π)) : ∃ x ∈ classD T, π x = y := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hy
  obtain ⟨g₀, rfl⟩ := hπ g
  obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.1 ht
  exact ⟨g₀⁻¹ * t₀ * g₀, ⟨g₀, t₀, ht₀, fun h => ht1 (by rw [h, map_one]), rfl⟩, by simp⟩

theorem isRootInvolutionSet_classD_map {π : R →* K} (hπ : Function.Surjective π)
    {T : Subgroup R} (h : CFSG.Timmesfeld.IsRootInvolutionSet (classD T)) :
    CFSG.Timmesfeld.IsRootInvolutionSet (classD (T.map π)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun y hy => ?_, fun y hy z hz => ?_, fun y hy z hz h4 => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := exists_mem_classD_of_mem_classD_map hπ hy
    refine orderOf_eq_prime ?_ (classD_ne_one hy)
    have hx2 : x ^ 2 = 1 := by rw [← h1 x hx]; exact pow_orderOf_eq_one x
    rw [← map_pow, hx2, map_one]
  · obtain ⟨x, hx, rfl⟩ := exists_mem_classD_of_mem_classD_map hπ hy
    obtain ⟨w, hw, rfl⟩ := exists_mem_classD_of_mem_classD_map hπ hz
    have hdvd : orderOf (π x * π w) ∣ orderOf (x * w) := by
      rw [← map_mul]
      exact orderOf_map_dvd π _
    rcases h2 x hx w hw with h | h | h
    · rw [h] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
      · exact Or.inr (Or.inr (by rw [h']; exact odd_one))
      · exact Or.inl h'
    · rw [h] at hdvd
      have h22 : orderOf (π x * π w) ∣ 2 ^ 2 := by simpa using hdvd
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 h22 with ⟨i, hi, hi'⟩
      interval_cases i
      · exact Or.inr (Or.inr (by rw [hi']; exact odd_one))
      · exact Or.inl (by simpa using hi')
      · exact Or.inr (Or.inl (by simpa using hi'))
    · exact Or.inr (Or.inr (Odd.of_dvd_nat h hdvd))
  · obtain ⟨x, hx, rfl⟩ := exists_mem_classD_of_mem_classD_map hπ hy
    obtain ⟨w, hw, rfl⟩ := exists_mem_classD_of_mem_classD_map hπ hz
    have hdvd : orderOf (π x * π w) ∣ orderOf (x * w) := by
      rw [← map_mul]
      exact orderOf_map_dvd π _
    have h4' : orderOf (x * w) = 4 := by
      rw [h4] at hdvd
      rcases h2 x hx w hw with h | h | h
      · rw [h] at hdvd
        exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
      · exact h
      · exact absurd (Odd.of_dvd_nat h hdvd) (by decide)
    have hsq : π ((x * w) ^ 2) = (π x * π w) ^ 2 := by simp [map_pow, map_mul]
    rw [← hsq]
    refine map_mem_classD_map π (h3 x hx w hw h4') ?_
    rw [hsq]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by omega)

theorem exists_classD_eq_isConj_of_transitive {T : Subgroup K} (hT : T ≠ ⊥)
    (htrans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set K), g * x * g⁻¹ = y) :
    ∃ d₀ : K, classD T = {g | IsConj d₀ g} := by
  obtain ⟨⟨d₀, hd₀⟩, hd₁⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT
  have hd₁' : d₀ ≠ 1 := fun h => hd₁ (Subtype.ext h)
  refine ⟨d₀, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨g, t, ht, ht1, rfl⟩
    obtain ⟨n, -, hn⟩ := htrans d₀ hd₀ hd₁' t ht ht1
    exact isConj_iff.2 ⟨g⁻¹ * n, by rw [← hn]; group⟩
  · intro hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    exact ⟨c⁻¹, d₀, hd₀, hd₁', by rw [← hc]; group⟩

end Map

end CFSG.CGT.Timmesfeld75
