module

public import CFSG.CharacterTheory.Wreathed.FourPointThreePairsSupport

public noncomputable section

namespace CFSG.Wreathed.FourPointThreePairs

open scoped BigOperators Classical

theorem fourier_column_analysis {ι : Type*} (B : Finset ι) (P : ι → ℝ) (L d : ι → ℂ)
    (Pz Lz : ι → ℤ) (deg : ι → ℕ) (p₀ : ι) (hp₀ : p₀ ∈ B) (hP : ∀ χ, P χ = Pz χ)
    (hL : ∀ χ ∈ B, L χ = Lz χ) (hd : ∀ χ, d χ = deg χ)
    (hE : (B.filter (fun χ => P χ ≠ 0)).card = 4)
    (hPunit : ∀ χ ∈ B, P χ ≠ 0 → P χ = 1 ∨ P χ = -1) (hLsq : ∑ χ ∈ B, L χ * L χ = 8)
    (hpar : ∀ χ ∈ B, ∃ k : ℤ, L χ = P χ + 2 * k) (hPL : ∑ χ ∈ B, (P χ : ℂ) * L χ = 0)
    (hPd : ∑ χ ∈ B, d χ * P χ = 0) (hLd : ∑ χ ∈ B, d χ * L χ = 0) (hPp : P p₀ = 1)
    (hLp : L p₀ = -1) (hdp : deg p₀ = 1) (hdeg : ∀ χ ∈ B, χ ≠ p₀ → 2 ≤ deg χ) :
    let E := B.filter (fun χ => P χ ≠ 0)
    let Eplus := E.filter (fun χ => L χ = P χ)
    let Eminus := E.filter (fun χ => L χ = -P χ)
    ∃ η ∈ B, η ∉ E ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ L η = 2 * ε ∧
      (∀ χ ∈ B, χ ∉ E → χ ≠ η → L χ = 0) ∧ (∀ χ ∈ E, L χ = 1 ∨ L χ = -1) ∧
      ∃ β ∈ E, β ≠ p₀ ∧ Eplus.card = 2 ∧ Eminus.card = 2 ∧ Eminus = {p₀, β} ∧
        d η = ‖1 + P β * d β‖ ∧ (d η = d β - 1 ∨ d η = d β + 1) ∧
        ∑ χ ∈ Eplus, P χ * d χ = -ε * d η ∧ ∑ χ ∈ Eminus, P χ * d χ = ε * d η := by
  intro E Eplus Eminus
  have hEz : B.filter (fun χ => Pz χ ≠ 0) = E :=
    Finset.filter_congr fun χ _ => by rw [hP χ, Int.cast_ne_zero]
  have hPunitz : ∀ χ ∈ B, Pz χ ≠ 0 → Pz χ = 1 ∨ Pz χ = -1 := by
    intro χ hχ hne
    have h := hPunit χ hχ (by rw [hP χ]; exact_mod_cast hne)
    rw [hP χ] at h
    rcases h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have hLsqz : ∑ χ ∈ B, Lz χ ^ 2 = 8 := by
    have h : ((∑ χ ∈ B, Lz χ ^ 2 : ℤ) : ℂ) = 8 := by
      rw [← hLsq]
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [hL χ hχ, sq]
    exact_mod_cast h
  have hparz : ∀ χ ∈ B, ∃ k : ℤ, Lz χ = Pz χ + 2 * k := by
    intro χ hχ
    obtain ⟨k, hk⟩ := hpar χ hχ
    refine ⟨k, ?_⟩
    rw [hL χ hχ, hP χ] at hk
    exact_mod_cast hk
  have hPLz : ∑ χ ∈ B, Pz χ * Lz χ = 0 := by
    have h : ((∑ χ ∈ B, Pz χ * Lz χ : ℤ) : ℂ) = 0 := by
      rw [← hPL]
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [hL χ hχ, hP χ]; push_cast; ring
    exact_mod_cast h
  have hPdz : ∑ χ ∈ B, Pz χ * (deg χ : ℤ) = 0 := by
    have h : ((∑ χ ∈ B, Pz χ * (deg χ : ℤ) : ℤ) : ℂ) = 0 := by
      rw [← hPd]
      push_cast
      exact Finset.sum_congr rfl fun χ _ => by rw [hd χ, hP χ]; push_cast; ring
    exact_mod_cast h
  have hLdz : ∑ χ ∈ B, Lz χ * (deg χ : ℤ) = 0 := by
    have h : ((∑ χ ∈ B, Lz χ * (deg χ : ℤ) : ℤ) : ℂ) = 0 := by
      rw [← hLd]
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [hd χ, hL χ hχ]; ring
    exact_mod_cast h
  have hPpz : Pz p₀ = 1 := by
    have h := hPp
    rw [hP p₀] at h
    exact_mod_cast h
  have hLpz : Lz p₀ = -1 := by
    have h := hLp
    rw [hL p₀ hp₀] at h
    exact_mod_cast h
  obtain ⟨η, hηB, hηE, ε, hε, hLη, hzero, hunit, β, hβE, hβp, hcp, hcm, hEm, hdη, hdβ, hSp,
    hSm⟩ := column_eight_analysis B Pz Lz (fun χ => (deg χ : ℤ)) p₀ hp₀ (hEz ▸ hE) hPunitz
      hLsqz hparz hPLz hPdz hLdz hPpz hLpz (by rw [hdp]; rfl)
      (fun χ hχ hne => by exact_mod_cast hdeg χ hχ hne)
  rw [hEz] at hηE hzero hunit hβE hcp hcm hEm hSp hSm
  have hplus : E.filter (fun χ => Lz χ = Pz χ) = Eplus :=
    Finset.filter_congr fun χ hχ => by
      rw [hL χ (Finset.filter_subset _ _ hχ), hP χ]
      constructor
      · intro h
        rw [h]
        push_cast
        rfl
      · intro h
        exact_mod_cast h
  have hminus : E.filter (fun χ => Lz χ = -Pz χ) = Eminus :=
    Finset.filter_congr fun χ hχ => by
      rw [hL χ (Finset.filter_subset _ _ hχ), hP χ]
      constructor
      · intro h
        rw [h]
        push_cast
        rfl
      · intro h
        exact_mod_cast h
  rw [hplus] at hcp hSp
  rw [hminus] at hcm hEm hSm
  have hcast : ∀ χ, (P χ : ℂ) * d χ = ((Pz χ * (deg χ : ℤ) : ℤ) : ℂ) := fun χ => by
    rw [hP χ, hd χ]
    push_cast
    rfl
  refine ⟨η, hηB, hηE, ε, hε, by rw [hL η hηB, hLη]; push_cast; ring, fun χ hχB hχE hχη => by
    rw [hL χ hχB, hzero χ hχB hχE hχη, Int.cast_zero], fun χ hχ => ?_, β, hβE, hβp, hcp, hcm,
    hEm, ?_, ?_, ?_, ?_⟩
  · rw [hL χ (Finset.filter_subset _ _ hχ)]
    rcases hunit χ hχ with h | h
    · left
      rw [h, Int.cast_one]
    · right
      rw [h, Int.cast_neg, Int.cast_one]
  · rw [hd η, hd β, hP β, show (1 : ℂ) + ((Pz β : ℝ) : ℂ) * (deg β : ℂ) =
      ((1 + Pz β * (deg β : ℤ) : ℤ) : ℂ) by push_cast; rfl, Complex.norm_intCast,
      ← Int.cast_abs, ← hdη]
    push_cast
    rfl
  · rw [hd η, hd β]
    rcases hdβ with h | h
    · left
      have h' : ((deg η : ℤ) : ℂ) = (((deg β : ℤ) - 1 : ℤ) : ℂ) := by rw [h]
      push_cast at h'
      exact h'
    · right
      have h' : ((deg η : ℤ) : ℂ) = (((deg β : ℤ) + 1 : ℤ) : ℂ) := by rw [h]
      push_cast at h'
      exact h'
  · rw [Finset.sum_congr rfl fun χ _ => hcast χ, ← Int.cast_sum, hSp, hd η]
    push_cast
    ring
  · rw [Finset.sum_congr rfl fun χ _ => hcast χ, ← Int.cast_sum, hSm, hd η]
    push_cast
    ring

theorem fourier_pair_alternatives {ι : Type*} (B E : Finset ι) (L₁ L₃ : ι → ℂ) (χ₁ ψ₁ : ι)
    (hD1 : L₁ χ₁ - L₃ χ₁ = -2) (hD2 : L₁ ψ₁ - L₃ ψ₁ = 2)
    (hD0 : ∀ χ ∈ B, χ ≠ χ₁ → χ ≠ ψ₁ → L₁ χ = L₃ χ) (hχ₁ : χ₁ ∈ B) (hψ₁ : ψ₁ ∈ B)
    (hEB : E ⊆ B) (η₁ η₃ : ι) (ε₁ ε₃ : ℤ) (hη₁B : η₁ ∈ B) (hη₃B : η₃ ∈ B) (hη₁E : η₁ ∉ E)
    (hη₃E : η₃ ∉ E) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε : ε₃ = ε₁) (hL₁η : L₁ η₁ = 2 * ε₁)
    (hL₃η : L₃ η₃ = 2 * ε₃) (hz₁ : ∀ χ ∈ B, χ ∉ E → χ ≠ η₁ → L₁ χ = 0)
    (hz₃ : ∀ χ ∈ B, χ ∉ E → χ ≠ η₃ → L₃ χ = 0) :
    (η₁ ≠ η₃ → ({χ₁, ψ₁} : Finset ι) = {η₁, η₃} ∧ ∀ χ ∈ E, L₁ χ = L₃ χ) ∧
      (η₁ = η₃ → χ₁ ∈ E ∧ ψ₁ ∈ E) := by
  have hε0 : (2 * ε₁ : ℂ) ≠ 0 := by
    rcases hε₁ with rfl | rfl <;> norm_num
  have hχψ : χ₁ ≠ ψ₁ := by
    rintro rfl
    rw [hD1] at hD2
    norm_num at hD2
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have h1 : η₁ = χ₁ ∨ η₁ = ψ₁ := by
      by_contra h
      rw [not_or] at h
      have h' := hD0 η₁ hη₁B h.1 h.2
      rw [hL₁η, hz₃ η₁ hη₁B hη₁E hne] at h'
      exact hε0 h'
    have h3 : η₃ = χ₁ ∨ η₃ = ψ₁ := by
      by_contra h
      rw [not_or] at h
      have h' := hD0 η₃ hη₃B h.1 h.2
      rw [hL₃η, hz₁ η₃ hη₃B hη₃E (Ne.symm hne), hε] at h'
      exact hε0 h'.symm
    have hpair : ({χ₁, ψ₁} : Finset ι) = {η₁, η₃} := by
      rcases h1 with rfl | rfl <;> rcases h3 with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact Finset.pair_comm _ _
      · exact absurd rfl hne
    refine ⟨hpair, fun χ hχ => hD0 χ (hEB hχ) ?_ ?_⟩
    · rintro rfl
      have hmem : χ ∈ ({η₁, η₃} : Finset ι) := hpair ▸ Finset.mem_insert_self χ {ψ₁}
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hη₁E (h ▸ hχ)
      · exact hη₃E ((Finset.mem_singleton.mp h) ▸ hχ)
    · rintro rfl
      have hmem : χ ∈ ({η₁, η₃} : Finset ι) :=
        hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self χ)
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hη₁E (h ▸ hχ)
      · exact hη₃E ((Finset.mem_singleton.mp h) ▸ hχ)
  · subst heq
    have hkey : ∀ χ ∈ B, χ ∉ E → L₁ χ = L₃ χ := by
      intro χ hχB hχE
      by_cases hχη : χ = η₁
      · rw [hχη, hL₁η, hL₃η, hε]
      · rw [hz₁ χ hχB hχE hχη, hz₃ χ hχB hχE hχη]
    refine ⟨?_, ?_⟩
    · by_contra h
      rw [hkey χ₁ hχ₁ h, sub_self] at hD1
      norm_num at hD1
    · by_contra h
      rw [hkey ψ₁ hψ₁ h, sub_self] at hD2
      norm_num at hD2

end CFSG.Wreathed.FourPointThreePairs
