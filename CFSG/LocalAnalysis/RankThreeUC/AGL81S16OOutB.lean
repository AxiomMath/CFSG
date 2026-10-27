module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutA

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Orthogonal

namespace OutLin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem b_ne_zero (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
  apply hirr s
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [hb, hs]
  linear_combination s * s * h2

theorem involution_scalars (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {α β γ δ : F}
    (e00 : α * α + β * γ = 1) (e11 : γ * β + δ * δ = 1)
    (h10 : α ^ 2 + b * α * γ + c * γ ^ 2 = 1) (h01 : β ^ 2 + b * β * δ + c * δ ^ 2 = c)
    (hne : ¬ (α = 1 ∧ β = 0 ∧ γ = 0)) : δ = α ∧ β = b * α + c * γ := by
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hαδ : δ = α := by
    have h1 : (α + δ) ^ 2 = 0 := by
      linear_combination e00 - e11 + (δ * α + δ * δ) * h2c
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    linear_combination this - α * h2c
  subst hαδ
  have hbg : γ * (β + b * δ + c * γ) = 0 := by
    linear_combination h10 - e00 + (β * γ) * h2c
  have hbb : β * (β + b * δ + c * γ) = 0 := by
    linear_combination h01 - c * e00 + (c * β * γ) * h2c
  have hpair : β ≠ 0 ∨ γ ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨hb0, hg0⟩ := hcon
    apply hne
    refine ⟨?_, hb0, hg0⟩
    rw [hb0, hg0] at e00
    have h1 : (δ + 1) ^ 2 = 0 := by linear_combination e00 + (δ + 1) * h2c
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    linear_combination this - h2c
  refine ⟨rfl, ?_⟩
  have h3 : β + b * δ + c * γ = 0 := by
    rcases hpair with hb' | hg'
    · exact (mul_eq_zero.mp hbb).resolve_left hb'
    · exact (mul_eq_zero.mp hbg).resolve_left hg'
  linear_combination h3 - (b * δ + c * γ) * h2c

theorem involution_shape (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {ρ : Matrix (Fin 2) (Fin 2) F}
    (hρ : ∀ p q : F, Nf b c (ρ 0 0 * p + ρ 0 1 * q) (ρ 1 0 * p + ρ 1 1 * q) = Nf b c p q)
    (h2 : ρ * ρ = 1) (hne : ρ ≠ 1) :
    ρ 1 1 = ρ 0 0 ∧ ρ 0 1 = b * ρ 0 0 + c * ρ 1 0 ∧ Nf b c (ρ 0 0) (ρ 1 0) = 1 := by
  have e00 := congrFun (congrFun h2 0) 0
  have e11 := congrFun (congrFun h2 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11
  have h10 := hρ 1 0
  have h01 := hρ 0 1
  simp only [Nf, mul_one, mul_zero, add_zero, zero_add, one_pow, zero_pow two_ne_zero] at h10 h01
  have e00' : ρ 0 0 * ρ 0 0 + ρ 0 1 * ρ 1 0 = 1 := e00
  have e11' : ρ 1 0 * ρ 0 1 + ρ 1 1 * ρ 1 1 = 1 := e11
  have hne' : ¬ (ρ 0 0 = 1 ∧ ρ 0 1 = 0 ∧ ρ 1 0 = 0) := by
    rintro ⟨ha, hb', hg⟩
    have hd : ρ 1 1 = ρ 0 0 := by
      have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
      have h1 : (ρ 0 0 + ρ 1 1) ^ 2 = 0 := by
        linear_combination e00' - e11' + (ρ 1 1 * ρ 0 0 + ρ 1 1 * ρ 1 1) * h2c
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      linear_combination this - ρ 0 0 * h2c
    apply hne
    rw [Matrix.eta_fin_two ρ, Matrix.one_fin_two, ha, hb', hg, hd, ha]
  obtain ⟨hd, hβ⟩ := involution_scalars hirr e00' e11' h10 h01 hne'
  exact ⟨hd, hβ, by simp only [Nf]; exact h10⟩

theorem commuting_involutions_eq (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {ρ ρ' : Matrix (Fin 2) (Fin 2) F}
    (hρ : ∀ p q : F, Nf b c (ρ 0 0 * p + ρ 0 1 * q) (ρ 1 0 * p + ρ 1 1 * q) = Nf b c p q)
    (hρ' : ∀ p q : F, Nf b c (ρ' 0 0 * p + ρ' 0 1 * q) (ρ' 1 0 * p + ρ' 1 1 * q) = Nf b c p q)
    (h2 : ρ * ρ = 1) (h2' : ρ' * ρ' = 1) (hc : ρ * ρ' = ρ' * ρ) :
    ρ = 1 ∨ ρ' = 1 ∨ ρ = ρ' := by
  by_cases h1 : ρ = 1
  · exact Or.inl h1
  by_cases h1' : ρ' = 1
  · exact Or.inr (Or.inl h1')
  right; right
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hb := b_ne_zero hirr
  obtain ⟨hd, hβ, hN⟩ := involution_shape hirr hρ h2 h1
  obtain ⟨hd', hβ', hN'⟩ := involution_shape hirr hρ' h2' h1'
  have hc00 := congrFun (congrFun hc 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at hc00
  simp only [Nf] at hN hN'
  have hcross : b * (ρ 0 0 * ρ' 1 0 + ρ' 0 0 * ρ 1 0) = 0 := by
    rw [hβ, hβ'] at hc00
    linear_combination hc00 + (b * ρ' 0 0 * ρ 1 0) * h2c
  have hcross' : ρ 0 0 * ρ' 1 0 + ρ' 0 0 * ρ 1 0 = 0 := (mul_eq_zero.mp hcross).resolve_left hb
  have hzero : (ρ 0 0 + ρ' 0 0) ^ 2 + b * (ρ 0 0 + ρ' 0 0) * (ρ 1 0 + ρ' 1 0) +
      c * (ρ 1 0 + ρ' 1 0) ^ 2 = 0 := by
    linear_combination hN + hN' + b * hcross' + (ρ 0 0 * ρ' 0 0 + c * ρ 1 0 * ρ' 1 0 + 1) * h2c
  obtain ⟨ha, hg⟩ := binary_eq_zero_of_irreducible hirr hzero
  have ha' : ρ' 0 0 = ρ 0 0 := by linear_combination ha - ρ 0 0 * h2c
  have hg' : ρ' 1 0 = ρ 1 0 := by linear_combination hg - ρ 1 0 * h2c
  have hβeq : ρ' 0 1 = ρ 0 1 := by rw [hβ, hβ', ha', hg']
  have hdeq : ρ' 1 1 = ρ 1 1 := by rw [hd, hd', ha']
  rw [Matrix.eta_fin_two ρ, Matrix.eta_fin_two ρ', ha', hβeq, hg', hdeq]

end OutLin

end CFSG.LocalAnalysis.RankThreeUC
