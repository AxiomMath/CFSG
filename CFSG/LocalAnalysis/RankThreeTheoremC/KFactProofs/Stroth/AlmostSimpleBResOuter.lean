module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Abstract

variable {P : Type} [Group P]

theorem false_of_outer_fixing_pair {p : ℕ} (hp : p.Prime)
    (hconj : Function.Injective (MulAut.conj : P →* MulAut P))
    {X : Type} [Group X] [Finite X] (hrk : CFSG.LieType.SeitzGeneration.RankLE2 p X)
    (ψ : X →* MulAut P) (hψ : Function.Injective ψ) (L : Subgroup X)
    (hL : ∀ y : P, ∃ l ∈ L, ψ l = MulAut.conj y)
    {x : X} (hx : x ^ p = 1) (hxout : ψ x ∉ inner P)
    {y₁ y₂ : P} (hc : Commute y₁ y₂) (h1 : y₁ ^ p = 1) (h2 : y₂ ^ p = 1)
    (hi : ∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j)
    (hfix1 : ψ x y₁ = y₁) (hfix2 : ψ x y₂ = y₂) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set a : MulAut P := ψ x with ha
  have hap : a ^ p = 1 := by rw [ha, ← map_pow, hx, map_one]
  have haI : a ∉ inner P := hxout
  obtain ⟨l₂, hl₂L, hl₂⟩ := hL y₁
  obtain ⟨l₃, hl₃L, hl₃⟩ := hL y₂
  have hfa : ∀ y : P, a y = y → a * MulAut.conj y = MulAut.conj y * a := fun y hy =>
    (apply_eq_self_iff_commute_conj_of_injective hconj a y).1 hy
  have hconjmul : MulAut.conj y₁ * MulAut.conj y₂ = MulAut.conj y₂ * MulAut.conj y₁ := by
    rw [← map_mul, ← map_mul, hc.eq]
  have hpow : ∀ u : P, u ^ p = 1 → (MulAut.conj u) ^ p = 1 := by
    intro u hu
    rw [← map_pow, hu, map_one]
  refine CFSG.LieType.SeitzGeneration.false_of_three_independent hp hrk (e₁ := x) (e₂ := l₂)
    (e₃ := l₃) ?_ ?_ ?_ hx ?_ ?_ ?_
  · refine hψ ?_
    rw [map_mul, map_mul, hl₂]
    exact hfa y₁ hfix1
  · refine hψ ?_
    rw [map_mul, map_mul, hl₃]
    exact hfa y₂ hfix2
  · refine hψ ?_
    rw [map_mul, map_mul, hl₂, hl₃]
    exact hconjmul
  · refine hψ ?_
    rw [map_pow, hl₂, map_one]
    exact hpow y₁ h1
  · refine hψ ?_
    rw [map_pow, hl₃, map_one]
    exact hpow y₂ h2
  · intro i j k hijk
    have hψ1 := congrArg ψ hijk
    rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, hl₂, hl₃, map_one] at hψ1
    have hun : (MulAut.conj y₁) ^ j * (MulAut.conj y₂) ^ k =
        MulAut.conj (y₁ ^ j * y₂ ^ k) := by
      rw [map_mul, map_zpow, map_zpow]
    have hai : a ^ i = (MulAut.conj (y₁ ^ j * y₂ ^ k))⁻¹ := by
      rw [← hun]
      exact eq_inv_of_mul_eq_one_left (by rwa [mul_assoc] at hψ1)
    have hpi : (p : ℤ) ∣ i := by
      by_contra hpi
      have hcop : IsCoprime (p : ℤ) i :=
        (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.2 hpi
      obtain ⟨u, v, huv⟩ := hcop
      have hainner : a ^ i ∈ inner P := by
        rw [hai]
        exact (inner P).inv_mem ⟨_, rfl⟩
      have : a = (a ^ i) ^ v := by
        rw [← zpow_mul, mul_comm i v]
        have h5 : v * i = 1 + (p : ℤ) * (-u) := by linarith
        rw [h5, zpow_add, zpow_one, zpow_mul, zpow_natCast, hap, one_zpow, mul_one]
      exact haI (this ▸ (inner P).zpow_mem hainner v)
    obtain ⟨c', hc'⟩ := id hpi
    have hai1 : a ^ i = 1 := by
      rw [hc', zpow_mul, zpow_natCast, hap, one_zpow]
    have hconj1 : MulAut.conj (y₁ ^ j * y₂ ^ k) = 1 := by
      rw [hai1] at hai
      exact inv_eq_one.1 hai.symm
    have hy1 : y₁ ^ j * y₂ ^ k = 1 := hconj (hconj1.trans (map_one _).symm)
    obtain ⟨hj, hk⟩ := hi j k hy1
    exact ⟨hpi, hj, hk⟩

end Abstract

section Field

theorem ringEquiv_apply_eq_of_pow_three {K : Type} [Field K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {σ : K ≃+* K} (hσ : σ ^ 3 = 1) : σ ω = ω := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hσω2 : (σ ω) ^ 2 + σ ω + 1 = 0 := by
    have := congrArg σ hω
    simpa [map_add, map_pow] using this
  have hcases : σ ω = ω ∨ σ ω = ω + 1 := by
    have h0 : (σ ω - ω) * (σ ω + ω + 1) = 0 := by linear_combination hσω2 - hω
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (by linear_combination h - (ω + 1) * h2)
  rcases hcases with h | h
  · exact h
  · exfalso
    have hσσ : σ (σ ω) = ω := by
      rw [h, map_add, map_one, h]
      linear_combination h2
    have h3 : (σ ^ 3) ω = σ (σ (σ ω)) := by
      simp [pow_succ, RingAut.mul_apply]
    rw [hσ, hσσ, h] at h3
    have : (1 : K) = 0 := by
      have h4 : ω = ω + 1 := h3
      linear_combination -h4
    exact one_ne_zero this

end Field

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
