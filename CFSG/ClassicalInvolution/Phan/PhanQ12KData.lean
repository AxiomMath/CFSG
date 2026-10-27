module

public import CFSG.ClassicalInvolution.Phan.PhanQ9KGeo

public section

namespace CFSG.ClassicalInvolution.PhanQ

section Exists

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [Finite K]

theorem exists_kdata (p e : ℕ) [Fact p.Prime] [CharP K p] (hF : Nat.card F = p ^ e)
    (hK : Nat.card K = (p ^ e) ^ 2) (hp2 : p ≠ 2) {ε : F} (hε : ε ≠ 0)
    (hnsq : ¬ IsSquare (-ε)) : Nonempty (KData F K ε) := by
  classical
  have := Fintype.ofFinite F
  have := Fintype.ofFinite K
  have : ExpChar K p := ExpChar.prime Fact.out
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hpowF : ∀ a : F, a ^ Nat.card F = a := fun a => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  have hpowK : ∀ x : K, x ^ Nat.card K = x := fun x => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  let τ : K →+* K := iterateFrobenius K p e
  have hτpow : ∀ x : K, τ x = x ^ Nat.card F := fun x => by
    simp only [τ, iterateFrobenius_def, hF]
  have hK' : Nat.card K = Nat.card F ^ 2 := by rw [hK, hF]
  have htt : ∀ x : K, τ (τ x) = x := fun x => by
    rw [hτpow, hτpow, ← pow_mul, ← sq, ← hK']
    exact hpowK x
  have htalg : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a := fun a => by
    rw [hτpow, ← map_pow, hpowF]
  have hfixed : ∀ x : K, τ x = x → ∃ a : F, algebraMap F K a = x := by
    intro x hx
    set P : Polynomial K := Polynomial.X ^ Nat.card F - Polynomial.X with hP
    have hdeg : P.natDegree = Nat.card F := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
    have hP0 : P ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hdeg
      omega
    have hsub : Finset.univ.image (algebraMap F K) ⊆ P.roots.toFinset := by
      intro y hy
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← map_pow, hpowF, sub_self]
    have hcard : P.roots.toFinset.card ≤ (Finset.univ.image (algebraMap F K)).card := by
      rw [Finset.card_image_of_injective _ (algebraMap F K).injective, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
      calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ = Nat.card F := hdeg
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hx' : x ∈ P.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← hτpow, hx, sub_self]
    rw [← heq] at hx'
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx'
    exact ⟨a, ha⟩
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.Prime.eq_two_or_odd' Fact.out).resolve_left hp2 |>.pow
  have hsq : ∃ θ : K, θ ^ 2 = algebraMap F K (-(1 / ε)) := by
    have hne : algebraMap F K (-(1 / ε)) ≠ 0 := by
      intro h
      have h' := (map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).1 h
      exact one_div_ne_zero hε (by linear_combination -h')
    have hchar : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      exact hp2
    obtain ⟨k, hk⟩ := hodd
    have hc : (-(1 / ε)) ≠ 0 := fun h => hne (by rw [h, map_zero])
    have h1 : (-(1 / ε)) ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hc
    have hcardF : Fintype.card F = 2 * k + 1 := by rw [← Nat.card_eq_fintype_card]; exact hk
    have hcardK : Fintype.card K = (2 * k + 1) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hK, ← hF, hk]
    have hexp : Fintype.card K / 2 = (Fintype.card F - 1) * (k + 1) := by
      rw [hcardK, hcardF]
      have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
      rw [this]
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this]
      omega
    obtain ⟨θ, hθ⟩ := (FiniteField.isSquare_iff hchar hne).2 (by
      rw [hexp, pow_mul, ← map_pow, h1, map_one, one_pow])
    exact ⟨θ, by rw [sq]; exact hθ.symm⟩
  obtain ⟨θ, hθ2⟩ := hsq
  have hτθ : τ θ = -θ := by
    have h1 : (τ θ) ^ 2 = θ ^ 2 := by
      rw [← map_pow, hθ2, htalg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exfalso
      obtain ⟨a, ha⟩ := hfixed θ h
      apply hnsq
      refine ⟨a * ε, ?_⟩
      apply (algebraMap F K).injective
      rw [map_neg, map_mul, map_mul, ha]
      have : algebraMap F K ε * (θ ^ 2) = -1 := by
        rw [hθ2, ← map_mul]
        have : ε * (-(1 / ε)) = -1 := by field_simp
        rw [this, map_neg, map_one]
      linear_combination (-(algebraMap F K ε)) * this
    · exact h
  exact ⟨{
    τ := τ
    tau_alg := htalg
    tau_tau := htt
    tau_pow := hτpow
    card_K := hK'
    fixed := hfixed
    θ := θ
    theta_sq := hθ2
    tau_theta := hτθ }⟩

end Exists

end CFSG.ClassicalInvolution.PhanQ
