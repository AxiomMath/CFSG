module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowD4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowNum

public section

namespace CFSG.AGLEmbedding.OuterSylow

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor lieSylowExponent LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OuterFixedOrderBound : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n ℓ f : ℕ),
    StatedLieAdmissible t n ℓ f → CFSG.Blueprint.LieModel K t n ℓ f → t ≠ .Tits →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) →
      ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) →
    ∀ α : MulAut K, α ^ p = 1 → α ∉ inner K →
      (∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator t n (ℓ ^ f₀)) ∨
      (t = .trialityD4 ∧ p = 3 ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (ℓ ^ f))

theorem one_le_lieSylowExponent {t : StatedLieTag} {n ℓ f : ℕ}
    (hadm : StatedLieAdmissible t n ℓ f) : 1 ≤ lieSylowExponent t n := by
  obtain ⟨-, -, h⟩ := hadm
  cases t <;> simp only [lieSylowExponent] at h ⊢ <;> try norm_num
  · exact Nat.div_pos (Nat.mul_le_mul (by omega : 2 ≤ n) (by omega : 1 ≤ n - 1)) (by norm_num)
  · exact Nat.div_pos (Nat.mul_le_mul (by omega : 2 ≤ n) (by omega : 1 ≤ n - 1)) (by norm_num)
  · rcases h with ⟨h, -⟩
    nlinarith
  · rcases h with ⟨h, -⟩
    nlinarith
  · exact Nat.mul_pos (by omega) (by omega)
  · exact Nat.mul_pos (by omega) (by omega)

theorem lieOrderNumerator_ne_zero {t : StatedLieTag} {n q : ℕ} (ht : t ≠ .Tits)
    (hN : 1 ≤ lieSylowExponent t n) (hq : 2 ≤ q) : lieOrderNumerator t n q ≠ 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases ht3 : t = .trialityD4
  · subst ht3
    have h6 : 1 < q ^ 6 := Nat.one_lt_pow (by norm_num) (by omega)
    have h2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    simp only [lieOrderNumerator]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)) (by omega))
      (by omega)
  · obtain ⟨k, hk⟩ := exists_stp_numerator (p := 3) ⟨1, by norm_num⟩ ht ht3 hN hq
    exact hk.1

theorem mem_inner_of_lie_model (hLie : LieOrderFormulasInput) (hb : OuterFixedOrderBound)
    {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n ℓ f : ℕ}
    (hadm : StatedLieAdmissible t n ℓ f) (hmodel : CFSG.Blueprint.LieModel K t n ℓ f)
    (ht : t ≠ .Tits) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K)
    (hdiv : ¬ p ∣ lieOrderDivisor t n (ℓ ^ f)) (hD4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3))
    {S : Subgroup K} (hS : IsPGroup p S) (hSidx : ¬ p ∣ S.index) {α : MulAut K}
    (hαp : α ^ p = 1) (hαS : ∀ s ∈ S, α s = s) : α ∈ inner K := by
  by_contra hα
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hcard, -⟩ := hLie K t n ℓ f hadm hmodel
  have hN := one_le_lieSylowExponent hadm
  have hℓ : ℓ.Prime := hadm.1
  have hf1 : 1 ≤ f := hadm.2.1
  have hq' : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hnum0 : lieOrderNumerator t n (ℓ ^ f) ≠ 0 := lieOrderNumerator_ne_zero ht hN hq'
  have hdiv0 : lieOrderDivisor t n (ℓ ^ f) ≠ 0 := fun h0 => hnum0 (by rw [← hcard, h0, mul_zero])
  have hSle : S ≤ fixedSubgroup α := fun s hs => hαS s hs
  have hSsyl : Nat.card S = p ^ (Nat.card K).factorization p :=
    (hS.toSylow hSidx).card_eq_multiplicity
  have hdvdC : p ^ (Nat.card K).factorization p ∣ Nat.card (fixedSubgroup α) := by
    rw [← hSsyl]
    exact Subgroup.card_dvd_of_le hSle
  have hnumK : (lieOrderNumerator t n (ℓ ^ f)).factorization p = (Nat.card K).factorization p := by
    rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' hdiv0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hdiv, add_zero]
  rcases hb K t n ℓ f hadm hmodel ht p hp hp2 hdiv hD4 α hαp hα with
    ⟨f₀, hf, hfix⟩ | ⟨ht4, hp3, hfix⟩
  · have hf₀ : 1 ≤ f₀ := by
      rcases Nat.eq_zero_or_pos f₀ with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    have hq : 2 ≤ ℓ ^ f₀ := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
    have hqp : (ℓ ^ f₀) ^ p = ℓ ^ f := by rw [← pow_mul, mul_comm, ← hf]
    have hne : lieOrderNumerator t n (ℓ ^ f₀) ≠ 0 := lieOrderNumerator_ne_zero ht hN hq
    have h1 : (Nat.card K).factorization p ≤ (lieOrderNumerator t n (ℓ ^ f₀)).factorization p :=
      (hp.pow_dvd_iff_le_factorization hne).1 (hdvdC.trans hfix)
    have hpnum : p ∣ lieOrderNumerator t n ((ℓ ^ f₀) ^ p) := by
      rw [hqp, ← hcard]
      exact hpK.trans (dvd_mul_right _ _)
    have h2 : (lieOrderNumerator t n (ℓ ^ f₀)).factorization p <
        (lieOrderNumerator t n ((ℓ ^ f₀) ^ p)).factorization p := by
      by_cases ht3 : t = .trialityD4
      · subst ht3
        exact numerator_trialityD4_factorization_lt hp2 hq hpnum
      · exact numerator_factorization_lt hp hp2 ht ht3 hN hq hpnum
    rw [hqp, hnumK] at h2
    omega
  · subst ht4
    subst hp3
    have hN2 : 1 ≤ lieSylowExponent .G2 0 := by simp [lieSylowExponent]
    have hG0 : lieOrderNumerator .G2 0 (ℓ ^ f) ≠ 0 :=
      lieOrderNumerator_ne_zero (by decide) hN2 hq'
    have h1 : (Nat.card K).factorization 3 ≤ (lieOrderNumerator .G2 0 (ℓ ^ f)).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hG0).1 (hdvdC.trans hfix)
    have h2 := factorization_G2_lt_trialityD4 hq'
    have hnumK' : (lieOrderNumerator .trialityD4 0 (ℓ ^ f)).factorization 3 =
        (Nat.card K).factorization 3 := hnumK
    rw [hnumK'] at h2
    omega

end CFSG.AGLEmbedding.OuterSylow
