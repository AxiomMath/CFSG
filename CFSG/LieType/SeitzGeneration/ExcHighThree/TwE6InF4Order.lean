module

public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem card_twistedE6RootGroup_eq {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (twistedE6RootGroup K σ) = ordTwistedE6 (ℓ ^ f) :=
  CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 hℓ hf hK σ.toRingHom hσ

theorem card_adjointGroup_F4_eq (K : Type) [Field K] [Finite K] :
    Nat.card (adjointGroup .F4 K) = ordF4 (Nat.card K) :=
  CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4

theorem ordTwistedE6_eq_mul_ordF4 {q : ℕ} (hq : q % 3 = 1) :
    ordTwistedE6 q = q ^ 12 * (q ^ 9 + 1) * (q ^ 5 + 1) * ordF4 q := by
  have hgcd : Nat.gcd 3 (q + 1) = 1 := by
    have h3 : ¬ 3 ∣ q + 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  unfold ordTwistedE6 ordF4
  rw [hgcd, Nat.div_one]
  ring

theorem not_three_dvd_mul {q : ℕ} (hq : q % 3 = 1) :
    ¬ 3 ∣ q ^ 12 * (q ^ 9 + 1) * (q ^ 5 + 1) := by
  intro h
  have hpow : ∀ n : ℕ, q ^ n % 3 = 1 := fun n => by
    rw [Nat.pow_mod, hq]
    simp
  have hA : q ^ 12 % 3 = 1 := hpow 12
  have hB : (q ^ 9 + 1) % 3 = 2 := by
    have := hpow 9
    omega
  have hC : (q ^ 5 + 1) % 3 = 2 := by
    have := hpow 5
    omega
  have key : (q ^ 12 * (q ^ 9 + 1) * (q ^ 5 + 1)) % 3 = 1 := by
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 12), hA, hB, hC]
  have h0 := Nat.mod_eq_zero_of_dvd h
  omega

theorem factorization_three_ordTwistedE6 {q : ℕ} (hq : q % 3 = 1) (hq2 : 2 ≤ q) :
    (ordTwistedE6 q).factorization 3 = (ordF4 q).factorization 3 := by
  have hpos : ∀ n : ℕ, n ≠ 0 → 2 ≤ q ^ n := fun n hn =>
    le_trans hq2 (Nat.le_self_pow hn q)
  have hA : q ^ 12 * (q ^ 9 + 1) * (q ^ 5 + 1) ≠ 0 := by
    have h12 := hpos 12 (by norm_num)
    apply Nat.mul_ne_zero (Nat.mul_ne_zero _ _) _ <;> omega
  have hB : ordF4 q ≠ 0 := by
    unfold ordF4
    have h2 := hpos 2 (by norm_num)
    have h6 := hpos 6 (by norm_num)
    have h8 := hpos 8 (by norm_num)
    have h12 := hpos 12 (by norm_num)
    apply Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero _ _) _) _) _ <;> try omega
    exact Nat.pos_iff_ne_zero.1 (by positivity)
  rw [ordTwistedE6_eq_mul_ordF4 hq, Nat.factorization_mul hA hB, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_three_dvd_mul hq), zero_add]

end CFSG.LieType.SeitzGeneration.ExcHighThree
