module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.AGLEmbedding.LieOut

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem not_exists_pow_five_eq (h : UnitaryFieldData 2 2 K) {c : K} (hc5 : c ^ 5 = 1)
    (hc1 : c ≠ 1) : ∀ b : K, b ^ 5 ≠ c := by
  have := h.finite
  have := Fintype.ofFinite K
  intro b hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
    rw [← hb] at hc5
    norm_num at hc5
  have h15 : b ^ 15 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one b hb0
    rwa [Fintype.card_eq_nat_card, h.card] at this
  have hc3 : c ^ 3 = 1 := by rw [← hb, ← pow_mul]; exact h15
  apply hc1
  calc c = c * c ^ 5 := by rw [hc5, mul_one]
    _ = (c ^ 3) ^ 2 := by ring
    _ = 1 := by rw [hc3]; norm_num

theorem irreducible_X_pow_five_sub (h : UnitaryFieldData 2 2 K) {c : K} (hc5 : c ^ 5 = 1)
    (hc1 : c ≠ 1) : Irreducible (X ^ 5 - C c : K[X]) :=
  X_pow_sub_C_irreducible_of_prime (by norm_num) (not_exists_pow_five_eq h hc5 hc1)

theorem card_adjoinRoot (h : UnitaryFieldData 2 2 K) {c : K}
    (hirr : Irreducible (X ^ 5 - C c : K[X])) :
    Nat.card (AdjoinRoot (X ^ 5 - C c : K[X])) = 16 ^ 5 := by
  have := h.finite
  have hfd : Module.Finite K (AdjoinRoot (X ^ 5 - C c : K[X])) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  rw [Module.natCard_eq_pow_finrank (K := K), h.card]
  have : Module.finrank K (AdjoinRoot (X ^ 5 - C c : K[X])) = 5 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank]
    simp
  rw [this]
  norm_num

theorem exists_adjoinRoot_hom {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {c : K}
    (hAc : A ^ 5 = c • (1 : Matrix (Fin n) (Fin n) K)) :
    ∃ Φ : AdjoinRoot (X ^ 5 - C c : K[X]) →ₐ[K] Matrix (Fin n) (Fin n) K,
      Φ (AdjoinRoot.root _) = A := by
  let ev : K[X] →ₐ[K] Matrix (Fin n) (Fin n) K := Polynomial.aeval A
  have hev : ∀ g : K[X], g ∈ (Ideal.span {X ^ 5 - C c} : Ideal K[X]) → ev g = 0 := by
    intro g hg
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.1 hg
    simp [ev, hAc, Algebra.algebraMap_eq_smul_one]
  refine ⟨Ideal.Quotient.liftₐ _ ev hev, ?_⟩
  have := AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp (R₁ := K) (Ideal.span {X ^ 5 - C c}) ev hev) X
  exact this.trans (by simp [ev])

theorem pow_two_pow_ten (h : UnitaryFieldData 2 2 K) (r : K) : r ^ 2 ^ 10 = h.bar r := by
  have := h.finite
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 2 ^ 4 := by rw [Fintype.card_eq_nat_card, h.card]
  have h16 : r ^ 2 ^ 4 = r := by rw [← hq]; exact FiniteField.pow_card r
  rw [UnitaryFieldData.bar_apply]
  calc r ^ 2 ^ 10 = (r ^ 2 ^ 4) ^ 2 ^ 6 := by rw [← pow_mul]; norm_num
    _ = r ^ 2 ^ 6 := by rw [h16]
    _ = (r ^ 2 ^ 4) ^ 2 ^ 2 := by rw [← pow_mul]; norm_num
    _ = r ^ 2 ^ 2 := by rw [h16]

theorem adj_adjoinRoot_hom (h : UnitaryFieldData 2 2 K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hAu : adj h.bar A * A = 1) {c : K} (hc5 : c ^ 5 = 1)
    (hAc : A ^ 5 = c • (1 : Matrix (Fin n) (Fin n) K))
    (hirr : Irreducible (X ^ 5 - C c : K[X]))
    (Φ : AdjoinRoot (X ^ 5 - C c : K[X]) →ₐ[K] Matrix (Fin n) (Fin n) K)
    (hΦ : Φ (AdjoinRoot.root _) = A) (a : AdjoinRoot (X ^ 5 - C c : K[X])) :
    adj h.bar (Φ a) = Φ (a ^ 2 ^ 10) := by
  have : Fact (Irreducible (X ^ 5 - C c : K[X])) := ⟨hirr⟩
  have : CharP K 2 := h.charP
  have : CharP (AdjoinRoot (X ^ 5 - C c : K[X])) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (X ^ 5 - C c : K[X]))).injective 2
  have htop : Algebra.adjoin K {AdjoinRoot.root (X ^ 5 - C c : K[X])} = ⊤ :=
    AdjoinRoot.adjoinRoot_eq_top
  have ha : a ∈ Algebra.adjoin K {AdjoinRoot.root (X ^ 5 - C c : K[X])} := htop ▸ Algebra.mem_top
  have hA25 : A ^ 25 = 1 := by
    rw [show 25 = 5 * 5 from rfl, pow_mul, hAc, _root_.smul_pow, one_pow, hc5, one_smul]
  have hadjA : adj h.bar A = A ^ 24 := by
    calc adj h.bar A = adj h.bar A * (A * A ^ 24) := by
          rw [← pow_succ', hA25, Matrix.mul_one]
      _ = (adj h.bar A * A) * A ^ 24 := by rw [Matrix.mul_assoc]
      _ = A ^ 24 := by rw [hAu, Matrix.one_mul]
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx, hΦ, map_pow, hΦ, hadjA]
    rw [show 2 ^ 10 = 25 * 40 + 24 from rfl, pow_add, pow_mul, hA25, one_pow, one_mul]
  | algebraMap r =>
    rw [AlgHom.commutes, ← map_pow, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, adj_smul, adj_one, pow_two_pow_ten h]
  | add x y hx hy ihx ihy =>
    rw [map_add, adj_add, ihx, ihy, ← map_add, add_pow_char_pow]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, adj_mul, ihx, ihy, ← map_mul, mul_pow, mul_comm]

theorem exists_order_fortyone (h : UnitaryFieldData 2 2 K) {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) K) (hAu : adj h.bar A * A = 1) {c : K} (hc5 : c ^ 5 = 1)
    (hc1 : c ≠ 1) (hAc : A ^ 5 = c • (1 : Matrix (Fin n) (Fin n) K)) :
    ∃ u : Matrix (Fin n) (Fin n) K, adj h.bar u * u = 1 ∧ A * u = u * A ∧ u ^ 41 = 1 ∧
      u ≠ 1 := by
  have hirr := irreducible_X_pow_five_sub h hc5 hc1
  have : Fact (Irreducible (X ^ 5 - C c : K[X])) := ⟨hirr⟩
  obtain ⟨Φ, hΦ⟩ := exists_adjoinRoot_hom A hAc
  have hcardL := card_adjoinRoot h hirr
  have hfin : Finite (AdjoinRoot (X ^ 5 - C c : K[X])) :=
    Nat.finite_of_card_ne_zero (by rw [hcardL]; norm_num)
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have hdvd : 41 ∣ Nat.card (AdjoinRoot (X ^ 5 - C c : K[X]))ˣ := by
    rw [Nat.card_units, hcardL]; norm_num
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 41 hdvd
  have hk41 : (k : AdjoinRoot (X ^ 5 - C c : K[X])) ^ 41 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hk, pow_orderOf_eq_one, Units.val_one]
  have hk1 : (k : AdjoinRoot (X ^ 5 - C c : K[X])) ≠ 1 := by
    intro h1
    have : k = 1 := Units.ext h1
    rw [this, orderOf_one] at hk
    omega
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨Φ k, ?_, ?_, ?_, ?_⟩
  · rw [adj_adjoinRoot_hom h A hAu hc5 hAc hirr Φ hΦ, ← map_mul, ← pow_succ]
    have : (k : AdjoinRoot (X ^ 5 - C c : K[X])) ^ (2 ^ 10 + 1) = 1 := by
      rw [show 2 ^ 10 + 1 = 41 * 25 from rfl, pow_mul, hk41, one_pow]
    rw [this, map_one]
  · rw [← hΦ, ← map_mul, ← map_mul, mul_comm]
  · rw [← map_pow, hk41, map_one]
  · intro h1
    have : Φ k = Φ 1 := by rw [h1, map_one]
    exact hk1 (Φ.toRingHom.injective this)

end CFSG.AGLEmbedding.LieOut
