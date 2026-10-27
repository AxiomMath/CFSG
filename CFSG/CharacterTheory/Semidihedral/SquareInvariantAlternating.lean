module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.ChevalleyWarning
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public section

namespace CFSG.Semidihedral.SquareInvariantAlternating

noncomputable section

universe u v w

open Finset


section Polynomial

variable {R : Type w} [Field R] {K : Type u} [Field K] [Algebra R K]
variable {ι : Type v} [Fintype ι]

def squareMultiplierPolynomial (e : Module.Basis ι R K)
    (b : K →ₗ[R] K →ₗ[R] R) (x y : K) : MvPolynomial ι R :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    MvPolynomial.X i * (MvPolynomial.X j * (MvPolynomial.X k *
      (MvPolynomial.X l * MvPolynomial.C (b (e i * e j * x) (e k * e l * y)))))

theorem squareMultiplierPolynomial_totalDegree (e : Module.Basis ι R K)
    (b : K →ₗ[R] K →ₗ[R] R) (x y : K) :
    (squareMultiplierPolynomial e b x y).totalDegree ≤ 4 := by
  unfold squareMultiplierPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro l _
  have h1 := MvPolynomial.totalDegree_mul (MvPolynomial.X l)
    (MvPolynomial.C (b (e i * e j * x) (e k * e l * y)))
  have h2 := MvPolynomial.totalDegree_mul (MvPolynomial.X k)
    (MvPolynomial.X l * MvPolynomial.C (b (e i * e j * x) (e k * e l * y)))
  have h3 := MvPolynomial.totalDegree_mul (MvPolynomial.X j)
    (MvPolynomial.X k * (MvPolynomial.X l *
      MvPolynomial.C (b (e i * e j * x) (e k * e l * y))))
  have h4 := MvPolynomial.totalDegree_mul (MvPolynomial.X i)
    (MvPolynomial.X j * (MvPolynomial.X k * (MvPolynomial.X l *
      MvPolynomial.C (b (e i * e j * x) (e k * e l * y)))))
  simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] at h1 h2 h3 h4
  omega

theorem squareMultiplierPolynomial_eval (e : Module.Basis ι R K)
    (b : K →ₗ[R] K →ₗ[R] R) (x y : K) (a : K) :
    MvPolynomial.eval (e.equivFun a) (squareMultiplierPolynomial e b x y) =
      b (a ^ 2 * x) (a ^ 2 * y) := by
  classical
  have hsq (z : K) : a ^ 2 * z =
      ∑ i, ∑ j, ((e.repr a i) * (e.repr a j)) • (e i * e j * z) := by
    calc
      _ = (∑ i, e.repr a i • e i) * (∑ j, e.repr a j • e j) * z := by
        simp only [e.sum_repr, pow_two]
      _ = ∑ i, ∑ j, ((e.repr a i • e i) * (e.repr a j • e j)) * z := by
        rw [Finset.sum_mul_sum]
        simp only [Finset.sum_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
        rw [mul_comm (e.repr a j) (e.repr a i)]
  rw [hsq x, hsq y]
  simp only [LinearMap.map_sum₂, LinearMap.map_smul₂]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  simp only [squareMultiplierPolynomial, map_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C, e.equivFun_apply, mul_assoc]


set_option maxHeartbeats 800000 in
theorem square_invariant_bilinear_eq_zero_of_degree_bound
    [Fintype R] [Fintype K] [FiniteDimensional R K]
    (hdegree : 4 < (Fintype.card R - 1) * Module.finrank R K)
    (hcard : (Fintype.card K : R) = 0)
    (b : K →ₗ[R] K →ₗ[R] R)
    (hinv : ∀ (a : Kˣ) (x y : K),
      b ((a : K) ^ 2 * x) ((a : K) ^ 2 * y) = b x y) : b = 0 := by
  classical
  let e := Module.finBasis R K
  ext x y
  let P := squareMultiplierPolynomial e b x y
  have hsum : (∑ a : K, b (a ^ 2 * x) (a ^ 2 * y)) = 0 := by
    calc
      _ = ∑ a : K, MvPolynomial.eval (e.equivFun a) P := by
        apply Finset.sum_congr rfl
        intro a _
        exact (squareMultiplierPolynomial_eval e b x y a).symm
      _ = ∑ c : Fin (Module.finrank R K) → R, MvPolynomial.eval c P :=
        by
          exact e.equivFun.toEquiv.sum_comp
            (fun c : Fin (Module.finrank R K) → R => MvPolynomial.eval c P)
      _ = 0 := MvPolynomial.sum_eval_eq_zero P
        (by simpa only [Fintype.card_fin] using
          lt_of_le_of_lt (squareMultiplierPolynomial_totalDegree e b x y) hdegree)
  have hvalue (a : K) : b (a ^ 2 * x) (a ^ 2 * y) =
      b x y - if a = 0 then b x y else 0 := by
    by_cases ha : a = 0
    · simp [ha]
    · simpa [ha] using hinv (Units.mk0 a ha) x y
  simp_rw [hvalue] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.sum_ite_eq', hcard, zero_mul, zero_sub, neg_eq_zero] at hsum
  exact hsum

end Polynomial

theorem alternating_eq_zero_of_finrank_one
    {R : Type w} [Field R] {V : Type u} [AddCommGroup V] [Module R V]
    [FiniteDimensional R V] {W : Type v} [AddCommGroup W] [Module R W]
    (hrank : Module.finrank R V = 1) (b : V →ₗ[R] V →ₗ[R] W)
    (halt : b.IsAlt) : b = 0 := by
  let e := Module.finBasisOfFinrankEq R V hrank
  apply LinearMap.ext_basis e e
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  simpa only [hij, LinearMap.zero_apply] using halt (e j)

theorem quartic_degree_bound {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hf : 1 ≤ f) (hfone : f ≠ 1) (hnine : p ^ f ≠ 9) :
    4 < (p - 1) * f := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := Nat.odd_iff.mp hpodd
    omega
  have hf2 : 2 ≤ f := by omega
  by_cases hp4 : 4 ≤ p
  · have : 3 ≤ p - 1 := by omega
    nlinarith
  · have hpval : p = 3 := by omega
    have hfn : f ≠ 2 := by
      intro hfval
      apply hnine
      simp [hpval, hfval]
    have : 3 ≤ f := by omega
    rw [hpval]
    omega

theorem square_invariant_alternating_eq_zero
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (K : Type u) [Field K] [Algebra (ZMod p) K]
    (hcard : Nat.card K = p ^ f)
    (W : Type v) [AddCommGroup W] [Module (ZMod p) W]
    (b : K →ₗ[ZMod p] K →ₗ[ZMod p] W) (halt : b.IsAlt)
    (hinv : ∀ (a : Kˣ) (x y : K),
      b ((a : K) ^ 2 * x) ((a : K) ^ 2 * y) = b x y)
    (hnine : p ^ f ≠ 9) : b = 0 := by
  classical
  let : Finite K := FixedFieldData.finite_of_prime_power_card K Fact.out hcard
  let : Fintype K := Fintype.ofFinite K
  have hrank : Module.finrank (ZMod p) K = f :=
    FixedFieldData.prime_field_finrank p f K hcard
  by_cases hf1 : f = 1
  · exact alternating_eq_zero_of_finrank_one (hrank.trans hf1) b halt
  have hdegree : 4 < (Fintype.card (ZMod p) - 1) * Module.finrank (ZMod p) K := by
    rw [ZMod.card, hrank]
    exact quartic_degree_bound Fact.out hpodd hf hf1 hnine
  have hcast : (Fintype.card K : ZMod p) = 0 := by
    rw [Fintype.card_eq_nat_card, hcard, Nat.cast_pow]
    simp only [ZMod.natCast_self, zero_pow (by omega : f ≠ 0)]
  ext x y
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod p) (b x y)).mp
  intro φ
  have hz : b.compr₂ φ = 0 :=
    square_invariant_bilinear_eq_zero_of_degree_bound hdegree hcast (b.compr₂ φ)
      (fun a x y => by simp only [LinearMap.compr₂_apply, hinv])
  exact congrArg (fun B : K →ₗ[ZMod p] K →ₗ[ZMod p] ZMod p => B x y) hz


theorem square_invariant_alternating_eq_zero_over_prime_field
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (P : Type w) [Field P] (hprime : Nat.card P = p)
    (K : Type u) [Field K] [Algebra P K] (hcard : Nat.card K = p ^ f)
    (W : Type v) [AddCommGroup W] [Module P W]
    (b : K →ₗ[P] K →ₗ[P] W) (halt : b.IsAlt)
    (hinv : ∀ (a : Kˣ) (x y : K),
      b ((a : K) ^ 2 * x) ((a : K) ^ 2 * y) = b x y)
    (hnine : p ^ f ≠ 9) : b = 0 := by
  classical
  let : Finite P := Nat.finite_of_card_ne_zero (hprime ▸ (Fact.out : p.Prime).ne_zero)
  let : Fintype P := Fintype.ofFinite P
  let : Finite K := FixedFieldData.finite_of_prime_power_card K Fact.out hcard
  let : Fintype K := Fintype.ofFinite K
  have hrank : Module.finrank P K = f := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ Module.finrank P K = Nat.card P ^ Module.finrank P K := by rw [hprime]
      _ = Nat.card K := Module.natCard_eq_pow_finrank.symm
      _ = p ^ f := hcard
  by_cases hf1 : f = 1
  · exact alternating_eq_zero_of_finrank_one (hrank.trans hf1) b halt
  have hdegree : 4 < (Fintype.card P - 1) * Module.finrank P K := by
    rw [Fintype.card_eq_nat_card, hprime, hrank]
    exact quartic_degree_bound Fact.out hpodd hf hf1 hnine
  have hpzero : (p : P) = 0 := by
    rw [← hprime, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero P
  have hcast : (Fintype.card K : P) = 0 := by
    rw [Fintype.card_eq_nat_card, hcard, Nat.cast_pow, hpzero,
      zero_pow (by omega : f ≠ 0)]
  ext x y
  apply (Module.forall_dual_apply_eq_zero_iff P (b x y)).mp
  intro φ
  have hz : b.compr₂ φ = 0 :=
    square_invariant_bilinear_eq_zero_of_degree_bound hdegree hcast (b.compr₂ φ)
      (fun a x y => by simp only [LinearMap.compr₂_apply, hinv])
  exact congrArg (fun B : K →ₗ[P] K →ₗ[P] P => B x y) hz

@[expose] def bilinearOfBiadditive (p : ℕ) {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    {W : Type v} [AddCommGroup W] [Module (ZMod p) W]
    (b : V →+ V →+ W) : V →ₗ[ZMod p] V →ₗ[ZMod p] W :=
  AddMonoidHom.toZModLinearMap p
    (((AddMonoidHom.toZModLinearMapEquiv p (M := V) (M₁ := W)).toAddMonoidHom).comp b)

@[simp] theorem bilinearOfBiadditive_apply
    (p : ℕ) {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    {W : Type v} [AddCommGroup W] [Module (ZMod p) W]
    (b : V →+ V →+ W) (x y : V) : bilinearOfBiadditive p b x y = b x y := rfl

theorem square_invariant_biadditive_eq_zero
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (K : Type u) [Field K] [Algebra (ZMod p) K] (hcard : Nat.card K = p ^ f)
    (W : Type v) [AddCommGroup W] [Module (ZMod p) W]
    (b : K →+ K →+ W) (halt : ∀ x, b x x = 0)
    (hinv : ∀ (a : Kˣ) (x y : K),
      b ((a : K) ^ 2 * x) ((a : K) ^ 2 * y) = b x y)
    (hnine : p ^ f ≠ 9) : b = 0 := by
  have hz := square_invariant_alternating_eq_zero p f hpodd hf K hcard W
    (bilinearOfBiadditive p b) halt hinv hnine
  ext x y
  exact congrArg (fun B : K →ₗ[ZMod p] K →ₗ[ZMod p] W => B x y) hz

end

end CFSG.Semidihedral.SquareInvariantAlternating
