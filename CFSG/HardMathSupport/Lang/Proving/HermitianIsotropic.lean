module

public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.HardMathSupport.Lang.Proving

open Finset MvPolynomial Matrix

theorem exists_ne_zero_of_two_quadratic {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [CharP F p] [hp : Fact p.Prime] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (hσ : 4 < Fintype.card σ) (P : Fin 2 → MvPolynomial σ F) (hP : ∀ j, (P j).totalDegree ≤ 2)
    (h0 : ∀ j, eval 0 (P j) = 0) :
    ∃ x : σ → F, x ≠ 0 ∧ ∀ j, eval x (P j) = 0 := by
  classical
  have hdeg : ∑ j ∈ (univ : Finset (Fin 2)), (P j).totalDegree < Fintype.card σ := by
    calc ∑ j ∈ (univ : Finset (Fin 2)), (P j).totalDegree
        ≤ ∑ _j ∈ (univ : Finset (Fin 2)), 2 := sum_le_sum fun j _ => hP j
      _ = 4 := by simp
      _ < Fintype.card σ := hσ
  have hdvd : p ∣ Fintype.card { x : σ → F // ∀ j ∈ (univ : Finset (Fin 2)), eval x (P j) = 0 } := by
    convert char_dvd_card_solutions_of_sum_lt (p := p) hdeg
  have hmem0 : ∀ j ∈ (univ : Finset (Fin 2)), eval (0 : σ → F) (P j) = 0 :=
    fun j _ => h0 j
  have hpos : 0 < Fintype.card { x : σ → F // ∀ j ∈ (univ : Finset (Fin 2)), eval x (P j) = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, hmem0⟩⟩
  have h2 : 1 < Fintype.card { x : σ → F // ∀ j ∈ (univ : Finset (Fin 2)), eval x (P j) = 0 } := by
    have h1 := Nat.le_of_dvd hpos hdvd
    have h2 := hp.out.two_le
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h2 ⟨0, hmem0⟩
  refine ⟨y.1, fun h => hy (Subtype.ext h), fun j => y.2 j (mem_univ j)⟩

theorem exists_ne_zero_bar_dotProduct_mulVec_eq_zero {K : Type*} [Field K] [Finite K] {p f : ℕ}
    [hp : Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ (2 * f)) (hf : 1 ≤ f) {n : ℕ}
    (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) K) :
    ∃ v : Fin n → K, v ≠ 0 ∧ (fun i => v i ^ p ^ f) ⬝ᵥ A.mulVec v = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hp2 : 2 ≤ p := hp.out.two_le
  have hf0 : f ≠ 0 := by omega
  have hKcard : Fintype.card K = p ^ (2 * f) := by rw [Fintype.card_eq_nat_card, hK]
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  have hdimK : Module.finrank (ZMod p) K = 2 * f := by
    have h := FiniteField.pow_finrank_eq_card p K
    rw [hKcard] at h
    exact Nat.pow_right_injective hp2 h
  obtain ⟨φ⟩ : Nonempty (GaloisField p f →ₐ[ZMod p] K) :=
    FiniteField.nonempty_algHom_of_finrank_dvd
      (by rw [GaloisField.finrank p hf0, hdimK]; exact dvd_mul_left f 2)
  let _ : Algebra (GaloisField p f) K := φ.toRingHom.toAlgebra
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField p f) = p ^ f := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p f hf0]
  have hFx : ∀ x : GaloisField p f, x ^ p ^ f = x := fun x => by
    rw [← hFcard]
    exact FiniteField.pow_card x
  have hdimF : Module.finrank (GaloisField p f) K = 2 := by
    have h := Module.card_eq_pow_finrank (K := GaloisField p f) (V := K)
    rw [hKcard, hFcard, ← pow_mul] at h
    have h' : 2 * f = f * Module.finrank (GaloisField p f) K := Nat.pow_right_injective hp2 h
    have hfpos : 0 < f := by omega
    have h'' : f * 2 = f * Module.finrank (GaloisField p f) K := by rw [mul_comm f 2]; exact h'
    exact (Nat.eq_of_mul_eq_mul_left hfpos h'').symm
  have : Module.Finite (GaloisField p f) K := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) (GaloisField p f) K := Module.finBasisOfFinrankEq (GaloisField p f) K hdimF
  have hsmul : ∀ (x : GaloisField p f) (u : K), (x • u) ^ p ^ f = x • u ^ p ^ f := by
    intro x u
    rw [Algebra.smul_def, Algebra.smul_def, mul_pow, ← map_pow, hFx]
  have hsumK : ∀ (g : Fin 2 → K), (∑ k, g k) ^ p ^ f = ∑ k, g k ^ p ^ f := by
    intro g
    have h := map_sum (iterateFrobenius K p f) g (univ : Finset (Fin 2))
    simpa only [iterateFrobenius_def] using h
  have hvpow : ∀ (x : Fin n × Fin 2 → GaloisField p f) (i : Fin n),
      (∑ k, x (i, k) • b k) ^ p ^ f = ∑ k, x (i, k) • (b k) ^ p ^ f := by
    intro x i
    rw [hsumK]
    exact Finset.sum_congr rfl fun k _ => hsmul _ _
  let v : (Fin n × Fin 2 → GaloisField p f) → (Fin n → K) := fun x i => ∑ k, x (i, k) • b k
  let coef : Fin n × Fin 2 → Fin n × Fin 2 → K :=
    fun s t => (b s.2) ^ p ^ f * A s.1 t.1 * b t.2
  let H : (Fin n × Fin 2 → GaloisField p f) → K :=
    fun x => (fun i => v x i ^ p ^ f) ⬝ᵥ A.mulVec (v x)
  have hH : ∀ x, H x = ∑ s, ∑ t, (x s * x t) • coef s t := by
    intro x
    simp only [H, v, coef, dotProduct, Matrix.mulVec, hvpow, Finset.sum_mul, Finset.mul_sum,
      Fintype.sum_prod_type, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1 <;> ring
  let d : Fin 2 → Fin n × Fin 2 → Fin n × Fin 2 → GaloisField p f :=
    fun j s t => b.repr (coef s t) j
  let P : Fin 2 → MvPolynomial (Fin n × Fin 2) (GaloisField p f) :=
    fun j => ∑ s, ∑ t, MvPolynomial.C (d j s t) * X s * X t
  have hevalP : ∀ x j, eval x (P j) = ∑ s, ∑ t, (x s * x t) * d j s t := by
    intro x j
    simp only [P, map_sum, map_mul, eval_C, eval_X]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  have hdegP : ∀ j, (P j).totalDegree ≤ 2 := by
    intro j
    have hterm : ∀ (c : GaloisField p f) (s t : Fin n × Fin 2),
        (MvPolynomial.C c * X s * X t : MvPolynomial (Fin n × Fin 2) (GaloisField p f)).totalDegree
          ≤ 2 := by
      intro c s t
      refine (totalDegree_mul _ _).trans ?_
      refine (add_le_add (totalDegree_mul _ _) le_rfl).trans ?_
      simp [totalDegree_C, totalDegree_X]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun t _ => ?_)
    exact hterm _ s t
  have h0P : ∀ j, eval (0 : Fin n × Fin 2 → GaloisField p f) (P j) = 0 := fun j => by
    rw [hevalP]
    simp
  have hσ : 4 < Fintype.card (Fin n × Fin 2) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨x, hx0, hxP⟩ := exists_ne_zero_of_two_quadratic p hσ P hdegP h0P
  have hHx : H x = 0 := by
    refine (b.repr.map_eq_zero_iff).mp ?_
    refine Finsupp.ext fun j => ?_
    rw [hH x, map_sum]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
    have := hxP j
    rw [hevalP] at this
    simpa [d] using this
  refine ⟨v x, ?_, hHx⟩
  intro hv
  apply hx0
  funext ⟨i, k⟩
  have hi : ∑ k', x (i, k') • b k' = 0 := congrFun hv i
  exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun k' => x (i, k')) hi k

end CFSG.HardMathSupport.Lang.Proving

end
