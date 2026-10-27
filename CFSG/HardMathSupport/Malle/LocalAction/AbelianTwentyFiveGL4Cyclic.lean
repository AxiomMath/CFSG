module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open Polynomial

section Phi5

variable {F : Type} [Field F]

noncomputable def phi5 : F[X] := X ^ 4 + X ^ 3 + X ^ 2 + X + 1

lemma phi5_monic : (phi5 : F[X]).Monic := by
  unfold phi5
  monicity!

lemma phi5_natDegree : (phi5 : F[X]).natDegree = 4 := by
  unfold phi5
  compute_degree!

lemma X_sub_one_mul_phi5 : (X - 1) * (phi5 : F[X]) = X ^ 5 - 1 := by
  unfold phi5; ring

lemma charP_two_of_natCard_eq (hF : Nat.card F = 32) [Finite F] : CharP F 2 := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hpow : ringChar F ^ (n : ℕ) = 2 ^ 5 := by
    rw [← hn, ← Nat.card_eq_fintype_card, hF]; norm_num
  have hdvd : ringChar F ∣ 2 ^ 5 := by
    rw [← hpow]; exact dvd_pow_self _ n.ne_zero
  have h2 : ringChar F = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  rw [← h2]; exact ringChar.charP F

lemma four_le_natDegree_of_dvd_phi5 [Finite F] (hF : Nat.card F = 32) {f : F[X]}
    (hf : Irreducible f) (hd : f ∣ (phi5 : F[X])) : 4 ≤ f.natDegree := by
  have := Fact.mk hf
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
  have : Finite (AdjoinRoot f) := Module.finite_of_finite F
  have := Fintype.ofFinite (AdjoinRoot f)
  have : CharP F 2 := charP_two_of_natCard_eq hF
  have : CharP (AdjoinRoot f) 2 := charP_of_injective_algebraMap (algebraMap F _).injective 2
  have hcard : Nat.card (AdjoinRoot f) = 32 ^ f.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF, (AdjoinRoot.powerBasis hf.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  set r := AdjoinRoot.root f with hr_def
  have hr : r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = 0 := by
    have : AdjoinRoot.mk f (phi5 : F[X]) = 0 := AdjoinRoot.mk_eq_zero.2 hd
    rw [← AdjoinRoot.aeval_eq] at this
    simpa [phi5] using this
  have hr5 : r ^ 5 = 1 := by
    have : (r - 1) * (r ^ 4 + r ^ 3 + r ^ 2 + r + 1) = r ^ 5 - 1 := by ring
    rw [hr, mul_zero] at this
    exact (sub_eq_zero.1 this.symm)
  have hr1 : r ≠ 1 := by
    intro h
    rw [h] at hr
    have h5 : ((5 : ℕ) : AdjoinRoot f) = 0 := by
      push_cast; linear_combination hr
    rw [CharP.cast_eq_zero_iff (AdjoinRoot f) 2] at h5
    omega
  have hr0 : r ≠ 0 := by
    intro h; rw [h] at hr5; simp at hr5
  have hord : orderOf r = 5 := orderOf_eq_prime hr5 hr1
  have hdvd : 5 ∣ 32 ^ f.natDegree - 1 := by
    rw [← hcard, Nat.card_eq_fintype_card, ← hord]
    exact orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one r hr0)
  have hle : f.natDegree ≤ 4 := by
    rw [← phi5_natDegree (F := F)]
    exact natDegree_le_of_dvd hd (by unfold phi5; exact phi5_monic.ne_zero)
  have hpos := hf.natDegree_pos
  by_contra hlt
  interval_cases h : f.natDegree <;> omega

lemma irreducible_phi5 [Finite F] (hF : Nat.card F = 32) : Irreducible (phi5 : F[X]) := by
  obtain ⟨f, hf, hfd⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos (phi5 : F[X]) (by rw [phi5_natDegree]; norm_num)) phi5_monic.ne_zero
  have h4 := four_le_natDegree_of_dvd_phi5 hF hf hfd
  obtain ⟨h, hh⟩ := hfd
  have hf0 : f ≠ 0 := hf.ne_zero
  have hh0 : h ≠ 0 := by
    rintro rfl; exact phi5_monic.ne_zero (by simpa using hh)
  have hdeg : (phi5 : F[X]).natDegree = f.natDegree + h.natDegree := by
    rw [hh, natDegree_mul hf0 hh0]
  rw [phi5_natDegree] at hdeg
  have : h.natDegree = 0 := by omega
  have hu : IsUnit h := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hh0, this]; rfl
  rw [hh]
  exact (irreducible_mul_isUnit hu).2 hf

lemma trace_eq_one_of_pow_five [Finite F] (hF : Nat.card F = 32) {g : Matrix (Fin 4) (Fin 4) F}
    (h5 : g ^ 5 = 1) (h1 : g ≠ 1) : g.trace = 1 := by
  have : CharP F 2 := charP_two_of_natCard_eq hF
  have hirr := irreducible_phi5 hF
  have hm1 : minpoly F g ∣ (X - 1) * (phi5 : F[X]) := by
    rw [X_sub_one_mul_phi5]
    exact minpoly.dvd F g (by simp [h5])
  have hphi : (phi5 : F[X]) ∣ minpoly F g := by
    by_contra hnd
    have hc : IsCoprime (minpoly F g) (phi5 : F[X]) :=
      ((hirr.coprime_iff_not_dvd).2 hnd).symm
    obtain ⟨q, hq⟩ := hc.dvd_of_dvd_mul_right hm1
    apply h1
    have h0 : aeval g (X - 1 : F[X]) = 0 := by
      rw [hq, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h0
  have hchar : (phi5 : F[X]) ∣ g.charpoly :=
    hphi.trans (minpoly.dvd F g g.aeval_self_charpoly)
  have heq : g.charpoly = phi5 :=
    eq_of_monic_of_dvd_of_natDegree_le phi5_monic g.charpoly_monic hchar
      (by rw [g.charpoly_natDegree_eq_dim, phi5_natDegree]; simp)
  rw [Matrix.trace_eq_neg_charpoly_coeff, heq]
  have : (phi5 : F[X]).coeff 3 = 1 := by
    simp [phi5, coeff_X_pow, coeff_X, coeff_one]
  rw [Fintype.card_fin, show 4 - 1 = 3 from rfl, this]
  simp [CharTwo.neg_eq]

end Phi5

lemma isCyclic_of_abelian_card_twentyfive {F : Type} [Field F] [Finite F] (hF : Nat.card F = 32)
    (P : Subgroup (GL (Fin 4) F)) (_hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hc : Nat.card P = 25) : IsCyclic P := by
  classical
  by_contra hnc
  have : CharP F 2 := charP_two_of_natCard_eq hF
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype P := Fintype.ofFinite P
  have hord : ∀ x : P, x ^ 5 = 1 := by
    intro x
    have h1 : orderOf x ∣ 5 ^ 2 := by
      have := orderOf_dvd_natCard x
      rwa [hc] at this
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 h1
    interval_cases k
    · rw [← orderOf_dvd_iff_pow_eq_one, hk']; simp
    · rw [← orderOf_dvd_iff_pow_eq_one, hk']; simp
    · exact absurd (isCyclic_of_orderOf_eq_card x (by rw [hc]; simpa using hk')) hnc
  let v : {x : P // x ≠ 1} → Matrix (Fin 4) (Fin 4) F := fun x => (((x.1 : P) : GL (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F)
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    suffices hall : ∀ y, c y = ∑ i, c i by
      have hcard : Fintype.card {x : P // x ≠ 1} = 24 := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hc]
      have hs : ∑ i, c i = 0 := by
        have h24 : ((24 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 2 24).2 (by norm_num)
        calc ∑ i, c i = ∑ _i : {x : P // x ≠ 1}, ∑ j, c j := Finset.sum_congr rfl fun i _ => hall i
          _ = 0 := by
            rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, h24, zero_mul]
      intro y
      rw [hall y, hs]
    intro y
    have htr : ∀ i : {x : P // x ≠ 1}, (v i * (((y.1⁻¹ : P) : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F)).trace = if i = y then 0 else 1 := by
      intro i
      have hmul : v i * (((y.1⁻¹ : P) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
          = (((i.1 * y.1⁻¹ : P) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        simp [v]
      rw [hmul]
      split_ifs with hi
      · subst hi
        simp
        have h4 := (CharP.cast_eq_zero_iff F 2 4).2 (by norm_num)
        simpa using h4
      · apply trace_eq_one_of_pow_five hF
        · have := congrArg (fun z : P => (((z : P) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
            (hord (i.1 * y.1⁻¹))
          simpa using this
        · intro h
          apply hi
          have : ((i.1 * y.1⁻¹ : P) : GL (Fin 4) F) = 1 := Units.ext h
          have : i.1 * y.1⁻¹ = 1 := Subtype.ext this
          exact Subtype.ext (mul_inv_eq_one.1 this)
    have h1 : ∑ i, c i * (if i = y then (0 : F) else 1) = 0 := by
      have := congrArg (fun M => (M * (((y.1⁻¹ : P) : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F)).trace) hc0
      simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, htr,
        smul_eq_mul, Matrix.zero_mul, Matrix.trace_zero] at this
      exact this
    have h2 : ∑ i, c i * (if i = y then (0 : F) else 1) = (∑ i, c i) - c y := by
      calc ∑ i, c i * (if i = y then (0 : F) else 1)
          = ∑ i, (c i - if i = y then c i else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> ring
        _ = (∑ i, c i) - c y := by
            rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
            simp
    linear_combination h2 - h1
  have hcard : Fintype.card {x : P // x ≠ 1} = 24 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hc]
  have := hli.fintype_card_le_finrank
  rw [hcard, Module.finrank_matrix] at this
  simp at this

end CFSG.HardMathSupport.Malle.LocalAction

