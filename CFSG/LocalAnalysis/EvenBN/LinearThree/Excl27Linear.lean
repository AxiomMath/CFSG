module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Polynomial

theorem mul_aeval_of_mul_eq {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {m s s' : A} (h : m * s = s' * m) (p : R[X]) : m * aeval s p = aeval s' p * m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, mul_add, add_mul, hp, hq]
  | monomial n a =>
    have hpow : m * s ^ n = s' ^ n * m := SemiconjBy.pow_right h n
    rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hpow,
      ← mul_assoc]

section Degree

variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
theorem eq_X_sub_one_of_eval_one {g : F[X]} (hg : Irreducible g) (hgm : g.Monic)
    (h1 : g.eval 1 = 0) : g = X - 1 := by
  have hdvd : X - C 1 ∣ g := dvd_iff_isRoot.2 h1
  obtain ⟨k, hk⟩ := hdvd
  have hXu : ¬ IsUnit (X - C (1 : F)) := not_isUnit_X_sub_C 1
  have hku : IsUnit k := (hg.isUnit_or_isUnit hk).resolve_left hXu
  have hkm : k.Monic := by
    have := hgm
    rw [hk] at this
    exact (monic_X_sub_C 1).of_mul_monic_left this
  have hk1 : k = 1 := hkm.eq_one_of_isUnit hku
  rw [hk, hk1, mul_one, map_one]

theorem dvd_card_pow_natDegree_sub_one {r : ℕ} (hr : r.Prime) (a : ℕ) {g : F[X]}
    (hg : Irreducible g) (hgm : g.Monic) (hdvd : g ∣ X ^ r ^ a - 1) (hne : g ≠ X - 1) :
    r ∣ Nat.card F ^ g.natDegree - 1 := by
  classical
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Fintype F := Fintype.ofFinite F
  have hg0 : g ≠ 0 := hg.ne_zero
  set pb := AdjoinRoot.powerBasis hg0 with hpb
  have : Module.Finite F (AdjoinRoot g) := pb.finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite F
  have : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  set β : AdjoinRoot g := AdjoinRoot.root g with hβ
  have hβr : β ^ r ^ a = 1 := by
    have h : aeval β (X ^ r ^ a - 1 : F[X]) = 0 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h
    exact h
  have hβ1 : β ≠ 1 := by
    intro h
    have h0 : aeval (1 : AdjoinRoot g) g = 0 := by
      rw [← h, hβ, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have h0' : algebraMap F (AdjoinRoot g) (g.eval 1) = 0 := by
      have := h0
      rw [← map_one (algebraMap F (AdjoinRoot g)), aeval_algebraMap_apply,
        coe_aeval_eq_eval] at this
      exact this
    have he : g.eval 1 = 0 :=
      (map_eq_zero_iff _ (algebraMap F (AdjoinRoot g)).injective).1 h0'
    exact hne (eq_X_sub_one_of_eval_one hg hgm he)
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero a hr.ne_zero)] at hβr
    exact zero_ne_one hβr
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).1 (orderOf_dvd_of_pow_eq_one hβr)
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hi
    exact hβ1 hi
  have hrβ : r ∣ orderOf β := hi ▸ dvd_pow_self r hi0
  have hcard : Fintype.card (AdjoinRoot g) = Fintype.card F ^ g.natDegree := by
    rw [Module.card_fintype pb.basis, Fintype.card_fin]
    rfl
  have hdvd' : r ∣ Fintype.card F ^ g.natDegree - 1 := by
    rw [← hcard]
    exact hrβ.trans (orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one β hβ0))
  rwa [← Nat.card_eq_fintype_card] at hdvd'

theorem three_le_natDegree_of_dvd {r : ℕ} (hr : r.Prime) (a : ℕ) (h1 : ¬ r ∣ Nat.card F - 1)
    (h2 : ¬ r ∣ Nat.card F ^ 2 - 1) {g : F[X]} (hg : Irreducible g) (hgm : g.Monic)
    (hdvd : g ∣ X ^ r ^ a - 1) (hne : g ≠ X - 1) : 3 ≤ g.natDegree := by
  have hdvd' := dvd_card_pow_natDegree_sub_one hr a hg hgm hdvd hne
  have hd0 : g.natDegree ≠ 0 := (hg.natDegree_pos).ne'
  by_contra hlt
  push Not at hlt
  interval_cases hd : g.natDegree
  · exact hd0 rfl
  · rw [pow_one] at hdvd'
    exact h1 hdvd'
  · exact h2 hdvd'

variable [CharP F 2]

omit [Finite F] in
theorem false_of_aeval_inv {F' : Type*} [Field F'] [Algebra F F'] {g : F[X]} (hg : Irreducible g)
    (hgm : g.Monic) (hdeg : g.natDegree = 3) {β : F'} (hβ : aeval β g = 0)
    (hβ' : aeval β⁻¹ g = 0) : False := by
  set a := g.coeff 2 with ha
  set b := g.coeff 1 with hb
  set c := g.coeff 0 with hc
  have hgform : g = X ^ 3 + C a * X ^ 2 + C b * X + C c := by
    conv_lhs => rw [hgm.as_sum, hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
    ring
  have hev : ∀ x : F', aeval x g =
      x ^ 3 + algebraMap F F' a * x ^ 2 + algebraMap F F' b * x + algebraMap F F' c := by
    intro x
    rw [hgform]
    simp [aeval_def, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, inv_zero, hev] at hβ'
    have hc0 : algebraMap F F' c = 0 := by simpa using hβ'
    have hc0' : c = 0 := (map_eq_zero_iff _ (algebraMap F F').injective).1 hc0
    have hX : X ∣ g := by
      rw [X_dvd_iff]
      exact hc0'
    obtain ⟨k, hk⟩ := hX
    have hku : IsUnit k := (hg.isUnit_or_isUnit hk).resolve_left not_isUnit_X
    have hdeg' := congrArg natDegree hk
    rw [natDegree_mul X_ne_zero (by rintro rfl; exact hku.ne_zero rfl), natDegree_X,
      natDegree_eq_zero_of_isUnit hku, hdeg] at hdeg'
    omega
  have e1 := hβ
  rw [hev] at e1
  have e2 := hβ'
  rw [hev] at e2
  have e2' : 1 + algebraMap F F' a * β + algebraMap F F' b * β ^ 2 +
      algebraMap F F' c * β ^ 3 = 0 := by
    have h3 : β ^ 3 * (β⁻¹ ^ 3 + algebraMap F F' a * β⁻¹ ^ 2 + algebraMap F F' b * β⁻¹ +
        algebraMap F F' c) = 0 := by rw [e2, mul_zero]
    have hinv : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ0
    calc 1 + algebraMap F F' a * β + algebraMap F F' b * β ^ 2 + algebraMap F F' c * β ^ 3
        = β ^ 3 * (β⁻¹ ^ 3 + algebraMap F F' a * β⁻¹ ^ 2 + algebraMap F F' b * β⁻¹ +
          algebraMap F F' c) := by
          have h1 : β ^ 3 * β⁻¹ ^ 3 = 1 := by rw [← mul_pow, hinv, one_pow]
          have h2 : β ^ 3 * β⁻¹ ^ 2 = β := by
            rw [show β ^ 3 = β * β ^ 2 by ring, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
          have h3' : β ^ 3 * β⁻¹ = β ^ 2 := by
            rw [show β ^ 3 = β ^ 2 * β by ring, mul_assoc, hinv, mul_one]
          linear_combination (-1 : F') * h1 - algebraMap F F' a * h2 - algebraMap F F' b * h3'
      _ = 0 := h3
  set Q : F[X] := C (c * a - b) * X ^ 2 + C (c * b - a) * X + C (c ^ 2 - 1) with hQ
  have hQβ : aeval β Q = 0 := by
    have : aeval β Q = algebraMap F F' c * (β ^ 3 + algebraMap F F' a * β ^ 2 +
        algebraMap F F' b * β + algebraMap F F' c) -
        (1 + algebraMap F F' a * β + algebraMap F F' b * β ^ 2 +
          algebraMap F F' c * β ^ 3) := by
      rw [hQ]
      simp only [map_add, map_mul, aeval_C, aeval_X, map_pow, map_sub, map_one]
      ring
    rw [this, e1, e2', mul_zero, sub_zero]
  have hmin : minpoly F β = g := (minpoly.eq_of_irreducible_of_monic hg hβ hgm).symm
  have hQ0 : Q = 0 := by
    by_contra hQ0
    have hle := minpoly.degree_le_of_ne_zero F β hQ0 hQβ
    rw [hmin, degree_eq_natDegree hg.ne_zero, hdeg] at hle
    have hQdeg : Q.degree ≤ 2 := by
      rw [hQ]
      compute_degree
    have := hle.trans hQdeg
    norm_num at this
  have hc2 : c ^ 2 - 1 = 0 := by
    have := congrArg (fun p => p.coeff 0) hQ0
    simp only [hQ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this
    norm_num at this
    exact this
  have hca : c * a - b = 0 := by
    have := congrArg (fun p => p.coeff 2) hQ0
    simp only [hQ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this
    norm_num at this
    exact this
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc1 : c = 1 := by
    have h : (c - 1) ^ 2 = 0 := by linear_combination hc2 - (c - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  have hab : a = b := by
    rw [hc1, one_mul] at hca
    exact sub_eq_zero.1 hca
  have hev1 : g.eval 1 = 0 := by
    rw [hgform]
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, one_pow, mul_one]
    rw [hc1, ← hab]
    linear_combination (1 + a) * h2
  have := congrArg natDegree (eq_X_sub_one_of_eval_one hg hgm hev1)
  rw [hdeg, ← C_1, natDegree_X_sub_C] at this
  omega

theorem false_of_mul_eq_pow_mul {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (hW : Module.finrank F W ≤ 4) {r : ℕ} (hr : r.Prime) (a : ℕ)
    (h1 : ¬ r ∣ Nat.card F - 1) (h2 : ¬ r ∣ Nat.card F ^ 2 - 1)
    (h3 : r ∣ Nat.card F ^ 3 - 1) {s m : Module.End F W} (hs : s ^ r ^ a = 1) (hs1 : s ≠ 1)
    (hm : Function.Surjective m) (hms : m * s = s ^ (r ^ a - 1) * m) : False := by
  classical
  have hq2 : 2 ∣ Nat.card F := by
    have : Fintype F := Fintype.ofFinite F
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card] at h0
    exact (CharP.cast_eq_zero_iff F 2 _).1 h0
  have hr2 : ¬ 2 ∣ r := by
    intro hr2
    have hr2' : r = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 hr2).symm
    subst hr2'
    have hq3 : 2 ∣ Nat.card F ^ 3 := dvd_pow hq2 (by norm_num)
    have hpos : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos 3
    generalize Nat.card F ^ 3 = Q at *
    omega
  have hra2 : ¬ 2 ∣ r ^ a := fun h => hr2 (Nat.prime_two.dvd_of_dvd_pow h)
  have hra : 1 ≤ r ^ a := Nat.one_le_pow _ _ hr.pos
  have : Nontrivial (Module.End F W) := ⟨⟨s, 1, hs1⟩⟩
  have hint : IsIntegral F s := IsIntegral.of_finite F s
  set P := minpoly F s with hP
  have hPs : aeval s P = 0 := minpoly.aeval F s
  have hPm : P.Monic := minpoly.monic hint
  have hP0 : P ≠ 0 := hPm.ne_zero
  have hPdvd : P ∣ X ^ r ^ a - 1 :=
    minpoly.dvd F s (by rw [map_sub, map_pow, aeval_X, map_one, hs, sub_self])
  have hPdeg : P.natDegree ≤ 4 := by
    have h : P.natDegree ≤ s.charpoly.natDegree :=
      natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly s) (LinearMap.charpoly_monic s).ne_zero
    rw [LinearMap.charpoly_natDegree] at h
    omega
  have hPinv : aeval (s ^ (r ^ a - 1)) P = 0 := by
    have h := mul_aeval_of_mul_eq hms P
    rw [hPs, mul_zero] at h
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := hm w
    have h' := LinearMap.congr_fun h v
    rw [LinearMap.zero_apply, Module.End.mul_apply] at h'
    rw [LinearMap.zero_apply]
    exact h'.symm
  have hPcomp : P ∣ P.comp (X ^ (r ^ a - 1)) :=
    minpoly.dvd F s (by rw [aeval_comp, map_pow, aeval_X]; exact hPinv)
  have hsep : (X ^ r ^ a - 1 : F[X]).Separable := by
    have := separable_X_pow_sub_C' 2 (r ^ a) (1 : F) hra2 one_ne_zero
    rwa [map_one] at this
  have hPsq : Squarefree P := (hsep.of_dvd hPdvd).squarefree
  have hX1m : (X - 1 : F[X]).Monic := by simpa using monic_X_sub_C (1 : F)
  have hX1u : ¬ IsUnit (X - 1 : F[X]) := by simpa using not_isUnit_X_sub_C (1 : F)
  have hPX : P ≠ X - 1 := by
    intro h
    apply hs1
    have := hPs
    rw [h, map_sub, aeval_X, map_one, sub_eq_zero] at this
    exact this
  have hPu : ¬ IsUnit P := minpoly.not_isUnit F s
  obtain ⟨Q, hQP, hQu, hQX⟩ : ∃ Q : F[X], Q ∣ P ∧ ¬ IsUnit Q ∧ ¬ (X - 1 : F[X]) ∣ Q := by
    by_cases hX : (X - 1 : F[X]) ∣ P
    · obtain ⟨Q, hQ⟩ := hX
      refine ⟨Q, ⟨X - 1, by rw [hQ, mul_comm]⟩, fun hu => hPX ?_, fun hd => hX1u ?_⟩
      · exact (eq_of_monic_of_associated hX1m hPm ⟨hu.unit, by rw [IsUnit.unit_spec, hQ]⟩).symm
      · obtain ⟨k, hk⟩ := hd
        exact hPsq _ ⟨k, by rw [hQ, hk, mul_assoc]⟩
    · exact ⟨P, dvd_rfl, hPu, hX⟩
  obtain ⟨p, hpm, hpirr, hpQ⟩ := exists_monic_irreducible_factor Q hQu
  have hpP : p ∣ P := hpQ.trans hQP
  have hpX : p ≠ X - 1 := by
    rintro rfl
    exact hQX hpQ
  have hpr : p ∣ X ^ r ^ a - 1 := hpP.trans hPdvd
  have hp3 : 3 ≤ p.natDegree := three_le_natDegree_of_dvd hr a h1 h2 hpirr hpm hpr hpX
  have hp4 : p.natDegree ≤ 4 := (natDegree_le_of_dvd hpP hP0).trans hPdeg
  have hpdeg : p.natDegree = 3 := by
    have h4 := dvd_card_pow_natDegree_sub_one hr a hpirr hpm hpr hpX
    rcases (show p.natDegree = 3 ∨ p.natDegree = 4 by omega) with h | h
    · exact h
    · exfalso
      rw [h] at h4
      apply h1
      have hq1 : 1 ≤ Nat.card F := Nat.card_pos
      have h3' : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow _ _ hq1
      have h4' : 1 ≤ Nat.card F ^ 4 := Nat.one_le_pow _ _ hq1
      have hsplit : Nat.card F ^ 4 - 1 = Nat.card F * (Nat.card F ^ 3 - 1) + (Nat.card F - 1) := by
        zify [hq1, h3', h4']
        ring
      rw [hsplit] at h4
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_right h3 _)).1 h4
  obtain ⟨R, hR⟩ := hpP
  have hR0 : R ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hR
    exact hP0 hR
  have hRdeg : R.natDegree ≤ 1 := by
    have := congrArg natDegree hR
    rw [natDegree_mul hpirr.ne_zero hR0, hpdeg] at this
    omega
  have : Fact (Irreducible p) := ⟨hpirr⟩
  have : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis hpirr.ne_zero).finite
  set α : AdjoinRoot p := AdjoinRoot.root p with hα
  have hαp : aeval α p = 0 := by rw [hα, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hαP : aeval α P = 0 := by rw [hR, map_mul, hαp, zero_mul]
  have hαr : α ^ r ^ a = 1 := by
    obtain ⟨k, hk⟩ := hpr
    have h : aeval α (X ^ r ^ a - 1 : F[X]) = 0 := by rw [hk, map_mul, hαp, zero_mul]
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h
    exact h
  have hα1 : α ≠ 1 := by
    intro h
    have h0 : aeval (1 : AdjoinRoot p) p = 0 := h ▸ hαp
    rw [← map_one (algebraMap F (AdjoinRoot p)), aeval_algebraMap_apply, coe_aeval_eq_eval]
      at h0
    exact hpX (eq_X_sub_one_of_eval_one hpirr hpm
      ((map_eq_zero_iff _ (algebraMap F (AdjoinRoot p)).injective).1 h0))
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero a hr.ne_zero)] at hαr
    exact zero_ne_one hαr
  have hαinv : α ^ (r ^ a - 1) = α⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hra, hαr])
  have hαP' : aeval α⁻¹ P = 0 := by
    obtain ⟨k, hk⟩ := hPcomp
    have h := congrArg (aeval α) hk
    rw [aeval_comp, map_pow, aeval_X, hαinv, map_mul, hαP, zero_mul] at h
    exact h
  rw [hR, map_mul, mul_eq_zero] at hαP'
  rcases hαP' with hp' | hR'
  · exact false_of_aeval_inv hpirr hpm hpdeg hαp hp'
  ·
    have hint' : IsIntegral F α⁻¹ := IsIntegral.of_finite F _
    have hle : (minpoly F α⁻¹).natDegree ≤ R.natDegree :=
      natDegree_le_of_dvd (minpoly.dvd F _ hR') hR0
    have hge : 3 ≤ (minpoly F α⁻¹).natDegree := by
      refine three_le_natDegree_of_dvd hr a h1 h2 (minpoly.irreducible hint') (minpoly.monic hint')
        (minpoly.dvd F _ ?_) fun h => hα1 ?_
      · rw [map_sub, map_pow, aeval_X, map_one, inv_pow, hαr, inv_one, sub_self]
      · have h0 := minpoly.aeval F α⁻¹
        rw [h, map_sub, aeval_X, map_one, sub_eq_zero, inv_eq_one] at h0
        exact h0
    omega

end Degree

end CFSG.LocalAnalysis.EvenBN.LinearThree
