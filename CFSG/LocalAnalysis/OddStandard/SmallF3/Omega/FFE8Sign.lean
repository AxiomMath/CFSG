module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6POmegaAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma ffE8Sign_single_eq_reflection {ι : Type} [Fintype ι] [DecidableEq ι]
    {c : ι → ZMod 3} (fr : PFrame Q ι c) (k : ι) [Invertible (Q (fr.b k))] :
    fr.signChange {k} = TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.b k) := by
  apply Subtype.ext
  apply fr.b.ext'
  intro j
  rw [fr.signChange_basis {k} j, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  by_cases hjk : j = k
  · rw [hjk]
    rw [if_pos (Finset.mem_singleton_self k), TauCeti.QuadraticMap.reflection_apply_self]
  · rw [if_neg (by simpa [Finset.mem_singleton] using hjk),
      TauCeti.QuadraticMap.reflection_apply, fr.orth k j (Ne.symm hjk), mul_zero, zero_smul,
      sub_zero]

private lemma ffE8Sign_single_one {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (hQ : Q.Nondegenerate) (fr : PFrame Q ι c) {k : ι} (h : c k = 1) :
    detSpinorNorm hQ (fr.signChange {k}) =
      ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
  haveI : Invertible (Q (fr.b k)) := invertibleOfNonzero (by rw [fr.norm k, h]; decide)
  rw [ffE8Sign_single_eq_reflection fr k, detSpinorNorm_reflectionOrthogonal hQ]
  have hunit : unitOfInvertible (Q (fr.b k)) = 1 :=
    Units.ext (by rw [val_unitOfInvertible, fr.norm k, h]; rfl)
  rw [hunit, map_one]

private lemma ffE8Sign_single_neg {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (hQ : Q.Nondegenerate) (fr : PFrame Q ι c) {k : ι} (h : c k = -1) :
    detSpinorNorm hQ (fr.signChange {k}) =
      ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  haveI : Invertible (Q (fr.b k)) := invertibleOfNonzero (by rw [fr.norm k, h]; decide)
  rw [ffE8Sign_single_eq_reflection fr k, detSpinorNorm_reflectionOrthogonal hQ]
  have hunit : unitOfInvertible (Q (fr.b k)) = (-1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, fr.norm k, h]; rfl)
  rw [hunit, squareClassHom_apply]

theorem ffE8Sign_detSpinor (hQ : Q.Nondegenerate) {ι : Type} [Fintype ι] [DecidableEq ι]
    {c : ι → ZMod 3} (fr : PFrame Q ι c) (hc : ∀ i, c i = 1 ∨ c i = -1) (K : Finset ι) :
    detSpinorNorm hQ (fr.signChange K) =
      (((-1 : (ZMod 3)ˣ) ^ K.card),
        (Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) ^
          (K.filter fun i => c i = -1).card) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    simp [fr.signChange_empty]
    rfl
  | insert i K hi ih =>
    have hsym : symmDiff K {i} = insert i K := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [Finset.mem_symmDiff, hi]
      · simp [Finset.mem_symmDiff, Finset.mem_singleton, hji]
    have hprod : fr.signChange (insert i K) = fr.signChange K * fr.signChange {i} := by
      rw [← hsym, ← fr.signChange_mul]
    rw [hprod, map_mul, ih]
    rcases hc i with h | h
    · rw [ffE8Sign_single_one hQ fr h, Prod.mk_mul_mk,
        Finset.card_insert_of_notMem hi, Finset.filter_insert,
        if_neg (by rw [h]; decide), Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
      · rw [mul_one]
    · rw [ffE8Sign_single_neg hQ fr h, Prod.mk_mul_mk,
        Finset.card_insert_of_notMem hi, Finset.filter_insert, if_pos h,
        Finset.card_insert_of_notMem (by simp [hi]), Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
      · rw [pow_succ]

private lemma ffE8Sign_sq_pow_eq_one_iff (m : ℕ) :
    (Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) ^ m = 1 ↔ Even m := by
  set s : Multiplicative (SquareClassGroup (ZMod 3)) :=
    Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)) with hs_def
  have hs1 : s ≠ 1 := by
    rw [hs_def]
    exact fun h => aux_squareClass_neg_one_ne_zero (Multiplicative.ofAdd.injective h)
  have hsq : s * s = 1 :=
    (Prod.ext_iff.mp (ffOutFF6POmega_prod_mul_self ((1 : (ZMod 3)ˣ), s))).2
  have horder : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hs1
  rw [← orderOf_dvd_iff_pow_eq_one, horder, even_iff_two_dvd]

theorem ffE8Sign_mem_omega_iff (hQ : Q.Nondegenerate) {ι : Type} [Fintype ι] [DecidableEq ι]
    {c : ι → ZMod 3} (fr : PFrame Q ι c) (hc : ∀ i, c i = 1 ∨ c i = -1) (K : Finset ι) :
    fr.signChange K ∈ omegaGroup hQ ↔
      Even K.card ∧ Even (K.filter fun i => c i = -1).card := by
  rw [mem_omegaGroup_iff hQ, ffE8Sign_detSpinor hQ fr hc K]
  show (((-1 : (ZMod 3)ˣ) ^ K.card,
      (Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) ^
        (K.filter fun i => c i = -1).card) = (1, 1)) ↔
    Even K.card ∧ Even (K.filter fun i => c i = -1).card
  rw [Prod.mk.injEq, ffE8Sign_sq_pow_eq_one_iff,
    neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)]

end CFSG.OddStandard.SmallF3.Omega
