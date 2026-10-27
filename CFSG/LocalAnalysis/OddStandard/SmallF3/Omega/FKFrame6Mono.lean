module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fk_fr_prod_mul_self
    (a : (ZMod 3)ˣ × Multiplicative (SquareClassGroup (ZMod 3))) : a * a = 1 := by
  obtain ⟨u, b⟩ := a
  refine Prod.ext ?_ ?_
  · show u * u = 1
    rcases aux_units_zmod3 u with h | h <;> rw [h] <;> decide
  · show b * b = 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    have h : (2 : ℕ) • Multiplicative.toAdd b = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 (Multiplicative.toAdd b),
        CharP.cast_eq_zero (ZMod 2) 2, zero_smul]
    simpa [two_nsmul] using h

private lemma fk_fr_Q_sub (fr : NFrame Q (Fin 6) (-1)) {a b : Fin 6} (hab : a ≠ b) :
    Q (fr.b a - fr.b b) = 1 := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right, fr.norm a, fr.norm b, fr.orth a b hab, neg_zero, add_zero]
  decide

private lemma fk_fr_polar_sub_left (fr : NFrame Q (Fin 6) (-1)) {a b : Fin 6} (hab : a ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b a) = 1 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self,
    QuadraticMap.polar_comm Q (fr.b b) (fr.b a), fr.norm a, fr.orth a b hab]
  decide

private lemma fk_fr_polar_sub_right (fr : NFrame Q (Fin 6) (-1)) {a b : Fin 6} (hab : a ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b b) = -1 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self, fr.norm b, fr.orth a b hab]
  decide

private lemma fk_fr_polar_sub_of_ne (fr : NFrame Q (Fin 6) (-1)) {a b c : Fin 6}
    (hca : c ≠ a) (hcb : c ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b c) = 0 := by
  rw [QuadraticMap.polar_sub_left, fr.orth a c hca.symm, fr.orth b c hcb.symm]
  decide

private theorem fk_fr_signChange_single_eq_reflection (fr : NFrame Q (Fin 6) (-1)) (i : Fin 6)
    [Invertible (Q (fr.b i))] :
    fr.signChange {i} = TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.b i) := by
  apply Subtype.ext
  apply fr.b.ext'
  intro j
  rw [fr.signChange_basis {i} j, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  by_cases hji : j = i
  · subst hji
    rw [TauCeti.QuadraticMap.reflection_apply_self]
    simp
  · rw [if_neg (by simpa [Finset.mem_singleton] using hji),
      TauCeti.QuadraticMap.reflection_apply, fr.orth i j (Ne.symm hji), mul_zero, zero_smul,
      sub_zero]

private theorem fk_fr_detSpinor_signChange_single (hQ : Q.Nondegenerate)
    (fr : NFrame Q (Fin 6) (-1)) (i : Fin 6) :
    detSpinorNorm hQ (fr.signChange {i}) =
      ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  haveI : Invertible (Q (fr.b i)) :=
    invertibleOfNonzero (by rw [fr.norm i]; exact neg_ne_zero.mpr one_ne_zero)
  rw [fk_fr_signChange_single_eq_reflection fr i, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b i)) = (-1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, fr.norm i]; rfl)
  rw [hunit, squareClassHom_apply]

private theorem fk_fr_detSpinor_signChange (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) (-1))
    (K : Finset (Fin 6)) :
    detSpinorNorm hQ (fr.signChange K) =
      (((-1 : (ZMod 3)ˣ) ^ K.card),
        (Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) ^ K.card) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    rw [fr.signChange_empty, map_one, Finset.card_empty, pow_zero, pow_zero]
    rfl
  | insert i K hi ih =>
    have hsym : symmDiff {i} K = insert i K := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [Finset.mem_symmDiff, hi]
      · simp [Finset.mem_symmDiff, Finset.mem_singleton, hji, hi]
    have hprod : fr.signChange (insert i K) = fr.signChange {i} * fr.signChange K := by
      rw [← hsym, ← fr.signChange_mul]
    rw [hprod, map_mul, fk_fr_detSpinor_signChange_single hQ fr i, ih,
      Finset.card_insert_of_notMem hi, pow_succ', pow_succ', Prod.mk_mul_mk]

private theorem fk_fr_swap_eq_reflection (fr : NFrame Q (Fin 6) (-1)) {a b : Fin 6}
    (hab : a ≠ b) [Invertible (Q (fr.b a - fr.b b))] :
    fr.permOrth (Equiv.swap a b) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.b a - fr.b b) := by
  have hQv := fk_fr_Q_sub fr hab
  apply Subtype.ext
  apply fr.b.ext'
  intro c
  rw [fr.permOrth_basis (Equiv.swap a b) c, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.reflection_apply_eq_sub_div, hQv]
  by_cases hca : c = a
  · subst hca
    rw [Equiv.swap_apply_left, fk_fr_polar_sub_left fr hab]
    have hcoeff : (1 : ZMod 3) / 1 = 1 := by rw [div_one]
    rw [hcoeff, one_smul]
    abel
  · by_cases hcb : c = b
    · subst hcb
      rw [Equiv.swap_apply_right, fk_fr_polar_sub_right fr hab]
      have hcoeff : (-1 : ZMod 3) / 1 = -1 := by rw [div_one]
      rw [hcoeff, neg_one_smul]
      abel
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb, fk_fr_polar_sub_of_ne fr hca hcb,
        zero_div, zero_smul, sub_zero]

private theorem fk_fr_detSpinor_swap (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) (-1))
    {i j : Fin 6} (hij : i ≠ j) :
    detSpinorNorm hQ (fr.permOrth (Equiv.swap i j)) =
      ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
  haveI : Invertible (Q (fr.b i - fr.b j)) :=
    invertibleOfNonzero (by rw [fk_fr_Q_sub fr hij]; exact one_ne_zero)
  rw [fk_fr_swap_eq_reflection fr hij, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b i - fr.b j)) = (1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, fk_fr_Q_sub fr hij]; rfl)
  rw [hunit, map_one]

private theorem fk_fr_detSpinor_permOrth (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) (-1))
    (σ : Equiv.Perm (Fin 6)) :
    detSpinorNorm hQ (fr.permOrth σ) =
      if Equiv.Perm.sign σ = 1 then 1
      else ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    rw [fr.permOrth_one, map_one, Equiv.Perm.sign_one]
    simp
  | swap_mul τ a b hab ih =>
    rw [fr.permOrth_mul, map_mul, fk_fr_detSpinor_swap hQ fr hab, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hab]
    by_cases hs : Equiv.Perm.sign τ = 1
    · rw [ih, hs, if_pos rfl,
        if_neg (by decide : (-1 : ℤˣ) * (1 : ℤˣ) ≠ 1), mul_one]
    · have hs' : Equiv.Perm.sign τ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
        · exact absurd h hs
        · exact h
      rw [ih, hs', if_neg (by decide : (-1 : ℤˣ) ≠ 1),
        if_pos (by decide : (-1 : ℤˣ) * (-1) = 1)]
      exact fk_fr_prod_mul_self _

theorem fk_fr_sign_of_mem_omega (hQ : Q.Nondegenerate) {c : ZMod 3} (hc : c = 1 ∨ c = -1)
    (fr : NFrame Q (Fin 6) c) (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6))
    (h : fr.permOrth σ * fr.signChange K ∈ omegaGroup hQ) : Equiv.Perm.sign σ = 1 := by
  rcases hc with rfl | rfl
  · exact Equiv.Perm.mem_alternatingGroup.mp ((ffMono_mem_omega_iff hQ fr σ K).mp h).1
  · rw [mem_omegaGroup_iff hQ, map_mul, fk_fr_detSpinor_permOrth hQ fr σ,
      fk_fr_detSpinor_signChange hQ fr K] at h
    by_contra hs
    rw [if_neg hs] at h
    have h2 : (Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) ^ K.card = 1 := by
      have := (Prod.ext_iff.mp h).2
      simpa using this
    have h1 : ((-1 : (ZMod 3)ˣ) ^ K.card) = -1 := by
      have := eq_inv_of_mul_eq_one_right (Prod.ext_iff.mp h).1
      simpa using this
    have hs_ne : Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)) ≠ 1 := by
      intro hh
      exact aux_squareClass_neg_one_ne_zero (Multiplicative.ofAdd.injective hh)
    have h3 : (Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) ^ K.card =
        Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)) := by
      rw [← squareClassHom_apply (-1 : (ZMod 3)ˣ), ← map_pow, h1, squareClassHom_apply]
    exact hs_ne (h3.symm.trans h2)

end CFSG.OddStandard.SmallF3.Omega
