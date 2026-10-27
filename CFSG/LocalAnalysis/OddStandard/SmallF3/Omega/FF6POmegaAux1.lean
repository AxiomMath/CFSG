module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}


theorem ffOutFF6POmega_signChange_single_eq_reflection (fr : PFrame Q (Option (Fin 5)) ffC)
    (k : Option (Fin 5)) [Invertible (Q (fr.b k))] :
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

lemma ffOutFF6POmega_Q_sub (fr : PFrame Q (Option (Fin 5)) ffC) {i j : Fin 5} (hij : i ≠ j) :
    Q (fr.b (some i) - fr.b (some j)) = -1 := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right, fr.norm (some i), fr.norm (some j),
    fr.orth (some i) (some j) (by simpa using hij), neg_zero, add_zero]
  simp only [ffC]
  decide

lemma ffOutFF6POmega_polar_sub_left (fr : PFrame Q (Option (Fin 5)) ffC) {i j : Fin 5}
    (hij : i ≠ j) :
    polar Q (fr.b (some i) - fr.b (some j)) (fr.b (some i)) = -1 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self,
    QuadraticMap.polar_comm Q (fr.b (some j)) (fr.b (some i)),
    fr.norm (some i), fr.orth (some i) (some j) (by simpa using hij)]
  simp only [ffC]
  decide

lemma ffOutFF6POmega_polar_sub_right (fr : PFrame Q (Option (Fin 5)) ffC) {i j : Fin 5}
    (hij : i ≠ j) :
    polar Q (fr.b (some i) - fr.b (some j)) (fr.b (some j)) = 1 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self,
    fr.norm (some j), fr.orth (some i) (some j) (by simpa using hij)]
  simp only [ffC]
  decide

lemma ffOutFF6POmega_polar_sub_of_ne (fr : PFrame Q (Option (Fin 5)) ffC) {a b c : Option (Fin 5)}
    (hca : c ≠ a) (hcb : c ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b c) = 0 := by
  rw [QuadraticMap.polar_sub_left, fr.orth a c hca.symm, fr.orth b c hcb.symm]
  decide

theorem ffOutFF6POmega_swap_eq_reflection (fr : PFrame Q (Option (Fin 5)) ffC) {i j : Fin 5}
    (hij : i ≠ j) [Invertible (Q (fr.b (some i) - fr.b (some j)))] :
    fr.pOrth (Equiv.swap i j) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.b (some i) - fr.b (some j)) := by
  have hQv := ffOutFF6POmega_Q_sub fr hij
  apply Subtype.ext
  apply fr.b.ext'
  intro c
  rw [fr.pOrth_basis (Equiv.swap i j) c, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.reflection_apply_eq_sub_div, hQv]
  cases c with
  | none =>
    rw [Equiv.optionCongr_apply, Option.map_none,
      ffOutFF6POmega_polar_sub_of_ne fr (by intro h; cases h) (by intro h; cases h)]
    simp
  | some k =>
    rw [Equiv.optionCongr_apply, Option.map_some]
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left, ffOutFF6POmega_polar_sub_left fr hij]
      have hcoeff : (-1 : ZMod 3) / (-1) = 1 := by
        rw [div_eq_mul_inv, inv_neg, inv_one, mul_neg, mul_one, neg_neg]
      rw [hcoeff, one_smul]
      abel
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right, ffOutFF6POmega_polar_sub_right fr hij]
        have hcoeff : (1 : ZMod 3) / (-1) = -1 := by
          rw [div_eq_mul_inv, inv_neg, inv_one, mul_neg, mul_one]
        rw [hcoeff, neg_one_smul]
        abel
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
          ffOutFF6POmega_polar_sub_of_ne fr (by simpa using hki) (by simpa using hkj)]
        simp

lemma ffOutFF6POmega_neg_one_mul_pow_succ (n : ℕ) :
    (-1 : (ZMod 3)ˣ) * (-1) ^ (n + 1) = (-1) ^ n := by
  have hsq : (-1 : (ZMod 3)ˣ) * (-1) = 1 := by decide
  rw [pow_succ, mul_comm ((-1 : (ZMod 3)ˣ) ^ n) (-1), ← mul_assoc, hsq, one_mul]

theorem ffOutFF6POmega_prod_mul_self
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

lemma ffOutFF6POmega_eps_erase (σ : Equiv.Perm (Fin 5)) :
    ((if Equiv.Perm.sign σ = 1 then (∅ : Finset (Option (Fin 5))) else {none}).erase
        none) = ∅ := by
  by_cases hs : Equiv.Perm.sign σ = 1
  · simp [hs]
  · simp [hs, Finset.erase_singleton]

lemma ffOutFF6POmega_eps_map (σ ρ : Equiv.Perm (Fin 5)) :
    ((if Equiv.Perm.sign σ = 1 then (∅ : Finset (Option (Fin 5))) else {none}).map
        (Equiv.optionCongr ρ).toEmbedding) =
      (if Equiv.Perm.sign σ = 1 then ∅ else {none}) := by
  by_cases hs : Equiv.Perm.sign σ = 1
  · simp [hs]
  · rw [if_neg hs, Finset.map_singleton, Finset.singleton_inj]
    rfl

lemma ffOutFF6POmega_symmDiff_eps (σ τ : Equiv.Perm (Fin 5)) :
    symmDiff (if Equiv.Perm.sign σ = 1 then (∅ : Finset (Option (Fin 5))) else {none})
      (if Equiv.Perm.sign τ = 1 then ∅ else {none}) =
    (if Equiv.Perm.sign (σ * τ) = 1 then ∅ else {none}) := by
  by_cases hs : Equiv.Perm.sign σ = 1
  · by_cases ht : Equiv.Perm.sign τ = 1
    · rw [if_pos hs, if_pos ht,
        if_pos (by rw [Equiv.Perm.sign_mul, hs, ht, mul_one])]
      simp
    · rw [if_pos hs, if_neg ht,
        if_neg (by rw [Equiv.Perm.sign_mul, hs, one_mul]; exact ht)]
      simp
  · by_cases ht : Equiv.Perm.sign τ = 1
    · rw [if_neg hs, if_pos ht,
        if_neg (by rw [Equiv.Perm.sign_mul, ht, mul_one]; exact hs)]
      simp
    · have hs' : Equiv.Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h hs
        · exact h
      have ht' : Equiv.Perm.sign τ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
        · exact absurd h ht
        · exact h
      rw [if_neg hs, if_neg ht,
        if_pos (by rw [Equiv.Perm.sign_mul, hs', ht']; decide)]
      simp

end CFSG.OddStandard.SmallF3.Omega
