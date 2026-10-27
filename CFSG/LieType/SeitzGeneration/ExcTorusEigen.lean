module

public import CFSG.LieType.SeitzGeneration.ExcTorusCount

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial Module CFSG.Blueprint.Chevalley
open scoped Matrix

section Eigen

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem natCard_eigen_of_squarefree (A : Matrix ι ι K) (μ : K) {f : K[X]} (hf : Squarefree f)
    (hA : aeval A f = 0) :
    Nat.card {z : ι → K // A *ᵥ z = μ • z} = Nat.card K ^ A.charpoly.rootMultiplicity μ := by
  have hφ : aeval (Matrix.toLin' A) f = 0 := by
    have h : aeval (Matrix.toLinAlgEquiv' A) f = Matrix.toLinAlgEquiv' (aeval A f) :=
      aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)) A f
    rw [hA, map_zero] at h
    exact h
  have hss : Module.End.IsSemisimple (Matrix.toLin' A) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf hφ
  have hfin : Module.End.IsFinitelySemisimple (Matrix.toLin' A) :=
    Module.End.isFinitelySemisimple_iff_isSemisimple.mpr hss
  have h1 := hfin.maxGenEigenspace_eq_eigenspace μ
  have h2 := LinearMap.finrank_maxGenEigenspace_eq (Matrix.toLin' A) μ
  rw [Matrix.charpoly_toLin'] at h2
  have h4 : Nat.card {z : ι → K // A *ᵥ z = μ • z} =
      Nat.card (Module.End.eigenspace (Matrix.toLin' A) μ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z => by
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply])
  rw [h4, Module.natCard_eq_pow_finrank (K := K), ← h1, h2]

end Eigen

section ModP

variable {τ : Tag}

theorem aeval_modMat_transpose {p : ℕ} [Fact p.Prime] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    {n : ℕ} (hpow : M ^ n = 1) :
    aeval (modMat p M)ᵀ (X ^ n - C (1 : ZMod p)) = 0 := by
  have h : (modMat p M) ^ n = 1 := by
    have := map_pow (Int.castRingHom (ZMod p)).mapMatrix M n
    rw [hpow, map_one] at this
    exact this.symm
  have h' : (modMat p M)ᵀ ^ n = 1 := by
    rw [← Matrix.transpose_pow, h, Matrix.transpose_one]
  simp [h']

theorem natCard_solutions_modMat {p : ℕ} (hp : p.Prime) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    {n e m q : ℕ} (R : ℤ[X]) (hpow : M ^ n = 1) (hn : ¬ p ∣ n)
    (hchar : M.charpoly = cyclotomic e ℤ ^ m * R) (hpq : ¬ p ∣ q)
    (he : orderOf (q : ZMod p) = e) (hR : ¬ (p : ℤ) ∣ R.eval (q : ℤ)) :
    Nat.card {z : Fin τ.rank → ZMod p // (modMat p M)ᵀ *ᵥ z = (q : ZMod p) • z} = p ^ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hen : (n : ZMod p) ≠ 0 := fun h => hn ((ZMod.natCast_eq_zero_iff n p).1 h)
  have hsep : (X ^ n - C (1 : ZMod p)).Separable := separable_X_pow_sub_C 1 hen one_ne_zero
  rw [natCard_eigen_of_squarefree (modMat p M)ᵀ (q : ZMod p) hsep.squarefree
    (aeval_modMat_transpose M hpow), Matrix.charpoly_transpose, modMat, Matrix.charpoly_map,
    hchar, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_cyclotomic, Nat.card_zmod]
  congr 1
  have hRne : Polynomial.IsRoot (R.map (Int.castRingHom (ZMod p))) (q : ZMod p) → False :=
    fun h => hR (by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := Polynomial.eval_intCast_map (Int.castRingHom (ZMod p)) R (q : ℤ)
    simpa [Polynomial.IsRoot, this] using h)
  have hR0 : R.map (Int.castRingHom (ZMod p)) ≠ 0 := fun h => hRne (by simp [h])
  have hprim : IsPrimitiveRoot (q : ZMod p) e := he ▸ IsPrimitiveRoot.orderOf _
  have hepos : e ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have hene : (e : ZMod p) ≠ 0 := by
    intro h
    have h1 : p ∣ e := (ZMod.natCast_eq_zero_iff e p).1 h
    have h2 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have h3 := Nat.le_of_dvd h2 hepos
    have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero fun h0 => by
      rw [h0] at hepos; omega) h1
    have := hp.one_lt
    omega
  have : NeZero (e : ZMod p) := ⟨hene⟩
  have hroot : Polynomial.IsRoot (cyclotomic e (ZMod p)) (q : ZMod p) :=
    (isRoot_cyclotomic_iff).2 hprim
  have hmon : (cyclotomic e (ZMod p)).Monic := cyclotomic.monic e _
  have hΦ0 : cyclotomic e (ZMod p) ≠ 0 := hmon.ne_zero
  have h1 : (cyclotomic e (ZMod p)).rootMultiplicity (q : ZMod p) = 1 := by
    refine le_antisymm (rootMultiplicity_le_one_of_separable (separable_cyclotomic e _) _) ?_
    exact (rootMultiplicity_pos hΦ0).2 hroot
  have hpow0 : ∀ k : ℕ, (cyclotomic e (ZMod p) ^ k).rootMultiplicity (q : ZMod p) = k := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])
    | succ k ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hΦ0) hΦ0), ih, h1]
  rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero m hΦ0) hR0), hpow0,
    rootMultiplicity_eq_zero hRne, add_zero]

end ModP

end CFSG.LieType.SeitzGeneration
