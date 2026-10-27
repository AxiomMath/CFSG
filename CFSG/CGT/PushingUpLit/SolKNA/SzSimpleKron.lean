module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open Polynomial Matrix

theorem exists_residues {ι : Type} [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι) :
    ∃ j : ι → ZMod 5, (∀ i, j i ≠ 0) ∧ ∑ i, j i = 0 := by
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card ι)
  have key : ∀ t : ZMod 5, ∃ x y : ZMod 5, x ≠ 0 ∧ y ≠ 0 ∧ x + y = t := by decide
  obtain ⟨x, y, hx, hy, hxy⟩ := key (2 - (Fintype.card ι : ZMod 5))
  refine ⟨fun i => 1 + (if i = u then x - 1 else 0) + (if i = v then y - 1 else 0),
    fun i => ?_, ?_⟩
  · by_cases hiu : i = u
    · subst hiu
      simpa [huv] using hx
    · by_cases hiv : i = v
      · subst hiv
        simpa [hiu] using hy
      · simp only [hiu, hiv, ite_false, add_zero]
        decide
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    linear_combination hxy

theorem exists_eigenvector {E : Type} [Field E] (M : Matrix (Fin 4) (Fin 4) E) (μ : E)
    (hμ : M.charpoly.IsRoot μ) : ∃ v : Fin 4 → E, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  have hdet : ((scalar (Fin 4)) μ - M).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec] at hv
  have h1 : (scalar (Fin 4) μ) *ᵥ v = μ • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [h1] at hv
  exact (sub_eq_zero.mp hv).symm

theorem kron_mulVec_prod {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin 4) (Fin 4) E) (v : ι → Fin 4 → E) (μ : ι → E)
    (hv : ∀ i, C i *ᵥ v i = μ i • v i) :
    (Matrix.of fun x' x : ι → Fin 4 => ∏ i, C i (x' i) (x i)) *ᵥ (fun x => ∏ i, v i (x i)) =
      (∏ i, μ i) • (fun x : ι → Fin 4 => ∏ i, v i (x i)) := by
  ext x'
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : ∀ x : ι → Fin 4, (∏ i, C i (x' i) (x i)) * ∏ i, v i (x i) =
      ∏ i, (C i (x' i) (x i) * v i (x i)) := fun x => (Finset.prod_mul_distrib).symm
  simp only [h1]
  rw [← Fintype.prod_sum (fun i (y : Fin 4) => C i (x' i) y * v i y)]
  have h2 : ∀ i, ∑ y : Fin 4, C i (x' i) y * v i y = μ i * v i (x' i) := fun i => by
    have := congrFun (hv i) (x' i)
    simpa [Matrix.mulVec, dotProduct] using this
  simp only [h2]
  exact Finset.prod_mul_distrib

theorem exists_ker_of_map {E E' : Type} [Field E] [Field E'] (ι : E →+* E') {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n E)
    (h : ∃ y : n → E', y ≠ 0 ∧ (M.map ι) *ᵥ y = 0) : ∃ y : n → E, y ≠ 0 ∧ M *ᵥ y = 0 := by
  have h1 : (M.map ι).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp h
  have h2 : ι M.det = 0 := by
    rw [RingHom.map_det]
    exact h1
  exact Matrix.exists_mulVec_eq_zero_iff.mpr ((map_eq_zero ι).mp h2)

theorem exists_fixed_kron {E : Type} [Field E] [CharP E 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : 2 ≤ Fintype.card ι) (C : ι → Matrix (Fin 4) (Fin 4) E)
    (hC : ∀ i, (C i).charpoly = cyclotomic 5 E) :
    ∃ y : (ι → Fin 4) → E, y ≠ 0 ∧
      (Matrix.of fun x' x : ι → Fin 4 => ∏ i, C i (x' i) (x i)) *ᵥ y = y := by
  classical
  let E' := AlgebraicClosure E
  have hchar : CharP E' 2 := charP_of_injective_algebraMap (algebraMap E E').injective 2
  let ι₀ : E →+* E' := algebraMap E E'
  have hne : NeZero ((5 : ℕ) : E') := ⟨fun h => by
    have := (CharP.cast_eq_zero_iff E' 2 5).mp h
    omega⟩
  obtain ⟨ζ, hζroot⟩ : ∃ ζ : E', (cyclotomic 5 E').IsRoot ζ :=
    IsAlgClosed.exists_root _ (degree_cyclotomic_pos 5 E' (by norm_num)).ne'
  have hζ : IsPrimitiveRoot ζ 5 := isRoot_cyclotomic_iff.mp hζroot
  obtain ⟨j, hj0, hjsum⟩ := exists_residues hι
  have heig : ∀ i, ∃ v : Fin 4 → E', v ≠ 0 ∧
      (C i).map ι₀ *ᵥ v = (ζ ^ (j i).val) • v := by
    intro i
    have hcop : Nat.Coprime (j i).val 5 := by
      have hlt : (j i).val < 5 := ZMod.val_lt (j i)
      have hpos : 0 < (j i).val := Nat.pos_of_ne_zero (fun h => hj0 i ((ZMod.val_eq_zero _).mp h))
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr
        (fun hd => absurd (Nat.le_of_dvd hpos hd) (by omega)) |>.symm
    have hprim : IsPrimitiveRoot (ζ ^ (j i).val) 5 := hζ.pow_of_coprime _ hcop
    apply exists_eigenvector
    rw [Matrix.charpoly_map, hC i, Polynomial.map_cyclotomic]
    exact isRoot_cyclotomic_iff.mpr hprim
  choose v hv0 hv using heig
  have hprod : ∏ i, ζ ^ (j i).val = 1 := by
    rw [Finset.prod_pow_eq_pow_sum]
    have hs : ((∑ i, (j i).val : ℕ) : ZMod 5) = 0 := by
      push_cast
      simpa [ZMod.natCast_zmod_val] using hjsum
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ 5).mp hs
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  have hy0 : (fun x : ι → Fin 4 => ∏ i, v i (x i)) ≠ 0 := by
    intro h
    have hx : ∀ i, ∃ a : Fin 4, v i a ≠ 0 := fun i => by
      by_contra hcon
      push Not at hcon
      exact hv0 i (funext hcon)
    choose x₀ hx₀ using hx
    have h1 := congrFun h x₀
    have h2 : ∏ i, v i (x₀ i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hx₀ i
    exact h2 h1
  have hfix : (Matrix.of fun x' x : ι → Fin 4 => ∏ i, (C i).map ι₀ (x' i) (x i)) *ᵥ
      (fun x => ∏ i, v i (x i)) = fun x => ∏ i, v i (x i) := by
    rw [kron_mulVec_prod (fun i => (C i).map ι₀) v _ hv, hprod, one_smul]
  have hmap : ((Matrix.of fun x' x : ι → Fin 4 => ∏ i, C i (x' i) (x i)) - 1).map ι₀ =
      (Matrix.of fun x' x : ι → Fin 4 => ∏ i, (C i).map ι₀ (x' i) (x i)) - 1 := by
    ext x' x
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.of_apply, map_sub, map_prod,
      Matrix.one_apply, apply_ite ι₀, map_one, map_zero]
  obtain ⟨y, hy, hker⟩ := exists_ker_of_map ι₀
    ((Matrix.of fun x' x : ι → Fin 4 => ∏ i, C i (x' i) (x i)) - 1)
    ⟨fun x => ∏ i, v i (x i), hy0, by
      rw [hmap, Matrix.sub_mulVec, hfix, Matrix.one_mulVec, sub_self]⟩
  refine ⟨y, hy, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
  exact hker

end CFSG.CGT.PushingUpLit.SolKNA
