module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalIndexA
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagThreeTorsion

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Curtis.Coordinator (autFix mem_autFix)

variable {F : Type} [Field F] [Finite F]

theorem three_ne_zero_card_ge_four {n : ℕ} (hn : 3 ≤ n) (A : GL (Fin n) F) (c : Fˣ)
    (hc : A ^ 3 = GeneralLinearGroup.scalar (Fin n) c)
    (hout : ∀ k : projectiveSL n F, conjAut n F A ≠ MulAut.conj k) :
    (3 : F) ≠ 0 ∧ 4 ≤ Nat.card F := by
  have h3 : (3 : F) ≠ 0 := by
    intro h3
    have : CharP F 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 (by exact_mod_cast h3)
    obtain ⟨k, hk⟩ := exists_inner_of_charThree hn A c hc
    exact hout k hk
  refine ⟨h3, ?_⟩
  by_contra hlt
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have h23 : Nat.card F = 2 ∨ Nat.card F = 3 := by omega
  rcases h23 with h2 | h2
  · have hsub : Subsingleton Fˣ := by
      have : Nat.card Fˣ = 1 := by rw [Nat.card_units, h2]
      exact (Nat.card_eq_one_iff_unique.1 this).1
    have hdu : (Matrix.GeneralLinearGroup.det A : Fˣ) = 1 := Subsingleton.elim _ _
    have hd : (A : Matrix (Fin n) (Fin n) F).det = 1 := by
      have := congrArg Units.val hdu
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    obtain ⟨k, hk⟩ := conjAut_inner_of_det_eq_one hd
    exact hout k hk
  · apply h3
    let _ := Fintype.ofFinite F
    have := Nat.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, h2] at this
    exact_mod_cast this

open scoped Classical in
theorem block_or_minpoly_three (h3 : (3 : F) ≠ 0) (hK : 4 ≤ Nat.card F) {y : GL (Fin 3) F}
    (c : Fˣ) (hyp : y ^ 3 = GeneralLinearGroup.scalar (Fin 3) c) :
    (∃ a : primaryFactors (linEnd y), 2 ≤ mult (linEnd y) a ∧
      (3 ≤ mult (linEnd y) a ∨ 4 ≤ Nat.card (Efac (linEnd y) a))) ∨
    minpoly F (linEnd y) = X ^ 3 - C (c : F) := by
  have hx := squarefree_minpoly_linEnd_of_pow_scalar h3 c hyp
  by_cases hex : ∃ a : primaryFactors (linEnd y), 2 ≤ mult (linEnd y) a ∧
      (3 ≤ mult (linEnd y) a ∨ 4 ≤ Nat.card (Efac (linEnd y) a))
  · exact Or.inl hex
  right
  push Not at hex
  have hle : ∀ a : primaryFactors (linEnd y), mult (linEnd y) a ≤ 1 := by
    intro a
    by_contra h
    push Not at h
    have hE := hex a h
    have := finite_efac a
    have hle : Nat.card F ≤ Nat.card (Efac (linEnd y) a) :=
      Nat.card_le_card_of_injective _ (algebraMap F (Efac (linEnd y) a)).injective
    omega
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx
  rw [Module.finrank_fin_fun] at hsum
  have h1 : 3 ≤ ∑ a : primaryFactors (linEnd y), (a : F[X]).natDegree := by
    refine hsum.le.trans ?_
    exact Finset.sum_le_sum fun a _ => by
      have := hle a
      change (a : F[X]).natDegree * mult (linEnd y) a ≤ _
      nlinarith
  have hprod := prod_primaryFactors hx
  have hne : ∀ a ∈ primaryFactors (linEnd y), a ≠ 0 := fun a ha =>
    (UniqueFactorizationMonoid.irreducible_of_normalized_factor a
      (Multiset.mem_toFinset.1 ha)).ne_zero
  have hdeg : (minpoly F (linEnd y)).natDegree = ∑ a ∈ primaryFactors (linEnd y), a.natDegree := by
    rw [← hprod, Polynomial.natDegree_prod _ _ hne]
  have h2 : ∑ a : primaryFactors (linEnd y), (a : F[X]).natDegree =
      ∑ a ∈ primaryFactors (linEnd y), a.natDegree :=
    Finset.sum_coe_sort (primaryFactors (linEnd y)) fun a => a.natDegree
  have hdvd : minpoly F (linEnd y) ∣ (X ^ 3 - C (c : F) : F[X]) :=
    minpoly.dvd F _ (aeval_linEnd_X_pow_sub_C c hyp)
  have hne0 : (X ^ 3 - C (c : F) : F[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  have h4 := Polynomial.natDegree_le_of_dvd hdvd hne0
  rw [natDegree_X_pow_sub_C] at h4
  have hint : IsIntegral F (linEnd y) := Algebra.IsIntegral.isIntegral _
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
    (monic_X_pow_sub_C _ (by norm_num)) hdvd (by rw [natDegree_X_pow_sub_C]; omega)).symm

omit [Finite F] in
theorem det_eq_of_minpoly_three {y : GL (Fin 3) F} (c : Fˣ)
    (hmin : minpoly F (linEnd y) = X ^ 3 - C (c : F)) :
    (y : Matrix (Fin 3) (Fin 3) F).det = c := by
  have hch : (linEnd y).charpoly = X ^ 3 - C (c : F) := by
    have hd : minpoly F (linEnd y) ∣ (linEnd y).charpoly := LinearMap.minpoly_dvd_charpoly _
    rw [hmin] at hd
    have hmon : (linEnd y).charpoly.Monic := LinearMap.charpoly_monic _
    have hnd : (linEnd y).charpoly.natDegree = 3 := by
      rw [LinearMap.charpoly_natDegree, Module.finrank_fin_fun]
    exact eq_of_monic_of_dvd_of_natDegree_le (monic_X_pow_sub_C _ (by norm_num)) hmon hd
      (by rw [hnd, natDegree_X_pow_sub_C])
  have hdet := LinearMap.det_eq_sign_charpoly_coeff (linEnd y)
  have hdy : LinearMap.det (linEnd y) = (y : Matrix (Fin 3) (Fin 3) F).det :=
    LinearMap.det_toLin' _
  rw [hdy, hch, Module.finrank_fin_fun] at hdet
  rw [hdet]
  simp [coeff_sub, coeff_X_pow, coeff_C]
  ring

theorem conjAut_inner_of_det_cube {A : GL (Fin 3) F} (b : F) (hb : b ≠ 0)
    (hdet : (A : Matrix (Fin 3) (Fin 3) F).det = b ^ 3) :
    ∃ k : projectiveSL 3 F, conjAut 3 F A = MulAut.conj k := by
  let S : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 b⁻¹ (inv_ne_zero hb))
  have hS1 : conjAut 3 F S = 1 :=
    (ProjectivePlane.conjAut_eq_one_iff (by norm_num) S).2 ⟨_, rfl⟩
  have hA'm : ((S * A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      b⁻¹ • ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hdet1 : ((S * A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [hA'm, Matrix.det_smul, hdet]
    simp [inv_mul_cancel₀ (pow_ne_zero 3 hb)]
  obtain ⟨k, hk⟩ := conjAut_inner_of_det_eq_one hdet1
  exact ⟨k, by rw [map_mul, hS1, one_mul] at hk; exact hk⟩

theorem linearDiagSlice_holds : LinearDiagSlice := by
  intro F _ _ ζ hζ3 hlin hout hfixD hQ hT _
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hlin
  obtain ⟨c, hc⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) (A ^ 3)).mp
    (by rw [map_pow]; exact hζ3)
  obtain ⟨h3, hK⟩ := three_ne_zero_card_ge_four (by norm_num) A c hc hout
  rcases block_or_minpoly_three h3 hK c hc with ⟨a, ha, hE⟩ | hmin
  · obtain ⟨Q, hQ', hQp, hQ3⟩ := exists_perfect_three_dvd_autFix_of_block h3
      (squarefree_minpoly_linEnd_of_pow_scalar h3 c hc) a ha hE
    exact hfixD Q (fun x hx => (mem_autFix _ _).1 (hQ' hx)) hQp hQ3
  · have hdet := det_eq_of_minpoly_three c hmin
    by_cases hcube : ∃ b : F, b ^ 3 = c
    · obtain ⟨b, hb⟩ := hcube
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact c.ne_zero (by rw [← hb]; norm_num)
      obtain ⟨k, hk⟩ := conjAut_inner_of_det_cube b hb0 (by rw [hdet, hb])
      exact hout k hk
    · push Not at hcube
      obtain ⟨T, hTfix, hTe, hT9⟩ := hT
      have := card_le_three_of_fixed_exponent_three A c hc hcube T hTfix hTe.2
      omega

end CFSG.HardMathSupport.Malle.E27Lie
