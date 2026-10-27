module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.BlockLevi

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem dvd_cyclotomic_three_of_nontrivial (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) : h ∣ (X ^ 2 + X + 1 : K[X]) := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd := hx.dvd_X_pow_sub_one hh
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * (X ^ 2 + X + 1) := by ring
  rw [hfac] at hdvd
  rcases hirr.prime.dvd_or_dvd hdvd with h1 | h2
  · exact absurd (eq_of_monic_of_associated hmon monic_X_sub_one
      (hirr.associated_of_dvd irreducible_X_sub_one h1)) hne1
  · exact h2

theorem reciprocalPolynomial_X_add_C {c : K} (hc : c ≠ 0) :
    reciprocalPolynomial (X + C c : K[X]) = X + C c⁻¹ := by
  have h0 : (X + C c : K[X]).coeff 0 = c := by simp
  have hX : (X : K[X]).reverse = 1 := by
    have := reverse_mul_X (1 : K[X])
    rw [one_mul] at this
    rw [this, show (1 : K[X]) = C 1 from C_1.symm, reverse_C]
  have h1 : (X + C c : K[X]).reverse = 1 + C c * X := by
    rw [reverse_add_C, hX, natDegree_X, pow_one]
  unfold reciprocalPolynomial
  rw [h0, h1, mul_add, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul, mul_one]
  ring

theorem eq_or_eq_reciprocal (hx : OddOrderIsometry Q 3 x) {a b : K[X]}
    (ha : a ∈ primaryFactors x.toLinearMap) (hb : b ∈ primaryFactors x.toLinearMap)
    (ha1 : a ≠ X - 1) (hb1 : b ≠ X - 1) : b = a ∨ b = reciprocalPolynomial a := by
  by_cases hba : b = a
  · exact Or.inl hba
  right
  have hairr := irreducible_of_mem_primaryFactors ha
  have hbirr := irreducible_of_mem_primaryFactors hb
  have hamon := monic_of_mem_primaryFactors ha
  have hbmon := monic_of_mem_primaryFactors hb
  have haΦ := dvd_cyclotomic_three_of_nontrivial hx ha ha1
  have hbΦ := dvd_cyclotomic_three_of_nontrivial hx hb hb1
  have hΦdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hΦmon : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!
  have hcop : IsCoprime a b := isCoprime_of_mem_primaryFactors ha hb (Ne.symm hba)
  have habΦ : a * b ∣ (X ^ 2 + X + 1 : K[X]) := hcop.mul_dvd haΦ hbΦ
  have hapos : 0 < a.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hairr)
  have hbpos : 0 < b.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hbirr)
  have hmul : (a * b).natDegree = a.natDegree + b.natDegree := Monic.natDegree_mul hamon hbmon
  have hle : (a * b).natDegree ≤ 2 := by
    have := natDegree_le_of_dvd habΦ hΦmon.ne_zero
    omega
  have hda : a.natDegree = 1 := by omega
  have hdb : b.natDegree = 1 := by omega
  have hab : a * b = X ^ 2 + X + 1 :=
    eq_of_monic_of_dvd_of_natDegree_le (hamon.mul hbmon) hΦmon habΦ (by omega) |>.symm
  have hform_a : a = X + C (a.coeff 0) := hamon.eq_X_add_C hda
  have hform_b : b = X + C (b.coeff 0) := hbmon.eq_X_add_C hdb
  have h00 : a.coeff 0 * b.coeff 0 = 1 := by
    have := congrArg (fun p : K[X] => p.coeff 0) hab
    simpa [mul_coeff_zero] using this
  have ha0 : a.coeff 0 ≠ 0 := fun h => by simp [h] at h00
  have hb0 : b.coeff 0 = (a.coeff 0)⁻¹ := eq_inv_of_mul_eq_one_right h00
  conv_rhs => rw [hform_a, reciprocalPolynomial_X_add_C ha0]
  rw [hform_b, hb0]

theorem natDegree_eq_two_of_selfDual (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) : h.natDegree = 2 := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hΦmon : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!
  have hΦdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hle : h.natDegree ≤ 2 := by
    have := natDegree_le_of_dvd (dvd_cyclotomic_three_of_nontrivial hx hh hne1) hΦmon.ne_zero
    omega
  have hpos : 0 < h.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  by_contra hne2
  have hd1 : h.natDegree = 1 := by omega
  obtain ⟨ω, hω0, hω2, heig, heig'⟩ := exists_eigen_of_natDegree_one hx hh hne1 hd1
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot hx.squarefree_minpoly hh)
  have h1 := heig v hv
  have h2 := heig' v (by rw [← hself]; exact hv)
  rw [h1] at h2
  have h3 : ω = ω⁻¹ := by
    by_contra hne
    have : (ω - ω⁻¹) • v = 0 := by rw [sub_smul, h2, sub_self]
    exact hv0 ((smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne))
  apply hω2
  calc ω ^ 2 = ω * ω := sq ω
    _ = ω * ω⁻¹ := congrArg (ω * ·) h3
    _ = 1 := mul_inv_cancel₀ hω0

theorem finrank_orbitSpace (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    finrank K (orbitSpace x.toLinearMap h) = 2 * primaryMultiplicity x.toLinearMap h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : h = reciprocalPolynomial h
  · have hdeg := natDegree_eq_two_of_selfDual hx hh hne1 hself
    have : orbitSpace x.toLinearMap h = primaryComponent x.toLinearMap h := by
      rw [orbitSpace, ← hself, sup_idem]
    rw [this, finrank_primaryComponent, hdeg]
  · have hdeg := natDegree_eq_one_of_paired hx hh hne1 hself
    have hh' := hx.reciprocalPolynomial_mem hh
    haveI : Fact (Irreducible (reciprocalPolynomial h)) :=
      ⟨irreducible_of_mem_primaryFactors hh'⟩
    obtain ⟨hdeg', hmult, -⟩ := hx.pairedModel hh hne1 hself
    have hdisj := disjoint_primaryComponent_of_ne hx hh hh' hself
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (primaryComponent x.toLinearMap h)
      (primaryComponent x.toLinearMap (reciprocalPolynomial h))
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h1
    have h2 := finrank_primaryComponent x.toLinearMap h
    have h3 := finrank_primaryComponent x.toLinearMap (reciprocalPolynomial h)
    have hm2 : finrank (AdjoinRoot (reciprocalPolynomial h))
        ↥(primaryComponent x.toLinearMap (reciprocalPolynomial h)) =
        primaryMultiplicity x.toLinearMap h := hmult.symm
    unfold orbitSpace
    rw [h1, h2, h3, ← hdeg', hdeg, hm2]
    unfold primaryMultiplicity
    ring

theorem othersSpace_eq_orbitSpace (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    othersSpace x.toLinearMap (X - 1) = orbitSpace x.toLinearMap h := by
  have hh' := hx.reciprocalPolynomial_mem hh
  have hh'1 : reciprocalPolynomial h ≠ X - 1 := by
    intro h'
    apply hne1
    rw [← hx.reciprocal_reciprocal_eq hh, h', reciprocalPolynomial_X_sub_one]
  apply le_antisymm
  · unfold othersSpace
    refine iSup_le fun k => iSup_le fun hk => ?_
    rcases eq_or_eq_reciprocal hx hh hk.1 hne1 hk.2.1 with heq | heq
    · rw [heq]
      exact le_sup_left
    · rw [heq]
      exact le_sup_right
  · unfold orbitSpace
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le h ⟨hh, hne1, by rw [reciprocalPolynomial_X_sub_one]; exact hne1⟩ le_rfl
    · exact le_iSup₂_of_le (reciprocalPolynomial h)
        ⟨hh', hh'1, by rw [reciprocalPolynomial_X_sub_one]; exact hh'1⟩ le_rfl

section Parity

open CFSG.RankThree.OrthogonalInvolutions in
theorem even_finrank_sub_fixedSpace (hQ : (polarBilin Q).Nondegenerate) {y : V ≃ₗ[K] V}
    (hy : y ∈ orthDerived Q) : Even (finrank K V - finrank K (fixedSpace y)) := by
  have hd := dicksonHom_eq_one_of_mem_orthDerived hQ hy
  simp only [dicksonHom_apply, ofAdd_eq_one] at hd
  have hev : Even (finrank K (commSpace y)) := (ZMod.natCast_eq_zero_iff_even).mp hd
  have h2 := finrank_commSpace_add_finrank_fixSpace y
  have h3 : finrank K (fixSpace y) = finrank K (fixedSpace y) := rfl
  rw [← h2, h3, Nat.add_sub_cancel]
  exact hev

end Parity

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
