module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamCQ
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3OrthMinusBlock
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU4SplitThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open Polynomial Module QuadraticMap CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus

private theorem even_of_three_dvd_two_pow_sub_one {s : ℕ} (h : 3 ∣ 2 ^ s - 1) : Even s := by
  by_contra hs
  rw [Nat.not_even_iff_odd] at hs
  obtain ⟨k, rfl⟩ := hs
  have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h2 : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * k + 1) = X at *
  omega

private noncomputable def statedSLEquiv (n : ℕ) (K : Type) [Field K] :
    ↥(StatedSL n K) ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL n K)).trans
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm


theorem orth_block_L2 {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {xe : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 xe) {h : K[X]}
    (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q xe h)) {r : ℕ} (hr : Odd r) (hr1 : 1 < r)
    (hL : catalogIs (↥(componentImage Q xe h) ⧸ Subgroup.center ↥(componentImage Q xe h))
      (S10.isL2n r)) :
    h = X ^ 2 + X + 1 ∧ primaryMultiplicity xe.toLinearMap h = 2 ∧ Nat.card K = 2 ^ r := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hs : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hs1 : 1 ≤ (n : ℕ) := n.pos
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hinj := injective_mk'_of_charTwo hQ hT
  have hSB : specialBlock Q xe h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  have hkerc : (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker ≤
      Subgroup.center ↥(orthDerived Q) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact bot_le
  obtain ⟨lam, hlam, hlamk, -⟩ := exists_specialBlock_hom_onto (S := ProjOrthDerived Q)
    (MulEquiv.refl _) (J := componentImage Q xe h) xe h hSB (by simp) hkerc
  have hkerT : ∀ {G : Type} [Group G] (e : G ≃* ↥(specialBlock Q xe h)),
      (lam.comp e.toMonoidHom).ker ≤ Subgroup.center G := by
    intro G _ e z hz
    have h1 : e z ∈ lam.ker := hz
    have h2 := hlamk h1
    have h3 := Subgroup.comap_center_le_center (f := e.toMonoidHom) e.injective
    exact h3 (by simpa using h2)
  have hsurjT : ∀ {G : Type} [Group G] (e : G ≃* ↥(specialBlock Q xe h)),
      Function.Surjective (lam.comp e.toMonoidHom) := fun e => hlam.comp e.surjective
  have hm2 : 2 ≤ primaryMultiplicity xe.toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  by_cases hself : h = reciprocalPolynomial h
  ·
    obtain ⟨m, hm⟩ : ∃ m, primaryMultiplicity xe.toLinearMap h = m := ⟨_, rfl⟩
    obtain ⟨hdeg2, b, hb⟩ := exists_selfDual_matrix_data hx hh hne1 hself hm
    obtain ⟨ε, -⟩ := exists_specialBlock_equiv_SU hx hh b hb
    rw [hs] at ε
    have hcardE : Nat.card (AdjoinRoot h) = (2 ^ (n : ℕ)) ^ 2 := by
      rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hdeg2, hs]
    haveI : CharP (AdjoinRoot h) 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := (n : ℕ)) hcardE
    have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (n : ℕ) (AdjoinRoot h) :=
      CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hcardE hs1
    have hdvd : h ∣ (X ^ 2 + X + 1 : K[X]) := dvd_quadratic_of_mem_primaryFactors hx hh hne1
    have hnd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
    have hΦ : h = X ^ 2 + X + 1 :=
      (eq_of_monic_of_dvd_of_natDegree_le hmon (by monicity!) hdvd (by rw [hnd, hdeg2])).symm
    have hm2' : 2 ≤ m := hm ▸ hm2
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    ·
      obtain rfl : m = 2 := by omega
      obtain ⟨F, hFf, hFfin, hFcard, ⟨eF⟩⟩ :=
        CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaU4S3_exists_su2_equiv hUF
      let e' : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(specialBlock Q xe h) := eF.trans ε.symm
      have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hq).1.commutator_eq_top
      have := eq_of_SL_two_centerQuot_isL2n (E := F) (e := (n : ℕ)) hs1 (by simpa using hFcard)
        hperf (lam.comp e'.toMonoidHom) (hsurjT e') (hkerT e') hr hL
      exact ⟨hΦ, hm, by rw [hs, this]⟩
    ·
      exfalso
      obtain ⟨r', rfl⟩ : ∃ r', m = r' + 1 := ⟨m - 1, by omega⟩
      have hperf : commutator ↥(StatedSU (r' + 1) (2 ^ (n : ℕ)) (AdjoinRoot h)) = ⊤ :=
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv ε hq).1.commutator_eq_top
      by_cases hexc : (r' + 1, 2 ^ (n : ℕ)) = (3, 2)
      ·
        obtain ⟨hr3, hn2⟩ := Prod.mk.inj hexc
        have hr'2 : r' = 2 := by omega
        have hn1 : (n : ℕ) = 1 := by
          have : 2 ^ (n : ℕ) = 2 ^ 1 := by rw [hn2]; rfl
          exact Nat.pow_right_injective (le_refl 2) this
        subst hr'2
        have hcard : Nat.card ↥(StatedSU 3 (2 ^ (n : ℕ)) (AdjoinRoot h)) = 216 := by
          rw [KD264Lie.card_statedSU_eq_nat hUF (by omega), hn1]
          decide +kernel
        have h1 := catalogIs_isL2n_card_of_odd hr hL
        haveI : Finite ↥(componentImage Q xe h) := inferInstance
        have h2 : Nat.card (↥(componentImage Q xe h) ⧸ Subgroup.center ↥(componentImage Q xe h)) ≤
            Nat.card ↥(componentImage Q xe h) :=
          Nat.le_of_dvd Nat.card_pos ⟨Nat.card (Subgroup.center ↥(componentImage Q xe h)),
            Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
        have h3 : Nat.card ↥(componentImage Q xe h) ≤
            Nat.card ↥(StatedSU 3 (2 ^ (n : ℕ)) (AdjoinRoot h)) :=
          Nat.card_le_card_of_surjective (lam.comp ε.symm.toMonoidHom) (hsurjT ε.symm)
        have h4 : 8 ≤ 2 ^ r := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by obtain ⟨c, hc⟩ := hr; omega)
        have h5 : 8 * 63 ≤ 2 ^ r * ((2 ^ r) ^ 2 - 1) := by
          have h6 : 64 ≤ (2 ^ r) ^ 2 := by nlinarith
          have h7 : 63 ≤ (2 ^ r) ^ 2 - 1 := by omega
          exact Nat.mul_le_mul h4 h7
        omega
      · exact false_of_SU_centerQuot_isL2n (E := AdjoinRoot h) (r := r') (t := (n : ℕ))
          (by omega) hs1 hexc hcardE hperf (lam.comp ε.symm.toMonoidHom) (hsurjT ε.symm)
          (hkerT ε.symm) hr hL
  ·
    exfalso
    have hdeg := natDegree_eq_one_of_primary_paired hx hh hne1 hself
    let b : Basis (Fin (primaryMultiplicity xe.toLinearMap h)) (AdjoinRoot h)
        (primaryComponent xe.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
    obtain ⟨ε, -⟩ := exists_specialBlock_equiv_SL hx hh hself b
    let e' : Matrix.SpecialLinearGroup (Fin (primaryMultiplicity xe.toLinearMap h))
        (AdjoinRoot h) ≃* ↥(specialBlock Q xe h) := (statedSLEquiv _ _).symm.trans ε.symm
    have hcardE : Nat.card (AdjoinRoot h) = 2 ^ (n : ℕ) := by
      rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hdeg, pow_one, hs]
    have hω3 : (AdjoinRoot.root h) ^ 3 = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
    have hω1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
    have hωne : AdjoinRoot.root h ≠ 0 := by
      intro h0
      rw [h0] at hω3
      norm_num at hω3
    have hord : orderOf (Units.mk0 (AdjoinRoot.root h) hωne) = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime ?_ ?_
      · ext
        simpa using hω3
      · intro h1
        apply hω1
        simpa using congrArg Units.val h1
    have hdvd : 3 ∣ Nat.card (AdjoinRoot h) - 1 := by
      have h1 := orderOf_dvd_natCard (Units.mk0 (AdjoinRoot.root h) hωne)
      rw [hord, Nat.card_units] at h1
      exact h1
    rw [hcardE] at hdvd
    have hev := even_of_three_dvd_two_pow_sub_one hdvd
    have hperf : commutator (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity xe.toLinearMap h)) (AdjoinRoot h)) = ⊤ :=
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hq).1.commutator_eq_top
    exact false_of_SL_centerQuot_isL2n_even (E := AdjoinRoot h) (e := (n : ℕ)) hm2 hs1 hev
      hcardE hperf (lam.comp e'.toMonoidHom) (hsurjT e') (hkerT e') hr hL

end CFSG.LocalAnalysis.GLTheoremA.T1428
