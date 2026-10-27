module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.RankThree.PartTwo.KFacts.L34
open Matrix

variable {k : Type*} [Field k]

@[expose] noncomputable def xD (u : kˣ) : MulAut (projectiveSL 3 k) :=
  conjAut 3 k (LinearThreeFourOuter.diagGL u)

@[expose] noncomputable def tP [CharP k 2] : projectiveSL 3 k :=
  proj 3 k LinearFieldFour.s₂₃Mat

theorem xD_def (u : kˣ) : xD u = conjAut 3 k (LinearThreeFourOuter.diagGL u) :=
  rfl

theorem xD_tP [CharP k 2] (u : kˣ) : xD u (tP : projectiveSL 3 k) = tP := by
  rw [xD_def, tP, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, LinearThreeFourOuter.coe_diagGL, LinearThreeFourOuter.coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearFieldFour.s₂₃Mat, LinearFieldFour.s₂₃M, Matrix.mul_apply, Fin.sum_univ_three]

theorem tP_mul_tP [CharP k 2] : (tP : projectiveSL 3 k) * tP = 1 := by
  rw [tP, ← map_mul, LinearFieldFour.s₂₃Mat_mul_self, map_one]

theorem s23_mul_hSL_mul_s23 (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) [CharP k 2] :
    LinearFieldFour.s₂₃Mat * hSL u * LinearFieldFour.s₂₃Mat = zSL (u * u) * (hSL u)⁻¹ := by
  have h3 : (u : k) * u * u = 1 := by
    have := congrArg Units.val (LinearThreeFourOuter.units_pow_three hk u)
    simpa [pow_three, mul_assoc] using this
  apply Subtype.ext
  change (LinearFieldFour.s₂₃M : Matrix (Fin 3) (Fin 3) k) * (hSL u : Matrix (Fin 3) (Fin 3) k) *
      LinearFieldFour.s₂₃M = (zSL (u * u) : Matrix (Fin 3) (Fin 3) k) *
      (((hSL u)⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
  rw [coe_hSL hk, coe_zSL hk, coe_hSL_inv hk hu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearFieldFour.s₂₃Mat, LinearFieldFour.s₂₃M, LinearFieldFour.hM, hiM,
      Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (-(u : k)) * h3
  · linear_combination (-1 : k) * h3

theorem tP_mul_aP_mul_inv (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) [CharP k 2] :
    (tP : projectiveSL 3 k) * aP u * tP⁻¹ = (aP u)⁻¹ := by
  have hinv : (tP : projectiveSL 3 k)⁻¹ = tP := inv_eq_of_mul_eq_one_right tP_mul_tP
  have h1 : (tP : projectiveSL 3 k) * aP u * tP =
      proj 3 k (LinearFieldFour.s₂₃Mat * hSL u * LinearFieldFour.s₂₃Mat) := by
    rw [map_mul (proj 3 k), map_mul (proj 3 k)]
    rfl
  have h2 : proj 3 k (zSL (u * u) * (hSL u)⁻¹) = (aP u)⁻¹ := by
    rw [map_mul (proj 3 k), proj_eq_one_iff.mpr (zSL_mem_scalars hk), one_mul, map_inv]
    rfl
  rw [hinv, h1, s23_mul_hSL_mul_s23 hk hu, h2]

theorem xD_pow_three (hk : Nat.card k = 4) (u : kˣ) : xD u ^ 3 = 1 := by
  rw [xD_def, ← map_pow, pow_three, LinearThreeFourOuter.diagGL_mul,
    LinearThreeFourOuter.diagGL_mul, ← pow_three, LinearThreeFourOuter.units_pow_three hk,
    LinearThreeFourOuter.diagGL_one, map_one]

theorem xD_ne_one (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) : xD u ≠ 1 := by
  intro h
  have h1 : xD u bP = bP := by rw [h, MulAut.one_apply]
  rw [xD_def, conjAut_diagGL_bP hk hu, mul_eq_left, inv_eq_one] at h1
  exact aP_ne_one hk hu h1

theorem orderOf_xD (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) : orderOf (xD u) = 3 :=
  orderOf_eq_prime (xD_pow_three hk u) (xD_ne_one hk hu)

theorem xD_inv (u : kˣ) : (xD u)⁻¹ = xD u⁻¹ := by
  rw [xD_def, xD_def, ← map_inv]
  congr 1

theorem xD_mem_eZero (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) {p : projectiveSL 3 k}
    (hp : p ∈ eZero k) : xD u p ∈ eZero k := by
  obtain ⟨i, j, -, -, rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hp
  rw [xD_def, map_mul, map_pow, map_pow, conjAut_diagGL_aP, conjAut_diagGL_bP hk hu]
  exact mul_mem (pow_mem aP_mem_eZero _)
    (pow_mem (mul_mem bP_mem_eZero (inv_mem aP_mem_eZero)) _)

theorem tP_mul_mul_inv_of_fixed (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) [CharP k 2]
    {p : projectiveSL 3 k} (hp : p ∈ eZero k) (hfix : xD u p = p) :
    (tP : projectiveSL 3 k) * p * tP⁻¹ = p⁻¹ := by
  obtain ⟨i, j, -, hj, rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hp
  have hba : Commute (bP : projectiveSL 3 k) (aP u)⁻¹ :=
    commute_of_mem_eZero hk bP_mem_eZero (inv_mem aP_mem_eZero)
  rw [xD_def, map_mul, map_pow, map_pow, conjAut_diagGL_aP, conjAut_diagGL_bP hk hu,
    hba.mul_pow, ← mul_assoc, mul_eq_left] at hfix
  have ha1 := aP_ne_one hk hu
  have ha3 := pow_three_of_mem_eZero hk (aP_mem_eZero (u := u))
  have hj0 : j = 0 := by
    interval_cases j
    · rfl
    · rw [pow_one, inv_eq_one] at hfix
      exact absurd hfix ha1
    · rw [inv_pow, inv_eq_one] at hfix
      exfalso
      apply ha1
      calc aP u = aP u ^ 3 * (aP u ^ 2)⁻¹ := by group
        _ = 1 := by rw [ha3, hfix]; group
  subst hj0
  rw [pow_zero, mul_one, ← MulAut.conj_apply, map_pow, MulAut.conj_apply,
    tP_mul_aP_mul_inv hk hu, inv_pow]

theorem exists_eq_conj_of_commute (hk : Nat.card k = 4) {w : MulAut (projectiveSL 3 k)}
    (hw3 : w ^ 3 = 1) (hwE : ∀ p ∈ eZero k, w * MulAut.conj p = MulAut.conj p * w) :
    ∃ e ∈ eZero k, w = MulAut.conj e := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  have hfix : ∀ p ∈ eZero k, w p = p := fun p hp => by
    apply conj_injective hk
    rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hwE p hp, mul_inv_cancel_right]
  obtain ⟨e, he, rfl | rfl⟩ := (forall_fixes_eZero_iff hk hσ w).mp hfix
  · exact ⟨e, he, rfl⟩
  · exfalso
    set β := betaAut (frobeniusEquiv k 2)
    have hb := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv β e
    rw [betaAut_fixed hk hσ he] at hb
    have hcomm : Commute (MulAut.conj e) β := (mul_inv_eq_iff_eq_mul.mp hb).symm
    rw [hcomm.mul_pow, ← map_pow, pow_three_of_mem_eZero hk he, map_one, one_mul] at hw3
    have hβ2 : β * β = 1 := betaAut_mul_self hk hσ
    apply betaAut_ne_one hk (σ := frobeniusEquiv k 2)
    calc β = β ^ 3 * (β * β)⁻¹ := by group
      _ = 1 := by rw [hw3, hβ2]; group

theorem conj_tP_mul_mul_inv (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) [CharP k 2]
    {w : MulAut (projectiveSL 3 k)} (hw3 : w ^ 3 = 1)
    (hwE : ∀ p ∈ eZero k, w * MulAut.conj p = MulAut.conj p * w) (hwx : w * xD u = xD u * w) :
    MulAut.conj (tP : projectiveSL 3 k) * w * (MulAut.conj tP)⁻¹ = w⁻¹ := by
  obtain ⟨e, he, rfl⟩ := exists_eq_conj_of_commute hk hw3 hwE
  have hxe : xD u e = e := by
    apply conj_injective hk
    rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, ← hwx, mul_inv_cancel_right]
  rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, MulAut.conj_apply,
    tP_mul_mul_inv_of_fixed hk hu he hxe, map_inv]

theorem xD_not_mem_zpowers (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) {e : projectiveSL 3 k}
    (he : e ∈ eZero k) : xD u ∉ Subgroup.zpowers (MulAut.conj e) := by
  intro h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have h1 : xD u bP = bP := by
    rw [← hn, ← map_zpow, MulAut.conj_apply,
      commute_of_mem_eZero hk (zpow_mem he n) bP_mem_eZero, mul_inv_cancel_right]
  rw [xD_def, conjAut_diagGL_bP hk hu, mul_eq_left, inv_eq_one] at h1
  exact aP_ne_one hk hu h1

theorem slConjugation_diagGL_of_diagonal (u : kˣ) {M : SpecialLinearGroup (Fin 3) k}
    (hM : ∀ i j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) k) i j = 0) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k
      (LinearThreeFourOuter.diagGL u) M = M := by
  have h01 := hM 0 1 (by decide)
  have h02 := hM 0 2 (by decide)
  have h10 := hM 1 0 (by decide)
  have h12 := hM 1 2 (by decide)
  have h20 := hM 2 0 (by decide)
  have h21 := hM 2 1 (by decide)
  apply Subtype.ext
  rw [coe_slConjugation, LinearThreeFourOuter.coe_diagGL, LinearThreeFourOuter.coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21]
  rw [mul_comm (u : k), mul_assoc, mul_inv_cancel₀ u.ne_zero, mul_one]

theorem slConjugation_diagGL_transvection (u : kˣ) {i j : Fin 3} (hij : i ≠ j) (hi : i ≠ 0)
    (hj : j ≠ 0) (c : k) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k
      (LinearThreeFourOuter.diagGL u) (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij c := by
  apply Subtype.ext
  rw [coe_slConjugation, LinearThreeFourOuter.coe_diagGL, LinearThreeFourOuter.coe_diagGL_inv]
  fin_cases i <;> fin_cases j <;> simp at hij hi hj <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

theorem rSL_mul_transvection {i j : Fin 3} (hij : i ≠ j) (c : k) :
    rSL * SpecialLinearGroup.transvection hij c =
      SpecialLinearGroup.transvection (i := i + 1) (j := j + 1)
        (fun h => hij (add_right_cancel h)) c * rSL := by
  apply Subtype.ext
  change !![0, 0, 1; 1, 0, 0; 0, 1, 0] * (1 + Matrix.single i j c) =
    (1 + Matrix.single (i + 1) (j + 1) c) * !![(0 : k), 0, 1; 1, 0, 0; 0, 1, 0]
  fin_cases i <;> fin_cases j <;> simp at hij <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

theorem eq_top_of_diagonal_transvection (H : Subgroup (SpecialLinearGroup (Fin 3) k))
    (hdiag : ∀ M : SpecialLinearGroup (Fin 3) k,
      (∀ i j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) k) i j = 0) → M ∈ H)
    (htr : ∀ (i j : Fin 3) (hij : i ≠ j) (c : k), SpecialLinearGroup.transvection hij c ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro M _
  refine SpecialLinearGroup.diagonal_transvection_induction' (· ∈ H) M ?_ htr
    (fun A B hA hB => H.mul_mem hA hB)
  intro i j hij c hc
  apply hdiag
  intro a b hab
  rw [SpecialLinearGroup.diag2n_coe, diagonal_apply_ne _ hab]

theorem eq_top_of_bP_mem {u : kˣ} {H : Subgroup (projectiveSL 3 k)} (hb : bP ∈ H)
    (hfix : ∀ p, xD u p = p → p ∈ H) : H = ⊤ := by
  set H' := H.comap (proj 3 k) with hH'
  have hr : (rSL : SpecialLinearGroup (Fin 3) k) ∈ H' := hb
  have hfix' : ∀ g : SpecialLinearGroup (Fin 3) k,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k
        (LinearThreeFourOuter.diagGL u) g = g → g ∈ H' := fun g hg =>
    hfix _ (by rw [xD_def, conjAut_proj, hg])
  have hconj : ∀ {i j i' j' : Fin 3} (hij : i ≠ j) (hij' : i' ≠ j') (c : k), i' = i + 1 →
      j' = j + 1 → SpecialLinearGroup.transvection hij c ∈ H' →
        SpecialLinearGroup.transvection hij' c ∈ H' := by
    rintro i j i' j' hij hij' c rfl rfl h
    rw [← mul_inv_cancel_right (SpecialLinearGroup.transvection hij' c) rSL,
      ← rSL_mul_transvection hij c]
    exact H'.mul_mem (H'.mul_mem hr h) (H'.inv_mem hr)
  have h12 : ∀ c : k, SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2)
      (by decide) c ∈ H' := fun c =>
    hfix' _ (slConjugation_diagGL_transvection u _ (by decide) (by decide) c)
  have h21 : ∀ c : k, SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1)
      (by decide) c ∈ H' := fun c =>
    hfix' _ (slConjugation_diagGL_transvection u _ (by decide) (by decide) c)
  have h20 : ∀ c : k, SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 0)
      (by decide) c ∈ H' := fun c =>
    hconj (i := 1) (j := 2) (by decide) (by decide) c (by decide) (by decide) (h12 c)
  have h01 : ∀ c : k, SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1)
      (by decide) c ∈ H' := fun c =>
    hconj (i := 2) (j := 0) (by decide) (by decide) c (by decide) (by decide) (h20 c)
  have h02 : ∀ c : k, SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 2)
      (by decide) c ∈ H' := fun c =>
    hconj (i := 2) (j := 1) (by decide) (by decide) c (by decide) (by decide) (h21 c)
  have h10 : ∀ c : k, SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0)
      (by decide) c ∈ H' := fun c =>
    hconj (i := 0) (j := 2) (by decide) (by decide) c (by decide) (by decide) (h02 c)
  have htop : H' = ⊤ := by
    refine eq_top_of_diagonal_transvection H' (fun M hM => hfix' M
      (slConjugation_diagGL_of_diagonal u hM)) ?_
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01 c
    · exact h02 c
    · exact h10 c
    · exact absurd rfl hij
    · exact h12 c
    · exact h20 c
    · exact h21 c
    · exact absurd rfl hij
  rw [eq_top_iff]
  intro p _
  obtain ⟨g, rfl⟩ := proj_surjective 3 k p
  have hg : g ∈ H' := by rw [htop]; exact Subgroup.mem_top g
  exact hg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOL
