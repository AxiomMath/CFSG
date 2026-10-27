module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallOrder
public import CFSG.RankThree.PartOne.KF.RankGL
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructureNonsquare

public section

namespace CFSG.ComponentClassification.CatFC.OmegaSmall

open Module
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

theorem omegaLb_mul_gt {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = 7 ∨ a + b = 8) :
    5760 < omegaLb a * omegaLb b := by
  have ha7 : a ≤ 7 := by omega
  have hb7 : b ≤ 7 := by omega
  interval_cases a <;> interval_cases b <;> first | omega | decide

section Cases

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_cent_split {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (b : K) (hb : b ≠ 0) (hroot : (d : K) = b ^ 2) (hpos : (μ : K) / (d : K) = 1) :
    5760 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK)
  have hnd := positive_square_kernel_nondegenerate Q hQ A d μ b d.ne_zero hb h2 hsquare hroot
    hsim hpos
  have hcompl := square_kernels_isCompl A d b hb h2 hsquare hroot
  have hne := square_kernels_ne_bot A d b hb h2 hsquare hroot hnonscalar
  let e := positiveSquareKernelCentralizerEquiv Q A d μ b d.ne_zero hb h2 hsquare hroot hsim hpos
  have hndplus : (Q.comp (positiveSquareKernel A b).subtype).polarBilin.Nondegenerate := by
    have heq : (Q.comp (positiveSquareKernel A b).subtype).polarBilin =
        LinearMap.BilinForm.restrict Q.polarBilin (positiveSquareKernel A b) := by
      rw [QuadraticMap.polarBilin_comp]
      ext x y
      rfl
    rw [heq]
    exact hnd.1
  have hndminus : (Q.comp (negativeSquareKernel A b).subtype).polarBilin.Nondegenerate := by
    have heq : (Q.comp (negativeSquareKernel A b).subtype).polarBilin =
        LinearMap.BilinForm.restrict Q.polarBilin (negativeSquareKernel A b) := by
      rw [QuadraticMap.polarBilin_comp]
      ext x y
      rfl
    rw [heq]
    exact hnd.2
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  have hp1 : 1 ≤ finrank K (positiveSquareKernel A b) := Submodule.one_le_finrank_iff.mpr hne.1
  have hm1 : 1 ≤ finrank K (negativeSquareKernel A b) := Submodule.one_le_finrank_iff.mpr hne.2
  have hb1 := omega_card_orthogonalGroup_ge hK hndplus hp1 (by omega) rfl
  have hb2 := omega_card_orthogonalGroup_ge hK hndminus hm1 (by omega) rfl
  have hcard : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (positiveSquareKernel A b).subtype)) *
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (negativeSquareKernel A b).subtype)) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  rw [hcard]
  exact lt_of_lt_of_le (omegaLb_mul_gt hp1 hm1 (by omega)) (Nat.mul_le_mul hb1 hb2)

theorem omega_cent_paired {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (b : K) (hb : b ≠ 0) (hroot : (d : K) = b ^ 2) (hneg : (μ : K) / (d : K) = -1) :
    5760 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK)
  have hcompl := square_kernels_isCompl A d b hb h2 hsquare hroot
  have hgeom := negative_square_kernel_geometry Q hQ A d μ b d.ne_zero hb h2 hsquare hroot hsim
    hneg
  let e := negativeSquareKernelCentralizerEquiv Q hQ A d μ b d.ne_zero hb h2 hsquare hroot hsim
    hneg
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  obtain ⟨-, -, -, -, hh1, hh2⟩ := hgeom
  have hfr : finrank K (positiveSquareKernel A b) = 4 := by omega
  rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartOne.LIT.card_linearEquiv_eq 4 hfr, hK]
  decide

end Cases

section Unitary

variable {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem card_isometryGroup_unitary {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hE : Nat.card E = (ℓ ^ e) ^ 2) (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e)) {m : ℕ}
    (hm : finrank E W = m) (hm1 : 1 ≤ m) :
    (Nat.card (CatalogueBUnitaryIsometry.isometryGroup h) : ℤ) =
      ((ℓ ^ e : ℕ) : ℤ) ^ (m * (m - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 m, (((ℓ ^ e : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ e E :=
    ⟨hℓ, he, by rw [hE]; ring⟩
  have hbar : ∀ r : E, hUF.bar r = sigma.toRingHom r := fun r =>
    (hUF.bar_apply r).trans (hsig r).symm
  let B : W →ₛₗ[hUF.bar] W →ₗ[E] E :=
    { toFun := fun x => h x
      map_add' := fun x y => h.map_add x y
      map_smul' := fun r x => by
        show h (r • x) = hUF.bar r • h x
        rw [h.map_smulₛₗ, hbar r] }
  have hBsymm : B.IsSymm := ⟨fun x y => by
    have := hsym.eq x y
    show hUF.bar (h x y) = h y x
    rw [hbar]
    exact this⟩
  have hBsep : B.SeparatingLeft := hnd.1
  have hcard := (CFSG.LinearGroups.unitary_full_group_order hUF hBsymm hBsep hm hm1).1
  rw [← hcard]
  congr 1
  refine Nat.card_congr
    { toFun := fun g => ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv E W).symm g.val,
        fun x y => g.2 x y⟩
      invFun := fun g => ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv E W g.val,
        fun x y => g.2 x y⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }

end Unitary

section Field

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_cent_field_pos {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hns : ¬ IsSquare (d : K)) (hpos : (μ : K) / (d : K) = 1) :
    5760 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK)
  have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
  letI := scalarField A.toLinearMap d hns hs
  letI := evaluationModule A.toLinearMap
  haveI : Finite (scalarAlgebra A.toLinearMap) := scalarAlgebra_finite_type A.toLinearMap d hns hs
  haveI : Module.Finite (scalarAlgebra A.toLinearMap) V := evaluationModule_finite A.toLinearMap
  have hE : ((Nat.card (scalarAlgebra A.toLinearMap) : ℕ) : ℤ) = 9 := by
    rw [scalarAlgebra_card A.toLinearMap d hns hs, hK]; norm_num
  have hfr := evaluationModule_finrank A.toLinearMap d hns hs
  have hadj := positive_square_adjoint Q A d μ d.ne_zero hsquare hsim hpos
  have hnd := actualPositiveQuadratic_nondegenerate Q A.toLinearMap d d.ne_zero hns hs hadj hQ h2
  let e := actualPositiveCentralizerEquiv Q A.toLinearMap d d.ne_zero hns hs hadj h2
  rw [Nat.card_congr e.toEquiv]
  have hfr4 : finrank (scalarAlgebra A.toLinearMap) V = 2 * (1 + 1) := by omega
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType
      (actualPositiveQuadratic Q A.toLinearMap d d.ne_zero hns hs hadj)) ∨
      (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
        (actualPositiveQuadratic Q A.toLinearMap d d.ne_zero hns hs hadj)) := by
    by_cases hP : CFSG.GroupTheory.WeirSylow.IsPlusType
      (actualPositiveQuadratic Q A.toLinearMap d d.ne_zero hns hs hadj)
    · exact ⟨1, Or.inl ⟨rfl, hP⟩⟩
    · exact ⟨-1, Or.inr ⟨rfl, hP⟩⟩
  have hε' : ε = 1 ∨ ε = -1 := by rcases hε with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    (K := scalarAlgebra A.toLinearMap) hnd (m := 1) hfr4 hε
  rw [hE] at h
  generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup
    (actualPositiveQuadratic Q A.toLinearMap d d.ne_zero hns hs hadj)) = c at h ⊢
  rcases hε' with rfl | rfl <;> (norm_num [Finset.prod_Icc_succ_top] at h; omega)

theorem omega_cent_field_neg {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hns : ¬ IsSquare (d : K)) (hneg : (μ : K) / (d : K) = -1) :
    5760 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK)
  have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
  letI := scalarField A.toLinearMap d hns hs
  letI := evaluationModule A.toLinearMap
  haveI : Finite (scalarAlgebra A.toLinearMap) := scalarAlgebra_finite_type A.toLinearMap d hns hs
  haveI : Module.Finite (scalarAlgebra A.toLinearMap) V := evaluationModule_finite A.toLinearMap
  have hE : Nat.card (scalarAlgebra A.toLinearMap) = (3 ^ 1) ^ 2 := by
    rw [scalarAlgebra_card A.toLinearMap d hns hs, hK]; norm_num
  have hfr := evaluationModule_finrank A.toLinearMap d hns hs
  have hadj := negative_square_adjoint Q A d μ d.ne_zero hsquare hsim hneg
  have hsymm := actualNegativeHermitian_isSymm Q A.toLinearMap d d.ne_zero hns hs hadj
  have hnd := actualNegativeHermitian_nondegenerate Q A.toLinearMap d d.ne_zero hns hs hadj hQ
  let e := actualNegativeCentralizerEquiv Q A.toLinearMap d d.ne_zero hns hs hadj h2
  rw [Nat.card_congr e.toEquiv]
  have hfr4 : finrank (scalarAlgebra A.toLinearMap) V = 4 := by omega
  have h := card_isometryGroup_unitary (sigma := (conjugation A.toLinearMap d hns hs).toRingEquiv)
    Nat.prime_three le_rfl hE
    (actualNegativeHermitian Q.polarBilin A.toLinearMap d d.ne_zero hns hs hadj) hsymm hnd
    (fun z => by
      have := finite_conjugation_eq_card_power A.toLinearMap d hns hs z
      rw [hK] at this
      simpa using this) hfr4 (by norm_num)
  generalize Nat.card (CatalogueBUnitaryIsometry.isometryGroup
    (actualNegativeHermitian Q.polarBilin A.toLinearMap d d.ne_zero hns hs hadj)) = c at h ⊢
  norm_num [Finset.prod_Icc_succ_top] at h
  omega

theorem omega_centralizer_card_gt {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    5760 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hsign := original_similarity_ratio_sign Q hQ A d μ
    d.ne_zero hsquare hsim
  by_cases hsq : IsSquare (d : K)
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      intro h0
      apply d.ne_zero
      rw [hr, h0, mul_zero]
    have hroot : (d : K) = r ^ 2 := by rw [hr]; ring
    rcases hsign with h1 | h1
    · exact omega_cent_split hK hn hn78 Q hQ A d μ hsquare hsim hnonscalar r hr0 hroot h1
    · exact omega_cent_paired hK hn hn78 Q hQ A d μ hsquare hsim hnonscalar r hr0 hroot h1
  · rcases hsign with h1 | h1
    · exact omega_cent_field_pos hK hn hn78 Q hQ A d μ hsquare hsim hsq h1
    · exact omega_cent_field_neg hK hn hn78 Q hQ A d μ hsquare hsim hsq h1

end Field

end CFSG.ComponentClassification.CatFC.OmegaSmall
