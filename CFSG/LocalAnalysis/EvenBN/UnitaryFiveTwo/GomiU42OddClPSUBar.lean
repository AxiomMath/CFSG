module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSUBarEq
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSUAlt
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddCl
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarCard
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarArithSp
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarArithOdd
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarArithEvP
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarArithEvM

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p f n : ℕ} {K : Type} [Field K]

theorem u42_psi_comm_conj (h : UnitaryFieldData p f K) (A g : ↥(primeFormUnitary h (idGram K n)))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x) (z : Kˣ)
    (hz : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar =
      (z : K) • (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩ *
        primeFormConjHom h (idGram K n) g =
      primeFormConjHom h (idGram K n) g *
        primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩ := by
  have hGL : (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) z * ((g : GL (Fin n) K) * (A : GL (Fin n) K)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar]
    have hmap : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := Matrix.ext fun i j => hφ _
    rw [hmap, hz, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H s =>
    rw [MulAut.mul_apply, MulAut.mul_apply, primeFormConjHom_mk,
      CFSG.ComponentClassification.CatFC.psu_graph_hψ h A φ _,
      CFSG.ComponentClassification.CatFC.psu_graph_hψ h A φ s, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (A : GL (Fin n) K) * glAut φ ((g : GL (Fin n) K) * (s : GL (Fin n) K) *
        (g : GL (Fin n) K)⁻¹) * (A : GL (Fin n) K)⁻¹ =
      (g : GL (Fin n) K) * ((A : GL (Fin n) K) * glAut φ (s : GL (Fin n) K) *
        (A : GL (Fin n) K)⁻¹) * (g : GL (Fin n) K)⁻¹
    set Z : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) z with hZ
    rw [map_mul, map_mul, map_inv]
    have e1 : (A : GL (Fin n) K) * (glAut φ (g : GL (Fin n) K) * glAut φ (s : GL (Fin n) K) *
        (glAut φ (g : GL (Fin n) K))⁻¹) * (A : GL (Fin n) K)⁻¹ =
        ((A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K)) * glAut φ (s : GL (Fin n) K) *
          ((A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K))⁻¹ := by group
    rw [e1, hGL]
    have e2 : Z * ((g : GL (Fin n) K) * (A : GL (Fin n) K)) * glAut φ (s : GL (Fin n) K) *
        (Z * ((g : GL (Fin n) K) * (A : GL (Fin n) K)))⁻¹ =
        Z * (((g : GL (Fin n) K) * (A : GL (Fin n) K)) * glAut φ (s : GL (Fin n) K) *
          ((g : GL (Fin n) K) * (A : GL (Fin n) K))⁻¹) * Z⁻¹ := by group
    rw [e2, ← (commute_scalar z (((g : GL (Fin n) K) * (A : GL (Fin n) K)) *
      glAut φ (s : GL (Fin n) K) * ((g : GL (Fin n) K) * (A : GL (Fin n) K))⁻¹)).eq, ← hZ]
    group


open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem u42_psi_bar_not_inner (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) (A : ↥(primeFormUnitary h (idGram K n))) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x) :
    primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩ ∉
      inner (primeFormP h (idGram K n)) := by
  intro hin
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP h (idGram K n) _).1 hin
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have e1 := primeFormFieldFactor_psi h hC hn hq (⟨A, φ⟩ : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h hC] (K ≃+* K))
  have e2 := primeFormFieldFactor_psi h hC hn hq (⟨⟨s, s.2.1⟩, 1⟩ : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h hC] (K ≃+* K))
  have e3 : primeFormPsi h hC ⟨⟨s, s.2.1⟩, 1⟩ = primeFormConjHom h (idGram K n) ⟨s, s.2.1⟩ := by
    rw [primeFormPsi_apply, map_one, mul_one]
  rw [e3, ← hs, e1] at e2
  have e4 : φ = 1 := e2
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  apply hc₀
  rw [← hφ c₀, e4]
  rfl


theorem u42_psu_bar {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 3 f K) (hn : 3 ≤ n)
    (A : ↥(primeFormUnitary h (idGram K n))) (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K))
      ⟨A, φ⟩) = 2)
    {J : Subgroup ↥(fixedSubgroup (primeFormPsi h
      (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩))}
    (hJ : U42Hyp (primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K))
      ⟨A, φ⟩) J) :
    n = 4 ∧ f = 1 ∧ ∃ g : ↥(primeFormUnitary h (idGram K n)),
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = -1 ∧
      primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩ *
          primeFormConjHom h (idGram K n) g =
        primeFormConjHom h (idGram K n) g *
          primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hfpos := h.one_le
  have hq : ¬(n = 3 ∧ 3 ^ f = 2) := fun h3 => by
    have := h3.2
    have h4 : 3 ≤ 3 ^ f := Nat.le_self_pow (by omega) 3
    omega
  have hout := u42_psi_bar_not_inner h hn hq A φ hφ
  have hF25920 := hJ.card_outer hout
  have hx2 : primeFormPsi h hC (⟨A, φ⟩ * ⟨A, φ⟩) = 1 := by
    rw [map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hx2
  have hmapA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar :=
    Matrix.ext fun i j => hφ _
  have hAc : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = (c : K) • 1 := by
    have h1 : (A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := hc
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmapA] at h2
    rw [h2, Matrix.smul_one_eq_diagonal]
    rfl
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hτ₀def
  have hτ₀ : Function.Bijective τ₀ :=
    CFSG.ComponentClassification.CatLeafProof.OddInner.semilinearMatrixMap_bijective_of h
      c.ne_zero hAc
  have hτ₀B := CFSG.ComponentClassification.CatLeafProof.OddInner.idForm_semilinearMatrixMap h A.2
  have hμ : ∀ v, τ₀ (τ₀ v) = (c : K) • v :=
    CFSG.ComponentClassification.CatLeafProof.OddInner.semilinearMatrixMap_sq_of h hAc
  have hfin : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hnV : 1 ≤ Module.finrank K (Fin n → K) := by omega
  have hodd : Odd 3 := ⟨1, by norm_num⟩
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hnV (idForm_isSymm h n) (idForm_separatingLeft h n) τ₀ hτ₀ hτ₀B c hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = 3 ^ f := h.card_fixedField
  have hfinn : Module.finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = n := hfinW.trans hfin
  obtain ⟨e, ι, he, hι, heq⟩ := u42_psu_bar_eq h hn A φ hφ
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h (by norm_num) h1
  have hrc : ringChar h.fixedField ≠ 2 := fun h0 => by
    apply h2
    haveI : CharP h.fixedField 2 := ringChar.of_eq h0
    simpa using CharP.cast_eq_zero h.fixedField 2
  rcases hμ1 with hμ1 | hμ1
  ·
    exfalso
    obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have hQ : (CFSG.ComponentClassification.CatalogueBOrthogonalDescent.originalQuadratic
        B').polarBilin.Nondegenerate := by
      rw [CFSG.ComponentClassification.CatalogueBOrthogonalDescent.originalQuadratic_polarBilin
        B' hsym h2]
      exact hnd
    let Φ' := Φ.trans (MulEquiv.subgroupCongr
      (CFSG.ComponentClassification.CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2))
    rw [Nat.card_congr Φ'.toEquiv, hF25920] at heq
    rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hdim : Module.finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = 2 * (m' + 1) := by
        rw [hfinn, hm]
      rw [hm] at he
      rcases u42_card_O_even hkc hQ hdim with h1 | h1
      · rw [h1] at heq
        exact u42_arith_bar_orth_even_plus hfpos (by omega) hι he heq
      · rw [h1] at heq
        exact u42_arith_bar_orth_even_minus hfpos (by omega) hι he heq
    · have hdim : Module.finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = 2 * m + 1 := by
        rw [hfinn, hm]
      rw [hm] at he
      rw [u42_card_O_odd hkc hrc hQ hdim] at heq
      exact u42_arith_bar_orth_odd hfpos (by omega) hι he heq
  ·
    obtain ⟨B', -, halt, hnd, hEven, Φ, -⟩ := hB2 hμ1
    obtain ⟨m, hm⟩ := hEven
    rw [hfin] at hm
    have hdim : Module.finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = 2 * m := by
      rw [hfinn]; omega
    rw [Nat.card_congr Φ.toEquiv, u42_card_Sp hkc halt hnd hdim] at heq
    rw [show n = 2 * m by omega] at he
    obtain ⟨rfl, rfl⟩ := u42_arith_bar_sp hfpos (by omega) hι hJ.card_mem he heq
    obtain rfl : n = 4 := by omega
    have hAc' : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar = (-1 : K) • 1 := by
      rw [hAc]
      have := congrArg Units.val hμ1
      rw [Units.val_neg, Units.val_one] at this
      rw [this]
    obtain ⟨g, z, hdet, -, hcomm⟩ := u42_alt_element h A hAc'
    exact ⟨rfl, rfl, g, hdet, u42_psi_comm_conj h A g φ hφ z hcomm⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
