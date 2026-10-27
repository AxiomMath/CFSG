module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCOmLin
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OC

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare QuaternionMatrices
open CFSG.ComponentClassification CatalogueBOrthogonalSemilinear
  CatalogueBOrthogonalInvolutionRepresentation CatalogueBOrthogonalPointData
  CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent CatalogueBHigherLinearField
  CatalogueBOrthogonalScalarSquare CatalogueBOrthogonalScalarSquareField
  CatalogueBOrthogonalScalarSquareForms

theorem omWit_scalar_square {K V : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hd : 7 ≤ finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (a μ : Kˣ)
    (hsq : ∀ x, A (A x) = (a : K) • x)
    (hsim : ∀ x y, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hns : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    OmWit Q (Subgroup.centralizer {A}) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK' : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hε, -, hsqcase, hnscase⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure (ringChar K) n
      hℓ hK n.pos hK' (by omega) Q hQ A a μ hsq hsim hns
  by_cases hsqa : IsSquare (a : K)
  · obtain ⟨b, hb⟩ := hsqa
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hb
      exact a.ne_zero hb
    obtain ⟨hc, hP, hM, h1, h2⟩ := hsqcase (Units.mk0 b hb0) (by rw [Units.val_mk0, hb, pow_two])
    rcases hε with hε | hε
    · obtain ⟨-, hNp, hNm, e, -, -, he⟩ := h1 hε
      exact omWit_split hK hc hP hM hd hNp hNm e he
    · obtain ⟨-, -, -, -, hpd, -, e, -, -, -, he, -⟩ := h2 hε
      exact omWit_paired hK (by omega) e he
  · let _ : Field (scalarAlgebra A.toLinearMap) :=
      scalarField A.toLinearMap (a : K) hsqa
        (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A (a : K) hsq)
    let _ : Module (scalarAlgebra A.toLinearMap) V := evaluationModule A.toLinearMap
    obtain ⟨⟨-, hFinE, -, -, -, -, -, -, hcardE, -, -, -, -, -, hconj, hfixE, -, -, hST, hFin, hfr,
      -⟩, hc1, hc2⟩ := hnscase hsqa
    have : Finite (scalarAlgebra A.toLinearMap) := hFinE
    have : IsScalarTower K (scalarAlgebra A.toLinearMap) V := hST
    have : FiniteDimensional (scalarAlgebra A.toLinearMap) V := hFin
    have hmE : 3 ≤ finrank (scalarAlgebra A.toLinearMap) V := by omega
    rcases hε with hε | hε
    · obtain ⟨-, -, -, hQEn, -, -, e, -, he, -, -⟩ := hc1 hε
      exact omWit_field_orth hK hmE hQEn e he
    · obtain ⟨hhs, hhn, -, -, -, -, e, -, he, -, -⟩ := hc2 hε
      have hUF : UnitaryFieldData (ringChar K) n (scalarAlgebra A.toLinearMap) :=
        ⟨hℓ, n.pos, by rw [hcardE, ← pow_mul, mul_comm]⟩
      exact omWit_field_unitary hK hmE hUF hhs hhn (fun z => (hfixE _).2 ⟨z, rfl⟩) e he hconj

theorem omWit_semilinear {K V : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hd : 7 ≤ finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1)
    (hσ : σ ≠ 1) (τ₀ : V ≃+ V) (μ l : Kˣ) (hsemi : ∀ (a : K) x, τ₀ (a • x) = σ a • τ₀ x)
    (hform : ∀ x y, Q.polarBilin (τ₀ x) (τ₀ y) = (μ : K) * σ (Q.polarBilin x y))
    (hsquare : ∀ x, τ₀ (τ₀ x) = (l : K) • x) :
    OmWit Q (commutant τ₀) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsym := OddOrthogonal.isSymm_polarBilin Q
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_orthogonal_quadratic_semilinear_descent σ hσ2 hσ
    h2 (by omega) Q.polarBilin hsym hQ τ₀ μ l hsemi hform hsquare
  obtain ⟨-, -, hTsemi, hW, hfin, hrank, -, hB0n, -, -, hQ0pol, -, j, e, -, -, -, -, he, -, -,
    -⟩ := hall b c hb hc
  have h2k : ringChar (fixedSubfield K σ) ≠ 2 := fun h => by
    have hc2 := ringChar.Nat.cast_ringChar (R := fixedSubfield K σ)
    rw [h] at hc2
    apply h2
    have h3 := map_natCast (fixedSubfield K σ).subtype 2
    rw [hc2, map_zero] at h3
    exact_mod_cast h3.symm
  obtain ⟨ψk, hψk, hψks⟩ := exists_sl2_orth h2k
    (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c hform hc)
    (by rw [hQ0pol]; exact hB0n) (by rw [hrank]; omega)
  let Φ := e.symm.toMonoidHom.comp (ψk.codRestrict _ hψk)
  have hcomm : ∀ (g : semilinearOrthogonalCentralizer (originalQuadratic Q.polarBilin) τ₀) x,
      g.val.val (τ₀ x) = τ₀ (g.val.val x) := fun g x => by
    have h := Subgroup.mem_centralizer_singleton_iff.1 g.prop
    exact congrArg (fun f : Equiv.Perm V => f x) h
  obtain ⟨hS, hSo⟩ := elementary_closure_odd h2k 2
  refine ⟨SpecialLinearGroup (Fin 2) (fixedSubfield K σ), inferInstance,
    LinearGroups.elementarySet 2 _, (TauCeti.QuadraticMap.orthogonalGroup _).subtype.comp
    ((semilinearOrthogonalCentralizer _ τ₀).subtype.comp Φ), hS, hSo, fun X => ?_,
    fun X => mem_commutant.2 (hcomm (Φ X)), slQuatI _, slQuatI_pow_four, fun a h => ?_⟩
  · refine (TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar
      (IsSMulRegular.of_ne_zero h2)).2 fun x y => ?_
    exact (originalQuadratic_isometry_iff Q.polarBilin hsym h2 _).1 (Φ X).val.prop x y
  · obtain ⟨w, hw⟩ := exists_ne_of_notScalar hψks
    have hact : ∀ v : originalFixedSubspace σ τ₀ b hsemi,
        ((ψk (slQuatI _) v : originalFixedSubspace σ τ₀ b hsemi) : V) = a • (v : V) :=
      fun v => by
        have h1 := he (ψk.codRestrict _ hψk (slQuatI _)) 1 v
        rw [one_smul, one_smul] at h1
        exact h1.symm.trans (LinearMap.congr_fun h (v : V))
    have hwne : w ≠ 0 := fun h0 => hw (by rw [h0, map_zero])
    have hσa : σ a = a := by
      have h1 := (hW (a • (w : V))).1 (by rw [← hact w]; exact (ψk (slQuatI _) w).2)
      have h2' := (hW (w : V)).1 w.2
      rw [hsemi, smul_comm, h2'] at h1
      have h3 : (σ a - a) • (w : V) = 0 := by rw [sub_smul, h1, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right fun h0 => hwne (Subtype.ext h0))
    exact hψks ⟨a, (mem_fixedSubfield K σ a).2 hσa⟩ (LinearMap.ext fun v => Subtype.ext
      (hact v))

section Cases

variable {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {d : ℕ} (hd : 7 ≤ d)
  (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
include hK hd hQ

theorem exists_odd_linear_coordinate (g : similarityPairs Q) (hg1 : g.val.right = 1) (c : Kˣ)
    (hc : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c)
    (hns : ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left) :
    ∃ T : Set (matrixProjectiveDerived Q),
      (∀ t ∈ T, matrixProjectiveConjugationHom Q g t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
  have hd0 : 0 < d := by omega
  set A := matrixLinearEquiv g.val.left with hAdef
  have hτ : ∀ v, coordinateSemilinearMap g.val v = A v := fun v => by
    rw [coordinateSemilinearMap_apply, hg1]
    rfl
  rw [hg1, map_one] at hc
  have hsq : ∀ x, A (A x) = (c : K) • x := fun x => by
    have h1 : A (A x) = matrixLinearEquiv (g.val.left * g.val.left) x := by
      rw [matrixLinearEquiv_mul]
      rfl
    rw [h1, show g.val.left * g.val.left = GeneralLinearGroup.scalar (Fin d) c from hc]
    exact matrixLinearEquiv_scalar c x
  have hQA : ∀ v, Q (A v) = (multiplier Q g : K) * Q v := fun v => by
    rw [← hτ, multiplier_spec, hg1]
    rfl
  have hsim : ∀ x y, Q.polarBilin (A x) (A y) = (multiplier Q g : K) * Q.polarBilin x y := by
    intro x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← map_add A x y, hQA,
      hQA, hQA]
    ring
  have hAns : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K (Fin d → K)) := fun a h => by
    have hv : ∀ v, A v = a • v := fun v => LinearMap.congr_fun h v
    have ha : a ≠ 0 := by
      rintro rfl
      have h0 := hv (Pi.single ⟨0, hd0⟩ 1)
      rw [zero_smul, LinearEquiv.map_eq_zero_iff] at h0
      simpa using congrFun h0 ⟨0, hd0⟩
    refine hns (Units.mk0 a ha) (matrixLinearIso.injective (LinearEquiv.ext fun v => ?_))
    change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 a ha)) v = A v
    rw [hv]
    exact matrixLinearEquiv_scalar _ v
  obtain ⟨T, hT, hTo, hT2⟩ := exists_odd_of_omWit hK hQ (omWit_scalar_square hK
    (by rw [Module.finrank_fin_fun]; exact hd) Q hQ A c (multiplier Q g) hsq hsim hAns)
  have hW := map_le_fixed Q hd0 g (C := Subgroup.centralizer {A}) (fun u hu v => by
    rw [hτ, hτ]
    exact LinearEquiv.congr_fun (Subgroup.mem_centralizer_singleton_iff.1 hu) v)
    (W := closure T) ((closure_le _).2 hT)
  refine ⟨(projEquiv Q hd0).symm.toMonoidHom '' T, fun t ht => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨t', ht', rfl⟩ := ht
    exact hW ⟨t', subset_closure ht', rfl⟩
  · obtain ⟨t', ht', rfl⟩ := ht
    change Odd (orderOf ((projEquiv Q hd0).symm t'))
    rw [MulEquiv.orderOf_eq]
    exact hTo t' ht'
  · rw [← MonoidHom.map_closure, Subgroup.card_map_of_injective
      (f := (projEquiv Q hd0).symm.toMonoidHom) (projEquiv Q hd0).symm.injective]
    exact hT2

theorem exists_odd_semilinear_coordinate (g : similarityPairs Q) (hg2 : g.val.right ^ 2 = 1)
    (hg1 : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c) :
    ∃ T : Set (matrixProjectiveDerived Q),
      (∀ t ∈ T, matrixProjectiveConjugationHom Q g t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
  have hd0 : 0 < d := by omega
  have hsemi : ∀ (a : K) x, coordinateSemilinearMap g.val (a • x) =
      g.val.right a • coordinateSemilinearMap g.val x := coordinateSemilinearMap_smul g.val
  have hQτ := multiplier_spec Q g
  have hform : ∀ x y, Q.polarBilin (coordinateSemilinearMap g.val x)
      (coordinateSemilinearMap g.val y) =
        (multiplier Q g : K) * g.val.right (Q.polarBilin x y) := by
    intro x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar,
      ← map_add (coordinateSemilinearMap g.val) x y, hQτ, hQτ, hQτ, map_sub, map_sub]
    ring
  have hsquare : ∀ x, coordinateSemilinearMap g.val (coordinateSemilinearMap g.val x) =
      (c : K) • x := fun x => by
    rw [← coordinateSemilinearMap_mul, coordinateSemilinearMap_apply,
      coordinateSemilinearGroup_mul_matrix, hc, coordinateSemilinearGroup_mul_field, ← pow_two, hg2]
    exact matrixLinearEquiv_scalar c x
  obtain ⟨T, hT, hTo, hT2⟩ := exists_odd_of_omWit hK hQ (omWit_semilinear hK
    (by rw [Module.finrank_fin_fun]; exact hd) Q hQ g.val.right hg2 hg1
    (coordinateSemilinearMap g.val) (multiplier Q g) c hsemi hform hsquare)
  have hW := map_le_fixed Q hd0 g (C := commutant (coordinateSemilinearMap g.val))
    (fun u hu v => mem_commutant.1 hu v) (W := closure T) ((closure_le _).2 hT)
  refine ⟨(projEquiv Q hd0).symm.toMonoidHom '' T, fun t ht => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨t', ht', rfl⟩ := ht
    exact hW ⟨t', subset_closure ht', rfl⟩
  · obtain ⟨t', ht', rfl⟩ := ht
    change Odd (orderOf ((projEquiv Q hd0).symm t'))
    rw [MulEquiv.orderOf_eq]
    exact hTo t' ht'
  · rw [← MonoidHom.map_closure, Subgroup.card_map_of_injective
      (f := (projEquiv Q hd0).symm.toMonoidHom) (projEquiv Q hd0).symm.injective]
    exact hT2

end Cases

theorem exists_fixed_odd_coordinate {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {d : ℕ} (hd : 7 ≤ d) (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hrep : SemilinearRepresentation Q) (α : MulAut (matrixProjectiveDerived Q))
    (hα : α * α = 1) (h1 : α ≠ 1) :
    ∃ T : Set (matrixProjectiveDerived Q), (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
  obtain ⟨β, g, hβ, hg2, ⟨c, hc⟩, hlin, -⟩ := hrep.2 α hα h1
  have hT : ∃ T : Set (matrixProjectiveDerived Q),
      (∀ t ∈ T, matrixProjectiveConjugationHom Q g t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
    by_cases hg1 : g.val.right = 1
    · exact exists_odd_linear_coordinate hK hd Q hQ g hg1 c hc (hlin hg1)
    · exact exists_odd_semilinear_coordinate hK hd Q hQ g hg2 hg1 c hc
  exact exists_fixed_odd_conj (γ := β) (by rw [← hβ]; group) hT

theorem not_isPGroup_fixedPoints_of_statedOrthogonalModel
    {Y : Type} [Group Y] [Finite Y]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hp2 : p ≠ 2)
    (hmodel : CFSG.Open.StatedClassicalModel Y t n p f)
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(CFSG.ComponentClassification.HarrisLit.fixedPoints a) ⧸
      CFSG.pPrimeCore 2 ↥(CFSG.ComponentClassification.HarrisLit.fixedPoints a)) := by
  intro hP
  have hrep := odd_orthogonal_involution_semilinear_representation t ht hmodel
  have finish : ∀ {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)),
      ringChar K = p → 7 ≤ d → Q.polarBilin.Nondegenerate → SemilinearRepresentation Q →
      (Y ≃* matrixProjectiveDerived Q) → False := by
    intro K _ _ d Q hchar hd hQ hrepQ ψ
    have : Finite (matrixProjectiveDerived Q) := Finite.of_equiv _ ψ.toEquiv
    have hα2 : MulAut.congr ψ a * MulAut.congr ψ a = 1 := by
      rw [← map_mul, ← _root_.sq, ← ha, pow_orderOf_eq_one, map_one]
    have hα1 : MulAut.congr ψ a ≠ 1 := fun h => by
      have h1 : a = 1 := (MulAut.congr ψ).injective (h.trans (map_one _).symm)
      rw [h1, orderOf_one] at ha
      exact absurd ha (by decide)
    exact not_isPGroup_of_fixed_odd
      (exists_fixed_odd_coordinate (by rw [hchar]; exact hp2) hd Q hQ hrepQ _ hα2 hα1)
      (L33.isPGroup_fixedPoints_congr ψ a hP)
  rcases ht with rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel.2
    obtain ⟨hchar, hQ, -⟩ := coordinate_model_witness_odd hmodel K hK e
    exact (finish _ hchar (by have := hmodel.1.2.2.1; omega) hQ (hrep K hK e)
      (coordinateOddWitnessEquiv K e)).elim
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel.2
    obtain ⟨hchar, hQ, -⟩ := coordinate_model_witness_plus hmodel K hK e
    exact (finish _ hchar (by have := hmodel.1.2.2; omega) hQ (hrep K hK e)
      (coordinatePlusWitnessEquiv K e)).elim
  · obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmodel.2
    have hn : 1 ≤ n := by have := hmodel.1.2.2; omega
    obtain ⟨hchar, hQ, -⟩ := coordinate_model_witness_minus hmodel K hK b c hirr e
    exact (finish _ hchar (by have := hmodel.1.2.2; omega) hQ (hrep hn K hK b c hirr e)
      (coordinateMinusWitnessEquiv K hn b c e)).elim

theorem oddClsRow_orth (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) : OddClsRow t := by
  intro Y _ _ hY _ _ a ha hP
  obtain ⟨n, p, f, hp2, hL⟩ := hY
  exact (not_isPGroup_fixedPoints_of_statedOrthogonalModel ht hp2 hL a ha hP).elim

theorem twoNilpFor_odd :
    TwoNilpFor fun Y _ => ∃ t n p f, p ≠ 2 ∧ StatedClassicalModel Y t n p f :=
  twoNilpFor_odd_of_orth (oddClsRow_orth _ (Or.inl rfl)) (oddClsRow_orth _ (Or.inr (Or.inl rfl)))
    (oddClsRow_orth _ (Or.inr (Or.inr rfl)))

end CFSG.ComponentClassification.HarrisLit.L33.OC
