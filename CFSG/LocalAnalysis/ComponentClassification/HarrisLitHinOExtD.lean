module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinOExt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinOPlane
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthPlus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem exists_elemTwo_ext_plus {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (h8 : d = 8) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hU : ∃ U : Submodule K (Fin d → K), finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0)
    (g : similarityPairs Q) {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hτ : ∀ v, coordinateSemilinearMap g.val v = A v) (c μ : Kˣ)
    (hsquare : ∀ x, A (A x) = (c : K) • x)
    (hsim : ∀ x y, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K (Fin d → K)))
    (hnsq : ¬ IsSquare (c : K)) (hμ : (μ : K) / (c : K) = 1) :
    ∃ E' : Subgroup (matrixProjectiveDerived Q),
      E' ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧ ElemTwo E' ∧
        16 ≤ Nat.card E' := by
  classical
  have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk2
  have hdV : finrank K (Fin d → K) = 8 := by rw [Module.finrank_fin_fun, h8]
  obtain ⟨-, hadj0, -, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A c μ hsquare hsim hnonscalar
  have h4 := hns4 hnsq
  have : Nontrivial (Fin d → K) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let : Field (scalarAlgebra A.toLinearMap) := scalarField A.toLinearMap c hnsq
    (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A c hsquare)
  let : Module (scalarAlgebra A.toLinearMap) (Fin d → K) := evaluationModule A.toLinearMap
  obtain ⟨⟨-, hfin, hgen, -, -, hcoord, -, -, hcard, -, -, -, -, -, -, -, hsmul, -, htower,
    hfinE, hfinrank, -⟩, hpos, -⟩ := h4
  obtain ⟨hBEs, -, -, hQEnd, hBE, hQE, eO, -, heO2, -, -⟩ := hpos hμ
  have := hfin
  have : IsScalarTower K (scalarAlgebra A.toLinearMap) (Fin d → K) := htower
  have : FiniteDimensional (scalarAlgebra A.toLinearMap) (Fin d → K) := hfinE
  have hE4 : finrank (scalarAlgebra A.toLinearMap) (Fin d → K) = 4 := by omega
  obtain ⟨U, hU4, hUQ⟩ := hU
  have hμd : (μ : K) = c := (div_eq_one_iff_eq (Units.ne_zero c)).mp hμ
  have hQA : ∀ x, Q (A x) = (c : K) * Q x := by
    intro x
    have h1 := hsim x x
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_self, polar_self, two_smul,
      two_smul, hμd] at h1
    have h3 : (2 : K) * (Q (A x) - (c : K) * Q x) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2)
  have hadj : ∀ x y, Q.polarBilin (A x) y = Q.polarBilin x (A y) := fun x y => by
    rw [hadj0, hμ, one_mul]
  have hE : ∀ z : scalarAlgebra A.toLinearMap, ∃ a b : K,
      z = algebraMap K _ a + algebraMap K _ b * generator A.toLinearMap := by
    intro z
    obtain ⟨⟨a, b⟩, hab, -⟩ := hcoord z
    refine ⟨a, b, ?_⟩
    rw [← hab]
    simp only [coordinateElement, Algebra.smul_def]
  have hcardE : Nat.card (scalarAlgebra A.toLinearMap) = Nat.card K ^ 2 := by rw [hcard, hK]
  have hℓ3 : 3 ≤ ℓ := Nat.lt_of_le_of_ne hℓ.two_le (Ne.symm hℓ2)
  have h9 : 9 ≤ Nat.card (scalarAlgebra A.toLinearMap) := by
    rw [hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ (ℓ ^ e) ^ 2 := Nat.pow_le_pow_left (hℓ3.trans (Nat.le_self_pow (by omega) ℓ)) 2
  have hoddE : Odd (Nat.card (scalarAlgebra A.toLinearMap)) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  obtain ⟨S, hS2, hSQ⟩ := exists_split_of_totallySingular hk2 hcardE hQ hdV (A := A.toLinearMap)
    (Units.ne_zero c) (fun x => hsquare x) hQA hadj (generator A.toLinearMap)
    (fun v => by rw [hsmul, hgen]) hE hBEs hBE hQE hU4 hUQ
  obtain ⟨ψ, eD, -, heD, -⟩ := LocalAnalysis.ComponentInitial.orthogonal_split_four_derived
    (by omega) (by omega) _ hQEnd hE4 ⟨S, hS2, hSQ⟩
  exact exists_elemTwo_of_split_model Q g (by omega) hτ
    (CatFactsSp4.two_ne_zero_of_odd_card hoddE) hoddE (by omega) (by omega) eO heO2 ψ eD heD

theorem exists_elemTwo_ext_minus (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K (Fin d → K)}
    (hQ : (polarBilin Q).Nondegenerate) (hP : ThreePairs Q) (h8 : d = 8)
    (hZ : ∀ x ∈ orthogonalOmega Q, ∀ r : K, (∀ v, x v = r • v) → x = 1)
    (g : similarityPairs Q) {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hτ : ∀ v, coordinateSemilinearMap g.val v = A v) (c μ : Kˣ)
    (hsquare : ∀ x, A (A x) = (c : K) • x)
    (hsim : ∀ x y, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnsq : ¬ IsSquare (c : K)) (hμ : (μ : K) / (c : K) = 1) :
    ∃ E' : Subgroup (matrixProjectiveDerived Q),
      E' ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧ ElemTwo E' ∧
        8 ≤ Nat.card E' := by
  have hμd : (μ : K) = c := (div_eq_one_iff_eq (Units.ne_zero c)).mp hμ
  have hQA : ∀ x, Q (A x) = (c : K) * Q x := by
    intro x
    have h1 := hsim x x
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_self, polar_self, two_smul,
      two_smul, hμd] at h1
    have h3 : (2 : K) * (Q (A x) - (c : K) * Q x) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2)
  have hadj : ∀ x y, polar Q (A x) y = polar Q x (A y) := by
    intro x y
    have h1 := hsim x (A y)
    rw [polarBilin_apply_apply, polarBilin_apply_apply, hsquare, polar_smul_right, hμd,
      smul_eq_mul] at h1
    have h3 : (c : K) * (polar Q (A x) y - polar Q x (A y)) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left (Units.ne_zero c))
  obtain ⟨E, hEΩ, hE2, hE8, hEA⟩ := exists_elemTwo_ext h2 hQ hP
    (by rw [Module.finrank_fin_fun, h8]) hsquare hQA hadj hnsq
  obtain ⟨E', hE', hE'2, hcard⟩ := exists_elemTwo_fix Q g
    (fun x hx => ⟨hEΩ hx, mem_commutant.mpr fun v => by
      rw [hτ, hτ]
      exact LinearEquiv.congr_fun (hEA x hx) v⟩) hE2
    (fun x hx r hr => hZ x (hEΩ hx) r hr)
  exact ⟨E', hE', hE'2, hE8.trans hcard⟩

theorem omega_scalar_trivial_minus (h2 : (2 : K) ≠ 0) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ x ∈ orthogonalOmega (CatalogueBOrthogonalPointData.coordinateQuadMinus 4 K (by norm_num) b c),
      ∀ r : K, (∀ v, x v = r • v) → x = 1 := by
  classical
  set Q' := CatalogueBOrthogonalPointData.coordinateQuadMinus 4 K (by norm_num) b c with hQ'
  set ι := CatalogueBOrthogonalPointData.coordinateMinusIsometry 4 K (by norm_num) b c with hι
  intro x hx r hr
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q' := commutator_le_self _ hx
  obtain ⟨P₁, -, -, -, -, -⟩ := threePairs_coordinateQuadMinus K (n := 4) le_rfl b c
  have hv : Q' (P₁.e + P₁.f) = 1 := by
    rw [QuadraticMap.map_add Q', P₁.Q_e, P₁.Q_f, P₁.polar_ef]
    ring
  have hr2 : r * r = 1 := by
    have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hxO (P₁.e + P₁.f)
    rw [hr, QuadraticMap.map_smul, hv, smul_eq_mul, mul_one] at h1
    exact h1
  rcases mul_self_eq_one_iff.mp hr2 with h | h
  · refine LinearEquiv.ext fun v => ?_
    rw [hr, h, one_smul]
    rfl
  · exfalso
    have hneg : x = LinearEquiv.neg K := LinearEquiv.ext fun v => by
      rw [hr, h, neg_one_smul]
      rfl
    have hmap := CatalogueBOrthogonalPointIsometry.derivedOrthogonal_map_isometry ι
    have hx' : LinearEquiv.neg K ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q',
        TauCeti.QuadraticMap.orthogonalGroup Q'⁆ := hneg ▸ hx
    rw [← hmap] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hy' : y = LinearEquiv.neg K := by
      refine LinearEquiv.ext fun v => ?_
      have h1 := LinearEquiv.congr_fun hyx (ι.toLinearEquiv v)
      rw [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply,
        LinearEquiv.symm_apply_apply] at h1
      apply ι.toLinearEquiv.injective
      rw [h1]
      simp
    have hy2 : LinearEquiv.neg K ∈ elementaryGroup (LieType.Universal.Spin.quadMinus 4 K b c) := by
      rw [← ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus le_rfl hirr, ← hy']
      exact hy
    rw [ClassicalInvolution.neg_mem_elementaryGroup_quadMinus_iff h2 hirr le_rfl] at hy2
    obtain ⟨t, ht⟩ := hy2
    have h5 : t * t = b ^ 2 - 4 * c := by
      norm_num at ht
      linear_combination -ht
    have h4' : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    apply hirr ((t - b) / 2)
    have h7 : (4 : K) * (((t - b) / 2) ^ 2 + b * ((t - b) / 2) + c) = 0 := by
      have e1 : (4 : K) * (((t - b) / 2) ^ 2 + b * ((t - b) / 2) + c) =
          t * t - (b ^ 2 - 4 * c) := by
        field_simp
        ring
      rw [e1, h5, sub_self]
    exact (mul_eq_zero.mp h7).resolve_left h4'

omit [Finite K] in
theorem conjugationHom_not_mem_range {Q : QuadraticForm K (Fin d → K)}
    (hker : ∀ g' : similarityPairs Q, matrixProjectiveConjugationHom Q g' = 1 ↔
      g'.val.right = 1 ∧ ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = g'.val.left)
    (g : similarityPairs Q) {c : K} (hc : ¬ IsSquare c)
    (hQA : ∀ v, Q (coordinateSemilinearMap g.val v) = c * Q v) (hQ0 : ∃ v, Q v ≠ 0) :
    matrixProjectiveConjugationHom Q g ∉
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := matrixProjectiveProjection_surjective Q y
  have hxO : ∀ v, Q (matrixLinearEquiv x.val v) = Q v :=
    (mem_matrixIsometries_iff Q x.val).mp (matrixDerived_le_isometries Q x.2)
  have hxmem : (SemidirectProduct.inl x.val : coordinateSemilinearGroup d K) ∈
      similarityPairs Q := ⟨1, fun v => by
        change Q (matrixLinearEquiv x.val v) = ((1 : Kˣ) : K) * Q v
        rw [Units.val_one, one_mul]
        exact hxO v⟩
  set g' : similarityPairs Q := ⟨_, hxmem⟩ with hg'def
  have hg' : matrixProjectiveConjugationHom Q g' =
      MulAut.conj (matrixProjectiveProjection Q x) := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨X, rfl⟩ := matrixProjectiveProjection_surjective Q z
    change matrixProjectiveConjugation Q g' (matrixProjectiveProjection Q X) = _
    rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have h1 : matrixProjectiveConjugationHom Q (g'⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hg', hy, inv_mul_cancel]
  obtain ⟨hr, a, ha⟩ := (hker _).mp h1
  have hright : g.val.right = 1 := by
    have : (g'⁻¹ * g).val.right = g.val.right := by
      change (g'.val⁻¹ * g.val).right = g.val.right
      rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
      change (1 : K ≃+* K)⁻¹ * g.val.right = g.val.right
      rw [inv_one, one_mul]
    rw [← this]
    exact hr
  have hleft : g.val.left = x.val * GeneralLinearGroup.scalar (Fin d) a := by
    have : (g'⁻¹ * g).val.left = x.val⁻¹ * g.val.left := by
      change (g'.val⁻¹ * g.val).left = _
      rw [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.inv_right]
      change CatalogueBHigherLinearField.glFieldAut (Fin d) K 1⁻¹ x.val⁻¹ *
        CatalogueBHigherLinearField.glFieldAut (Fin d) K 1⁻¹ g.val.left = _
      rw [inv_one, map_one, MulAut.one_apply, MulAut.one_apply]
    rw [this] at ha
    rw [ha, mul_inv_cancel_left]
  obtain ⟨v, hv⟩ := hQ0
  apply hc
  refine ⟨(a : K), ?_⟩
  have h3 := hQA v
  have h4 : coordinateSemilinearMap g.val v = matrixLinearEquiv x.val ((a : K) • v) := by
    rw [coordinateSemilinearMap_apply, hright]
    change matrixLinearEquiv g.val.left v = _
    rw [hleft, matrixLinearEquiv_mul, LinearEquiv.mul_apply,
      LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar]
  rw [h4, hxO, QuadraticMap.map_smul, smul_eq_mul] at h3
  have h5 : ((a : K) * a - c) * Q v = 0 := by linear_combination h3
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right hv)).symm

end CFSG.ComponentClassification.HarrisLit.Hin
