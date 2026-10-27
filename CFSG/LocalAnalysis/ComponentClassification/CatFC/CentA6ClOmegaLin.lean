module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaLow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.RankThree.PartOne.K159.RowFourType
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSU

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.GroupTheory.WeirSylow (IsPlusType isPlusType_congr)

section Sum

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable def omegaSumIsometry (Q : QuadraticForm K V) (W₁ W₂ : Submodule K V)
    (hc : IsCompl W₁ W₂) (horth : ∀ x ∈ W₁, ∀ y ∈ W₂, QuadraticMap.polar Q x y = 0) :
    Q.IsometryEquiv ((Q.comp W₁.subtype).prod (Q.comp W₂.subtype)) where
  toLinearEquiv := (Submodule.prodEquivOfIsCompl W₁ W₂ hc).symm
  map_app' v := by
    obtain ⟨⟨x, y⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W₁ W₂ hc).surjective v
    have h : ((Submodule.prodEquivOfIsCompl W₁ W₂ hc (x, y) : V)) = (x : V) + y := by
      rw [Submodule.coe_prodEquivOfIsCompl']
    change ((Q.comp W₁.subtype).prod (Q.comp W₂.subtype))
      ((Submodule.prodEquivOfIsCompl W₁ W₂ hc).symm
        ((Submodule.prodEquivOfIsCompl W₁ W₂ hc) (x, y))) = _
    rw [LinearEquiv.symm_apply_apply, h, QuadraticMap.map_add Q (x : V) (y : V),
      horth _ x.2 _ y.2, add_zero]
    rfl

theorem omega_isPlusType_iff (Q : QuadraticForm K V) (W₁ W₂ : Submodule K V)
    (hc : IsCompl W₁ W₂) (horth : ∀ x ∈ W₁, ∀ y ∈ W₂, QuadraticMap.polar Q x y = 0)
    (h₁ : (Q.comp W₁.subtype).polarBilin.Nondegenerate)
    (h₂ : (Q.comp W₂.subtype).polarBilin.Nondegenerate) {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁)
    (hd₂ : 1 ≤ d₂) (hdim₁ : finrank K W₁ = 2 * d₁) (hdim₂ : finrank K W₂ = 2 * d₂) :
    IsPlusType Q ↔ (IsPlusType (Q.comp W₁.subtype) ↔ IsPlusType (Q.comp W₂.subtype)) :=
  (isPlusType_congr (omegaSumIsometry Q W₁ W₂ hc horth)).trans
    (CFSG.RankThree.PartOne.K159.isPlusType_prod_iff h₁ h₂ hd₁ hd₂ hdim₁ hdim₂)

end Sum

section ClassI

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_polarBilin_comp_nondeg {Q : QuadraticForm K V} {W : Submodule K V}
    (h : (LinearMap.BilinForm.restrict Q.polarBilin W).Nondegenerate) :
    (Q.comp W.subtype).polarBilin.Nondegenerate := by
  have heq : (Q.comp W.subtype).polarBilin = LinearMap.BilinForm.restrict Q.polarBilin W := by
    rw [QuadraticMap.polarBilin_comp]
    ext x y
    rfl
  rw [heq]
  exact h

theorem omega_classI {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V))
    (b : Kˣ) (hb : (c : K) = (b : K) ^ 2) (hpos : (μ : K) / (c : K) = 1)
    (hd : 7 ≤ finrank K V) :
    OmegaObstruction ↥(orthogonalOperatorCentralizer Q A.toLinearMap) ∨
      Group.IsSolvable ↥(orthogonalOperatorCentralizer Q A.toLinearMap) ∨
      (f = 1 ∧ (finrank K V = 7 ∨ (finrank K V = 8 ∧ ¬ IsPlusType Q))) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left (by norm_num)).pow
  obtain ⟨-, -, hsq, -⟩ := CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure
    3 f Nat.prime_three (by norm_num) hf hK (by omega) Q hQ A c μ hsquare hsim hnonscalar
  obtain ⟨hcompl, -, -, hpos', -⟩ := hsq b hb
  obtain ⟨horth, hnd₁, hnd₂, e, -, -, -⟩ := hpos' hpos
  set V₁ := positiveSquareKernel A (b : K) with hV₁
  set V₂ := negativeSquareKernel A (b : K) with hV₂
  have hnd₁' := omega_polarBilin_comp_nondeg hnd₁
  have hnd₂' := omega_polarBilin_comp_nondeg hnd₂
  have hdimsum : finrank K V₁ + finrank K V₂ = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  let ι₁ : TauCeti.QuadraticMap.orthogonalGroup (Q.comp V₁.subtype) →*
      ↥(orthogonalOperatorCentralizer Q A.toLinearMap) :=
    e.symm.toMonoidHom.comp (MonoidHom.inl _ _)
  let ι₂ : TauCeti.QuadraticMap.orthogonalGroup (Q.comp V₂.subtype) →*
      ↥(orthogonalOperatorCentralizer Q A.toLinearMap) :=
    e.symm.toMonoidHom.comp (MonoidHom.inr _ _)
  have hι₁ : Function.Injective ι₁ :=
    e.symm.injective.comp (fun a a' h => (Prod.mk.inj h).1)
  have hι₂ : Function.Injective ι₂ :=
    e.symm.injective.comp (fun a a' h => (Prod.mk.inj h).2)
  by_cases hf2 : 2 ≤ f
  · have h4 : 4 ≤ finrank K V₁ ∨ 4 ≤ finrank K V₂ := by omega
    rcases h4 with h4 | h4
    · exact Or.inl ((omega_obstruction_four hf2 hK _ hnd₁' h4).of_injective ι₁ hι₁)
    · exact Or.inl ((omega_obstruction_four hf2 hK _ hnd₂' h4).of_injective ι₂ hι₂)
  · have hf1 : f = 1 := by omega
    by_cases h5 : 5 ≤ finrank K V₁ ∨ 5 ≤ finrank K V₂
    · rcases h5 with h5 | h5
      · exact Or.inl ((omega_obstruction_five hf hK _ hnd₁' h5).of_injective ι₁ hι₁)
      · exact Or.inl ((omega_obstruction_five hf hK _ hnd₂' h5).of_injective ι₂ hι₂)
    · push Not at h5
      have h78 : finrank K V = 7 ∨ finrank K V = 8 := by omega
      rcases h78 with h7 | h8
      · exact Or.inr (Or.inr ⟨hf1, Or.inl h7⟩)
      by_cases hplus : IsPlusType Q
      swap
      · exact Or.inr (Or.inr ⟨hf1, Or.inr ⟨h8, hplus⟩⟩)
      have h41 : finrank K V₁ = 4 := by omega
      have h42 : finrank K V₂ = 4 := by omega
      have horth' : ∀ x ∈ V₁, ∀ y ∈ V₂, QuadraticMap.polar Q x y = 0 := fun x hx y hy => by
        simpa using horth x hx y hy
      have htype := omega_isPlusType_iff Q V₁ V₂ hcompl horth' hnd₁' hnd₂' (d₁ := 2) (d₂ := 2)
        (by norm_num) (by norm_num) (by omega) (by omega)
      by_cases hp₁ : IsPlusType (Q.comp V₁.subtype)
      ·
        have hp₂ : IsPlusType (Q.comp V₂.subtype) := (htype.mp hplus).mp hp₁
        have hK3 : Nat.card K = 3 := by rw [hK, hf1]; norm_num
        have hsol : ∀ (W : Submodule K V), finrank K W = 4 → IsPlusType (Q.comp W.subtype) →
            (Q.comp W.subtype).polarBilin.Nondegenerate →
            Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)) := by
          intro W hW hpW hndW
          obtain ⟨S, hS, hSQ⟩ := hpW
          exact ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_four_split_p_components_frontier
            hodd (Q.comp W.subtype) hndW hW ⟨S, by omega, hSQ⟩).2 hK3).1
        have h1 := hsol V₁ h41 hp₁ hnd₁'
        have h2 := hsol V₂ h42 hp₂ hnd₂'
        exact Or.inr (Or.inl (solvable_of_solvable_injective (f := e.toMonoidHom) e.injective))
      ·
        have hp₂ : ¬ IsPlusType (Q.comp V₂.subtype) := fun h => hp₁ ((htype.mp hplus).mpr h)
        have hmodel : ∀ (W : Submodule K V), finrank K W = 4 → ¬ IsPlusType (Q.comp W.subtype) →
            (Q.comp W.subtype).polarBilin.Nondegenerate →
            IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype))) ∧
              OddLieCentralQuotient 3
                (commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype))) := by
          intro W hW hpW hndW
          obtain ⟨hq, hadm, hlie⟩ := omega_nonsplit_four_model Nat.prime_three (by norm_num) hf
            hK (Q.comp W.subtype) hndW hW (fun ⟨S, hS, hSQ⟩ => hpW ⟨S, by omega, hSQ⟩)
          exact ⟨hq, .PSL, 2, 2 * f, hadm, hlie⟩
        obtain ⟨hq₁, m₁⟩ := hmodel V₁ h41 hp₁ hnd₁'
        obtain ⟨hq₂, m₂⟩ := hmodel V₂ h42 hp₂ hnd₂'
        refine Or.inl (Or.inr ⟨_, _, inferInstance, inferInstance,
          ι₁.comp (commutator _).subtype, ι₂.comp (commutator _).subtype, hq₁, hq₂,
          hι₁.comp (Subgroup.subtype_injective _), hι₂.comp (Subgroup.subtype_injective _),
          ?_, m₁, m₂⟩)
        intro x y
        change e.symm ((x.val, 1)) * e.symm ((1, y.val)) = e.symm ((1, y.val)) * e.symm ((x.val, 1))
        rw [← map_mul, ← map_mul]
        simp

end ClassI

section ClassII

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_sl_model {k : Type} [Field k] [Finite k] {p j n : ℕ}
    (hadm : StatedLieAdmissible .PSL n p j) (hk : Nat.card k = p ^ j) :
    Blueprint.LieModel (Matrix.SpecialLinearGroup (Fin n) k ⧸
      center (Matrix.SpecialLinearGroup (Fin n) k)) .PSL n p j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact Or.inl ⟨by decide,
    LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m k hadm hk⟩

theorem omega_classII {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V))
    (b : Kˣ) (hb : (c : K) = (b : K) ^ 2) (hneg : (μ : K) / (c : K) = -1)
    (hd : 7 ≤ finrank K V) :
    OmegaObstruction ↥(orthogonalOperatorCentralizer Q A.toLinearMap) := by
  obtain ⟨-, -, hsq, -⟩ := CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure
    3 f Nat.prime_three (by norm_num) hf hK (by omega) Q hQ A c μ hsquare hsim hnonscalar
  obtain ⟨hcompl, -, -, -, hneg'⟩ := hsq b hb
  obtain ⟨-, -, -, hdeq, -, -, e, dual, -, -, -, -⟩ := hneg' hneg
  have hdimsum : finrank K (positiveSquareKernel A (b : K)) +
      finrank K (negativeSquareKernel A (b : K)) = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  have hm : 4 ≤ finrank K (positiveSquareKernel A (b : K)) := by omega
  let eGL := e.trans (CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Module.finBasis K (positiveSquareKernel A (b : K))))
  set m := finrank K (positiveSquareKernel A (b : K)) with hmdef
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple m K (by omega)
    (Or.inl (by omega)) (Or.inl (by omega))
  have hadm : StatedLieAdmissible .PSL m 3 f :=
    ⟨Nat.prime_three, hf, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  refine Or.inl ⟨Matrix.SpecialLinearGroup (Fin m) K, inferInstance,
    eGL.symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL, hSL,
    eGL.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective, .PSL, m, f, hadm,
    omega_sl_model hadm hK, ?_⟩
  rintro ⟨-, h, -⟩
  omega

end ClassII

section Unitary

open CFSG.ComponentClassification.CatalogueBUnitaryIsometry

theorem omega_unitary_obstruction {E W : Type} [Field E] [Finite E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {sigma : E ≃+* E} {e : ℕ} (he : 1 ≤ e)
    (hE : Nat.card E = (3 ^ e) ^ 2) (hW : 3 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (3 ^ e)) :
    OmegaObstruction ↥(isometryGroup h) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP E 3 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hE
  have hE2 : (2 : E) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq E 3]; norm_num)
  have hnq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 2 := by
    intro h2
    have : Fintype (CatalogueBLinearTwoDescent.fixedSubfield E sigma) := Fintype.ofFinite _
    have h0 := FiniteField.cast_card_eq_zero (CatalogueBLinearTwoDescent.fixedSubfield E sigma)
    rw [← Nat.card_eq_fintype_card, h2] at h0
    have h3 := congrArg (CatalogueBLinearTwoDescent.fixedSubfield E sigma).subtype h0
    rw [map_natCast, map_zero] at h3
    exact hE2 (by exact_mod_cast h3)
  have hnq : (finrank E W, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) ≠
      (3, 2) := fun h3 => hnq2 (congrArg Prod.snd h3)
  have hq := specialIsometry_quasisimple_of_three_le h hsym hnd hsigma hne hW hnq
  have hcomm : commutator (isometryGroup h) = specialIsometry h := by
    refine le_antisymm (Abelianization.commutator_subset_ker _) ?_
    calc specialIsometry h = ⁅specialIsometry h, specialIsometry h⁆ :=
          (Subgroup.isPerfect_iff.mp hq.1).symm
      _ ≤ ⁅⊤, ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = _ := (_root_.commutator_def _).symm
  have hY : IsComponent (specialIsometry h) :=
    ⟨hq, hcomm ▸ Subgroup.Normal.isSubnormal inferInstance⟩
  obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu Nat.prime_three (by norm_num) he hE hW h
    hsym hnd hsigma hne hsig hY (MonoidHom.id ↥(specialIsometry h)) Function.surjective_id
    (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
      rw [hx]
      exact one_mem _)
  have hadm : StatedLieAdmissible .PSU (finrank E W) 3 e :=
    ⟨Nat.prime_three, he, hW, fun h' => by
      have := (Prod.mk.inj h').2
      have h3 : 3 ≤ 3 ^ e := Nat.le_self_pow (by omega) 3
      omega⟩
  exact Or.inl ⟨↥(specialIsometry h), inferInstance, (specialIsometry h).subtype, hq,
    Subgroup.subtype_injective _, .PSU, finrank E W, e, hadm,
    Or.inl ⟨by decide, hadm, E, inferInstance, inferInstance, hE, ⟨eX⟩⟩,
    by rintro ⟨h', -, -⟩; exact absurd h' (by decide)⟩

end Unitary

section ClassNonsquare

open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_classIII {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hsq : ¬ IsSquare (c : K)) (hpos : (μ : K) / (c : K) = 1) (hd : 7 ≤ finrank K V) :
    OmegaObstruction ↥(orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left (by norm_num)).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A c hsquare
  let := scalarField A.toLinearMap c hsq hs
  let := evaluationModule A.toLinearMap
  let := scalarAlgebra_finite_type A.toLinearMap c hsq hs
  let := evaluationModule_finite A.toLinearMap
  have hE : Nat.card (scalarAlgebra A.toLinearMap) = 3 ^ (2 * f) := by
    rw [scalarAlgebra_card A.toLinearMap c hsq hs, hK, ← pow_mul, mul_comm]
  have hdimE : finrank K V = 2 * finrank (scalarAlgebra A.toLinearMap) V :=
    evaluationModule_finrank A.toLinearMap c hsq hs
  have hadj := positive_square_adjoint Q A c μ c.ne_zero hsquare hsim hpos
  have hnd := actualPositiveQuadratic_nondegenerate Q A.toLinearMap c c.ne_zero hsq hs hadj hQ h2
  exact (omega_obstruction_four (e := 2 * f) (by omega) hE _ hnd (by omega)).of_mulEquiv
    (actualPositiveCentralizerEquiv Q A.toLinearMap c c.ne_zero hsq hs hadj h2).symm

theorem omega_classIV {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hsq : ¬ IsSquare (c : K)) (hneg : (μ : K) / (c : K) = -1) (hd : 7 ≤ finrank K V) :
    OmegaObstruction ↥(orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left (by norm_num)).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A c hsquare
  let := scalarField A.toLinearMap c hsq hs
  let := evaluationModule A.toLinearMap
  let := scalarAlgebra_finite_type A.toLinearMap c hsq hs
  let := evaluationModule_finite A.toLinearMap
  have hE : Nat.card (scalarAlgebra A.toLinearMap) = (3 ^ f) ^ 2 := by
    rw [scalarAlgebra_card A.toLinearMap c hsq hs, hK]
  have hdimE : finrank K V = 2 * finrank (scalarAlgebra A.toLinearMap) V :=
    evaluationModule_finrank A.toLinearMap c hsq hs
  have hadj := negative_square_adjoint Q A c μ c.ne_zero hsquare hsim hneg
  have hsig : (conjugation A.toLinearMap c hsq hs).toRingEquiv ^ 2 = 1 := by
    apply RingEquiv.ext
    intro z
    change conjugation A.toLinearMap c hsq hs (conjugation A.toLinearMap c hsq hs z) = z
    exact conjugation_involutive A.toLinearMap c hsq hs z
  have hne : (conjugation A.toLinearMap c hsq hs).toRingEquiv ≠ 1 := by
    intro heq
    apply conjugation_ne_one A.toLinearMap c hsq hs h2
    apply AlgEquiv.ext
    intro z
    exact congrArg (fun s : scalarAlgebra A.toLinearMap ≃+* scalarAlgebra A.toLinearMap =>
      s z) heq
  have hpow : ∀ z, (conjugation A.toLinearMap c hsq hs).toRingEquiv z = z ^ (3 ^ f) := by
    intro z
    rw [← hK]
    exact conjugation_eq_card_power A.toLinearMap c hsq hs h2 z
  exact (omega_unitary_obstruction hf hE (by omega) _
    (actualNegativeHermitian_isSymm Q A.toLinearMap c c.ne_zero hsq hs hadj)
    (actualNegativeHermitian_nondegenerate Q A.toLinearMap c c.ne_zero hsq hs hadj hQ)
    hsig hne hpow).of_mulEquiv
    (actualNegativeCentralizerEquiv Q A.toLinearMap c c.ne_zero hsq hs hadj h2).symm

end ClassNonsquare

section Core

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_linear_core {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (hO : LieOrderFormulasInput)
    (Q : QuadraticForm K V) [Finite (projectiveDerived Q)] (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V))
    (hd : 7 ≤ finrank K V)
    {D : Subgroup ↥(fixedSubgroup (projectiveConjugation Q A μ hsim))}
    (hD : A6Hyp (projectiveConjugation Q A μ hsim) D) :
    f = 1 ∧ (finrank K V = 7 ∨ (finrank K V = 8 ∧ ¬ IsPlusType Q)) := by
  have hsimP := polar_similarity Q A μ hsim
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨hsign, -, -, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure 3 f
      Nat.prime_three (by norm_num) hf hK (by omega) Q hQ A c μ hsquare hsimP hnonscalar
  by_cases hsqc : IsSquare (c : K)
  · obtain ⟨r, hr⟩ := hsqc
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by simpa using hr)
    let b : Kˣ := Units.mk0 r hr0
    have hb : (c : K) = (b : K) ^ 2 := by rw [hr, sq]; rfl
    rcases hsign with hpos | hneg
    · rcases omega_classI hf hK Q hQ A c μ hsquare hsimP hnonscalar b hb hpos hd with
        hobs | hsol | hres
      · exact (omega_false_of_obstruction hO hD hobs).elim
      · exact (omega_not_solvable Q A μ hsim hD hsol).elim
      · exact hres
    · exact (omega_false_of_obstruction hO hD
        (omega_classII hf hK Q hQ A c μ hsquare hsimP hnonscalar b hb hneg hd)).elim
  · rcases hsign with hpos | hneg
    · exact (omega_false_of_obstruction hO hD
        (omega_classIII hf hK Q hQ A c μ hsquare hsimP hsqc hpos hd)).elim
    · exact (omega_false_of_obstruction hO hD
        (omega_classIV hf hK Q hQ A c μ hsquare hsimP hsqc hneg hd)).elim

end Core

end CFSG.ComponentClassification.CatFC
