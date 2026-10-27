module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldConjugation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldRigid
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldGalois
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  mem_unitMultiplierPairs_iff evenOrthogonalRealization_of_regular)

variable {K : Type} [Field K] {d : ℕ}

abbrev extKappa {G : Type*} [Group G] (Q : QuadraticForm K (Fin d → K))
    (ext : G →* matrixIsometries Q) : G →* MulAut (matrixProjectiveDerived Q) :=
  (matrixProjectiveConjugationHom Q).comp ((matrixIsometryInclusion Q).comp ext)

@[expose] def EvenOrthogonalFieldCentralizer (Q : QuadraticForm K (Fin d → K)) (f : ℕ) : Prop :=
  ∀ α ∈ matrixProjectiveImage Q, orderOf α = 2 →
  ∀ (S : similarityPairs Q) (hS : S ∈ unitMultiplierPairs Q),
    matrixProjectiveConjugationHom Q S = α → S.val.right ≠ 1 →
    Even f ∧ Nat.card (descentField S.val.right) = 2 ^ (f / 2) ∧
    IsSimpleGroup ↥(pairDescentDerived hS) ∧ Even (Nat.card ↥(pairDescentDerived hS)) ∧
    ∃ ext : ↥(pairDescentDerived hS) →* matrixIsometries Q,
      (∀ (g : pairDescentDerived hS) (w : pairFix S),
        ((ext g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (w : Fin d → K) =
          (((g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) :
            Fin d → K)) ∧
      (∀ (g : pairDescentDerived hS) (A : GL (Fin d) K),
        (∀ w : pairFix S, (A : Matrix (Fin d) (Fin d) K) *ᵥ (w : Fin d → K) =
          (((g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) :
            Fin d → K)) → A = ext g) ∧
      Function.Injective (extKappa Q ext) ∧
      (extKappa Q ext).range ≤
        (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range ∧
      (extKappa Q ext).range ≤ matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} ∧
      ((extKappa Q ext).range.subgroupOf
        (matrixProjectiveImage Q ⊓ Subgroup.centralizer {α})).Normal ∧
      matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} ⊓
          Subgroup.centralizer ((extKappa Q ext).range : Set (MulAut (matrixProjectiveDerived Q)))
        = Subgroup.zpowers α

section Descent

variable {Q : QuadraticForm K (Fin d → K)} {S : similarityPairs Q}
  {hS : S ∈ unitMultiplierPairs Q}
  (e : ↥(pairCentralizer S) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)))

@[expose] def descentExt : ↥(pairDescentDerived hS) →* matrixIsometries Q :=
  (extIsometry e).comp (Subgroup.inclusion (Subgroup.commutator_le_self _))

theorem descentExt_apply (g : pairDescentDerived hS) :
    descentExt e g = extIsometry e ⟨g, Subgroup.commutator_le_self _ g.2⟩ := rfl

theorem inclusion_descentExt_commute (g : pairDescentDerived hS) :
    Commute (matrixIsometryInclusion Q (descentExt e g)) S :=
  inclusion_extIsometry_commute e _

theorem extKappa_le_inn :
    (extKappa Q (descentExt e)).range ≤
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range := by
  rintro _ ⟨g, rfl⟩
  have hgD : extHom e ⟨g, Subgroup.commutator_le_self _ g.2⟩ ∈ matrixDerived Q :=
    extHom_mem_matrixDerived e g.2
  exact ⟨matrixProjectiveProjection Q (⟨_, hgD⟩ : matrixDerived Q),
    (kappa_derived_eq_conj (⟨_, hgD⟩ : matrixDerived Q)).symm⟩

theorem extKappa_commute (g : pairDescentDerived hS) :
    Commute (extKappa Q (descentExt e) g) (matrixProjectiveConjugationHom Q S) :=
  (inclusion_descentExt_commute e g).map (matrixProjectiveConjugationHom Q)

theorem extKappa_le_centralizer :
    (extKappa Q (descentExt e)).range ≤
      matrixProjectiveImage Q ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom Q S} := by
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr (extKappa_commute e g).eq⟩

theorem zpowers_le_centralizer_extKappa :
    Subgroup.zpowers (matrixProjectiveConjugationHom Q S) ≤
      matrixProjectiveImage Q ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom Q S} ⊓
        Subgroup.centralizer
          ((extKappa Q (descentExt e)).range : Set (MulAut (matrixProjectiveDerived Q))) := by
  rw [Subgroup.zpowers_le]
  refine ⟨⟨⟨S, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
    Subgroup.mem_centralizer_iff.mpr ?_⟩
  rintro _ ⟨g, rfl⟩
  exact (extKappa_commute e g).eq

section Regular

variable [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q) (hd : 1 ≤ d)
include hQ hT hE hd

theorem extKappa_injective : Function.Injective (extKappa Q (descentExt e)) :=
  (kappa_inclusion_injective hQ hT hE hd).comp
    ((extIsometry_injective e).comp (Subgroup.inclusion_injective _))

variable [Finite K]

theorem exists_rep_commute (hS' : S ∈ unitMultiplierPairs Q)
    {y : MulAut (matrixProjectiveDerived Q)}
    (hy : y ∈ matrixProjectiveImage Q ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom Q S}) :
    ∃ R : similarityPairs Q, R ∈ unitMultiplierPairs Q ∧
      matrixProjectiveConjugationHom Q R = y ∧ R * S = S * R := by
  have hrep := exists_unit_rep hy.1
  obtain ⟨R, hR, hRy⟩ := hrep
  refine ⟨R, hR, hRy, ?_⟩
  have h1 : R * S * R⁻¹ = S := by
    refine kappa_eq_of_unit hQ hT hE hd (mul_mem (mul_mem hR hS') (inv_mem hR)) hS' ?_
    rw [map_mul, map_mul, map_inv, hRy, Subgroup.mem_centralizer_singleton_iff.mp hy.2,
      mul_inv_cancel_right]
  exact mul_inv_eq_iff_eq_mul.mp h1

omit hd in
theorem extKappa_normal (hd : 1 ≤ d) :
    ((extKappa Q (descentExt e)).range.subgroupOf (matrixProjectiveImage Q ⊓
      Subgroup.centralizer {matrixProjectiveConjugationHom Q S})).Normal := by
  constructor
  intro x hx y
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨g, hg⟩ := hx
  have hy := exists_rep_commute hQ hT hE hd hS y.2
  obtain ⟨R, -, hRy, hRS⟩ := hy
  have hmem := conjDescent_mem hRS e (g := ⟨g, Subgroup.commutator_le_self _ g.2⟩) g.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q
      (extIsometry e (conjDescent hRS e ⟨g, Subgroup.commutator_le_self _ g.2⟩))) =
    (y : MulAut (matrixProjectiveDerived Q)) * x * (y : MulAut (matrixProjectiveDerived Q))⁻¹
  rw [← conjIsometry_extIsometry, ← conj_kappa_inclusion, hRy, ← hg]
  rfl

end Regular

end Descent

section Bound

variable [CharP K 2] [Finite K] {n : ℕ} {Q : QuadraticForm K (Fin (2 * n) → K)}
  (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q) (hd : 1 ≤ 2 * n)
  {S : similarityPairs Q} {hS : S ∈ unitMultiplierPairs Q}
  (e : ↥(pairCentralizer S) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)))
  (he : ∀ g w, (((e g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) :
    Fin (2 * n) → K) = (g : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) w)
  (hspan : Submodule.span K (pairFix S : Set (Fin (2 * n) → K)) = ⊤)
  (hfix : ∀ φ : K ≃+* K, (∀ a ∈ descentField S.val.right, φ a = a) → φ = 1 ∨ φ = S.val.right)
  {Qc : QuadraticForm (descentField S.val.right) (Fin (2 * n) → descentField S.val.right)}
  (ψ : (pairDescentForm hS).IsometryEquiv Qc) (hQc : Qc.polarBilin.Nondegenerate)
  (hTc : ∃ T : Submodule (descentField S.val.right) (Fin (2 * n) → descentField S.val.right),
    Module.finrank (descentField S.val.right) T = 3 ∧ ∀ x ∈ T, Qc x = 0)
  (hEc : ⁅TauCeti.QuadraticMap.orthogonalGroup Qc, TauCeti.QuadraticMap.orthogonalGroup Qc⁆ =
    elementaryGroup Qc)
include hQ hT hE hd he hspan hfix ψ hQc hTc hEc

omit [CharP K 2] [Finite K] hQ hT hE in
theorem eq_one_or_eq_of_commute_descentExt [CharP (descentField S.val.right) 2]
    {R : similarityPairs Q} (hR : R ∈ unitMultiplierPairs Q) (hRS : R * S = S * R)
    (hcomm : ∀ g : pairDescentDerived hS, R * matrixIsometryInclusion Q (descentExt e g) * R⁻¹ =
      matrixIsometryInclusion Q (descentExt e g)) :
    R = 1 ∨ R = S := by
  have hid := semilinear_eq_id_of_commute_derived ψ hQc hTc hEc hd
    (restrictPairFix hRS) (restrictPairFix_quad hRS hR hS) fun g hg w =>
      restrictPairFix_commute hRS e he (g := ⟨g, Subgroup.commutator_le_self _ hg⟩)
        (hcomm ⟨g, hg⟩) w
  obtain ⟨hφ, hρ⟩ := hid
  have hφk : ∀ a ∈ descentField S.val.right, R.val.right a = a := by
    intro a ha
    have h1 := congrArg (fun τ : descentField S.val.right ≃+* descentField S.val.right =>
      ((τ ⟨a, ha⟩ : descentField S.val.right) : K)) hφ
    exact h1
  have hRW : ∀ x ∈ (pairFix S : Set (Fin (2 * n) → K)),
      coordinateSemilinearMap R.val x = x := fun x hx =>
    congrArg Subtype.val (hρ ⟨x, hx⟩)
  rcases hfix R.val.right hφk with h1 | h1
  · left
    apply Subtype.ext
    refine pair_eq_of_eq_on_span h1 hspan fun x hx => ?_
    rw [hRW x hx, Subgroup.coe_one, coordinateSemilinearMap_one]
  · right
    apply Subtype.ext
    refine pair_eq_of_eq_on_span h1 hspan fun x hx => ?_
    rw [hRW x hx]
    exact (mem_fixSpace.mp hx).symm

theorem centralizer_extKappa_le [CharP (descentField S.val.right) 2] :
    matrixProjectiveImage Q ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom Q S} ⊓
        Subgroup.centralizer
          ((extKappa Q (descentExt e)).range : Set (MulAut (matrixProjectiveDerived Q))) ≤
      Subgroup.zpowers (matrixProjectiveConjugationHom Q S) := by
  rintro y ⟨hyY, hyN⟩
  have hy := exists_rep_commute hQ hT hE hd hS hyY
  obtain ⟨R, hR, hRy, hRS⟩ := hy
  have hcomm : ∀ g : pairDescentDerived hS,
      R * matrixIsometryInclusion Q (descentExt e g) * R⁻¹ =
        matrixIsometryInclusion Q (descentExt e g) := by
    intro g
    refine conj_inclusion_eq_of_commute hQ hT hE hd hR ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hyN _ ⟨g, rfl⟩
    rw [← hRy] at h1
    exact h1.symm
  rcases eq_one_or_eq_of_commute_descentExt hd e he hspan hfix ψ hQc hTc hEc hR hRS hcomm with
    h1 | h1
  · rw [← hRy, h1, map_one]
    exact one_mem _
  · rw [← hRy, h1]
    exact Subgroup.mem_zpowers _

end Bound

theorem evenOrthogonalFieldCentralizer_of_regular {f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (Q : QuadraticForm K (Fin (2 * n) → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    EvenOrthogonalFieldCentralizer Q f := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hd : 1 ≤ 2 * n := by omega
  intro α hα hα2 S hS hSα hσ1
  subst hSα
  have hreal := evenOrthogonalRealization_of_regular hf hK hd Q hQ hT hE
  obtain ⟨-, -, -, -, F, -, -, -, hinv⟩ := hreal
  have hinvS := hinv _ hα hα2 S hS rfl
  obtain ⟨hSS, hTT, -⟩ := hinvS
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs Q => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  have hcard := card_descentField hf hK hσσ hσ1
  obtain ⟨hfeven, hk, hfix⟩ := hcard
  have hdesc := even_quadratic_semilinear_involution_descent
    hσσ hσ1 hQ (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  obtain ⟨hfin, -, -, hQ₀, -, -, -, e, he⟩ := hdesc
  obtain ⟨c, hc⟩ : ∃ c, S.val.right c ≠ c := by
    by_contra! h
    exact hσ1 (RingEquiv.ext h)
  have hσσ' : ∀ a, S.val.right (S.val.right a) = a := fun a => by
    change (S.val.right * S.val.right) a = a
    rw [hσσ]
    rfl
  have hspan : Submodule.span K (pairFix S : Set (Fin (2 * n) → K)) = ⊤ :=
    span_fixSpace hσσ' hTT hc
  have hk2 : 1 ≤ f / 2 := by
    obtain ⟨m, hm⟩ := hfeven
    omega
  have : CharP (descentField S.val.right) 2 :=
    finite_field_prime_power_characteristic Nat.prime_two hk2 hk
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  have hJ := derived_simple_even hn (pairDescentForm hS) hQ₀ hdim
  obtain ⟨-, hsimple, heven⟩ := hJ
  have hcoord := exists_coordinate_isometry hn (pairDescentForm hS) hQ₀ hdim
  obtain ⟨Qc, ⟨ψ⟩, hQc, hTc, hEc⟩ := hcoord
  exact ⟨hfeven, hk, hsimple, heven, descentExt e, fun g w => extHom_mulVec e he _ w,
    fun g A hA => extHom_unique e he hspan _ A hA, extKappa_injective e hQ hT hE hd,
    extKappa_le_inn e, extKappa_le_centralizer e, extKappa_normal e hQ hT hE hd,
    le_antisymm (centralizer_extKappa_le hQ hT hE hd e he hspan hfix ψ hQc hTc hEc)
      (zpowers_le_centralizer_extKappa e)⟩

theorem even_orthogonal_field_centralizer_fixed_derived_group (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) :
    match t with
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          EvenOrthogonalFieldCentralizer (coordinateQuadPlus n K) f
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          EvenOrthogonalFieldCentralizer (coordinateQuadMinus n K hn b c) f
    | _ => False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, hf, hn⟩ := h.1
    intro K _ _ hK _
    have hreg := regular_coordinateQuadPlus n K (by omega)
    exact evenOrthogonalFieldCentralizer_of_regular hf hK hn _ hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega))
  · obtain ⟨-, hf, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr _
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    exact evenOrthogonalFieldCentralizer_of_regular hf hK hn _ hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr)

end CFSG.ComponentClassification.UnbalancedCatalog
