module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {K : Type} [Field K] {d : ℕ}

@[expose] def EvenOrthogonalRealization (Q : QuadraticForm K (Fin d → K)) (f : ℕ) : Prop :=
  matrixDerivedScalars Q = ⊥ ∧
  (∀ g : similarityPairs Q, g ∈ unitMultiplierPairs Q ↔ multiplier Q g = 1) ∧
  (∃ Φ : unitMultiplierPairs Q ≃* matrixProjectiveImage Q,
    ∀ g, (Φ g : MulAut (matrixProjectiveDerived Q)) = matrixProjectiveConjugationHom Q g) ∧
  (∀ α ∈ matrixProjectiveImage Q, ∃! g : similarityPairs Q,
    g ∈ unitMultiplierPairs Q ∧ matrixProjectiveConjugationHom Q g = α) ∧
  ∃ F : matrixProjectiveImage Q →* (K ≃+* K),
    (∀ g : similarityPairs Q, F ⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ = g.val.right) ∧
    F.ker = ((matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)).range.subgroupOf
      (matrixProjectiveImage Q) ∧
    Function.Injective ((matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)) ∧
    ∀ α ∈ matrixProjectiveImage Q, orderOf α = 2 → ∀ g : similarityPairs Q,
      g ∈ unitMultiplierPairs Q → matrixProjectiveConjugationHom Q g = α →
        g * g = 1 ∧ (∀ v, coordinateSemilinearMap g.val (coordinateSemilinearMap g.val v) = v) ∧
        (g.val.right = 1 ∨ (orderOf g.val.right = 2 ∧
          (∀ τ : K ≃+* K, orderOf τ = 2 → τ = g.val.right) ∧ Even f))

theorem evenOrthogonalRealization_of_regular {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hd : 1 ≤ d) (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q) :
    EvenOrthogonalRealization Q f := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hQ0 := exists_ne_zero_of_polar_nondegenerate hd hQ
  set Φ : unitMultiplierPairs Q ≃* matrixProjectiveImage Q :=
    (MonoidHom.ofInjective (unitKappa_injective Q hQ hT hE hd)).trans
      (MulEquiv.subgroupCongr (range_unitKappa Q)) with hΦdef
  have hΦ : ∀ g, (Φ g : MulAut (matrixProjectiveDerived Q)) = matrixProjectiveConjugationHom Q g :=
    fun _ => rfl
  set F : matrixProjectiveImage Q →* (K ≃+* K) :=
    (fieldProjection Q).comp ((unitMultiplierPairs Q).subtype.comp Φ.symm.toMonoidHom) with hFdef
  have hFΦ : ∀ h : unitMultiplierPairs Q, F (Φ h) = h.1.val.right := fun h => by
    change fieldProjection Q (Φ.symm (Φ h)).1 = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hF : ∀ g : similarityPairs Q,
      F ⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ = g.val.right := by
    intro g
    obtain ⟨b, hb⟩ := exists_scalarPair_mul_mem Q g
    have h1 : (⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ : matrixProjectiveImage Q) =
        Φ ⟨_, hb⟩ := by
      apply Subtype.ext
      rw [hΦ]
      change matrixProjectiveConjugationHom Q g =
        matrixProjectiveConjugationHom Q (⟨_, scalarPair_mem Q b⟩ * g)
      rw [map_mul, kappa_scalarPair, one_mul]
    rw [h1, hFΦ]
    exact one_mul g.val.right
  obtain ⟨σ₀, -, -, hzp, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, hzp⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  refine ⟨matrixDerivedScalars_eq_bot_of_charTwo Q hQ0,
    mem_unitMultiplierPairs_iff_multiplier Q hQ0, ⟨Φ, hΦ⟩, ?_, F, hF, ?_, ?_, ?_⟩
  ·
    intro α hα
    obtain ⟨h, hh⟩ := Φ.surjective ⟨α, hα⟩
    refine ⟨h.1, ⟨h.2, by rw [← hΦ, hh]⟩, ?_⟩
    rintro g ⟨hg, hgα⟩
    have h1 : Φ ⟨g, hg⟩ = Φ h := Subtype.ext (by rw [hΦ, hgα, hh])
    exact congrArg Subtype.val (Φ.injective h1)
  ·
    ext α
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    obtain ⟨h, rfl⟩ := Φ.surjective α
    rw [hFΦ, hΦ]
    constructor
    · intro hσ
      have hA : h.1.val.left ∈ matrixIsometries Q := by
        rw [mem_matrixIsometries_iff]
        intro v
        have h2 := (mem_unitMultiplierPairs_iff Q h.1).mp h.2 v
        rw [coordinateSemilinearMap_apply, hσ] at h2
        exact h2
      refine ⟨⟨_, hA⟩, ?_⟩
      show matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ⟨_, hA⟩) = _
      congr 1
      apply Subtype.ext
      rw [matrixIsometryInclusion_val]
      exact SemidirectProduct.ext rfl hσ.symm
    · rintro ⟨A, hA⟩
      have h1 := hF (matrixIsometryInclusion Q A)
      have h2 : (⟨matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q A), ⟨_, rfl⟩⟩ :
          matrixProjectiveImage Q) = Φ h := Subtype.ext (by rw [hΦ]; exact hA)
      rw [h2, hFΦ] at h1
      rw [h1]
      rfl
  ·
    rw [injective_iff_map_eq_one]
    intro A hA
    have hmem : matrixIsometryInclusion Q A ∈ unitMultiplierPairs Q := fun v => by
      rw [matrixIsometryInclusion_val, coordinateSemilinearMap_inl]
      exact (mem_matrixIsometries_iff Q A.val).mp A.2 v
    have h1 := eq_one_of_kappa_eq_one Q hQ hT hE hd hmem hA
    exact matrixIsometryInclusion_injective Q (h1.trans (map_one _).symm)
  ·
    intro α hα hα2 g hg hgα
    have hgg : g * g = 1 := by
      have h1 : matrixProjectiveConjugationHom Q (g * g) = 1 := by
        have h2 := pow_orderOf_eq_one α
        rw [hα2, sq] at h2
        rw [map_mul, hgα, h2]
      exact eq_one_of_kappa_eq_one Q hQ hT hE hd (mul_mem hg hg) h1
    refine ⟨hgg, fun v => ?_, ?_⟩
    · rw [← coordinateSemilinearMap_mul]
      change coordinateSemilinearMap (g * g).val v = v
      rw [hgg]
      exact coordinateSemilinearMap_one v
    · by_cases hσ : g.val.right = 1
      · exact Or.inl hσ
      · have hσ2 : g.val.right ^ 2 = 1 := by
          rw [sq]
          exact congrArg (fun x : similarityPairs Q => x.val.right) hgg
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hord : orderOf g.val.right = 2 := orderOf_eq_prime hσ2 hσ
        refine Or.inr ⟨hord, fun τ hτ => eq_of_orderOf_eq_two_of_isCyclic hτ hord, ?_⟩
        rw [← hcard, even_iff_two_dvd, ← hord]
        exact orderOf_dvd_natCard _

theorem even_orthogonal_semilinear_isometry_realization (G : Type) [Group G] (t : StatedLieTag)
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ) (h : StatedClassicalModel G t n 2 f) :
    match t with
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          EvenOrthogonalRealization (coordinateQuadPlus n K) f
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          EvenOrthogonalRealization (coordinateQuadMinus n K hn b c) f
    | _ => False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, hf, hn⟩ := h.1
    intro K _ _ hK _
    have hreg := regular_coordinateQuadPlus n K (by omega)
    exact evenOrthogonalRealization_of_regular hf hK (by omega) _ hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega))
  · obtain ⟨-, hf, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr _
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    exact evenOrthogonalRealization_of_regular hf hK (by omega) _ hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr)

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
