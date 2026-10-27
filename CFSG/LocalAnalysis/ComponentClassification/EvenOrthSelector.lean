module

public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelectorCore
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelectorSource
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaInvolutionConjugacy

public noncomputable section

namespace CFSG.ComponentClassification.EvenOrthSelector

open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.Blueprint
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem statedModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel X t n p f) : StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem exists_coordinate_witness {W : Type} [Group W] {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n f : ℕ} (h : StatedClassicalModel W t n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (Q : QuadraticForm K (Fin (2 * n) → K)),
      Nat.card K = 2 ^ f ∧ Q.polarBilin.Nondegenerate ∧
      (∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
        elementaryGroup Q ∧
      (∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
        ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q) ∧
      Nonempty (W ≃* matrixProjectiveDerived Q) := by
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image W t ht n f h).1
  rcases ht with rfl | rfl
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
    have hreg := regular_coordinateQuadPlus n K (by omega)
    exact ⟨K, inferInstance, inferInstance, coordinateQuadPlus n K, hK, hreg.1, hreg.2,
      commutator_coordinateQuadPlus n K (by omega), (hI K hK e).1,
      ⟨coordinatePlusWitnessEquiv K e⟩⟩
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    exact ⟨K, inferInstance, inferInstance, coordinateQuadMinus n K (by omega) b c, hK, hreg.1,
      hreg.2, commutator_coordinateQuadMinus n K b c hn hirr, hI (by omega) K hK b c hirr e,
      ⟨coordinateMinusWitnessEquiv K (by omega) b c e⟩⟩

theorem false_of_coordinate {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hs : SmallSource L)
    {K : Type} [Field K] [Finite K] {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (θ : W ≃* matrixProjectiveDerived Q) : False := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hcinj :=
    UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived hQ hT hE
  have hZ : center (matrixProjectiveDerived Q) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    apply hcinj
    rw [map_one]
    ext y
    rw [MulAut.conj_apply, MulAut.one_apply, (mem_center_iff.mp hx y).symm, mul_inv_cancel_right]
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hCW θ hZ
  obtain ⟨-, hCWimg, -⟩ := OutcomeLocal.socle_images hinj θ hρW a
  have hL₁ := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
  rw [hCWimg] at hL₁
  have hαα : ρ a * ρ a = 1 := by
    have h2 := pow_orderOf_eq_one a
    rw [ha] at h2
    rw [← map_mul, ← pow_two, h2, map_one]
  obtain ⟨β, hβ⟩ := hconj (ρ a) hαα
  have hX := LocalAnalysis.ComponentInitial.isComponentOf_map_conj hL₁ β⁻¹
  rw [OutcomeLocal.map_conj_inner_inf_centralizer, inv_inv] at hX
  have hα2 : orderOf (β⁻¹ * ρ a * β) = 2 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj β⁻¹) (ρ a)
    rw [MulAut.conj_apply, inv_inv] at h1
    rw [h1, orderOf_injective ρ hinj a, ha]
  obtain ⟨hXs, k, _, _, g, hk, ι, hι⟩ := semilinear_component hf hK hn hQ hT hE hβ hα2 hX
  let eL : L ≃* ↥((L.map ρ).map (MulAut.conj β⁻¹).toMonoidHom) :=
    (L.equivMapOfInjective ρ hinj).trans
      ((L.map ρ).equivMapOfInjective _ (MulAut.conj β⁻¹).injective)
  have hLnab := OutcomeLocal.exists_ne_commute_of_isQuasisimple hLCW.2.2
  have : IsSimpleGroup L := eL.isSimpleGroup
  obtain ⟨eZ⟩ := OutcomeLocal.nonempty_quotient_center_mulEquiv hLnab eL
  obtain ⟨hP2, hA7, hP34⟩ := not_small_of_sp_embedding hk (by omega : 3 ≤ n - 1)
    (ι := eZ.symm.toMonoidHom.comp ι) (eZ.symm.injective.comp hι)
  rcases hs with ⟨p, f', -, hp2, -, -, hm, -⟩ | ⟨⟨e7⟩, -⟩ | h34
  · exact hP2 p f' hp2 (statedModel_of_lieModel (by decide) hm)
  · exact hA7.false e7
  · exact hP34 (statedModel_of_lieModel (by decide) h34)

theorem almostSimpleRestricted_evenOrthogonal : AlmostSimpleRestricted EvenOrthogonal := by
  intro A _ _ W _ _ _ hCW _ hEO a ha L hLW _ hL _ hs
  exfalso
  have hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
    LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  obtain ⟨n, f, hn, hf, hm⟩ := hEO
  obtain ⟨t, ht, hmod⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel W t n 2 f := by
    rcases hm with hm | hm
    · exact ⟨_, Or.inl rfl, statedModel_of_lieModel (by decide) hm⟩
    · exact ⟨_, Or.inr rfl, statedModel_of_lieModel (by decide) hm⟩
  obtain ⟨K, _, _, Q, hK, hQ, hT, hE, hconj, ⟨θ⟩⟩ := exists_coordinate_witness ht hmod
  exact false_of_coordinate hCW ha hLCW hs hf hK hn hQ hT hE hconj θ

end CFSG.ComponentClassification.EvenOrthSelector
