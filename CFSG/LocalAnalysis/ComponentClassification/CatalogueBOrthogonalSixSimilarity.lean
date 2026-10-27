module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixSimilarityCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitSimilarity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixSimilarityWitt

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSixSimilarity

open Matrix QuadraticMap CatalogueBOddQuadratic CatalogueBOrthogonalFourNonsplit
  CatalogueBOrthogonalSix

universe u v

variable {K : Type u} [Field K]

@[expose] def planesBinaryToSix (w : Fin 2 → Kˣ)
    (ha : (weightedSumSquares K w).Anisotropic) (h2 : (2 : K) ≠ 0) :
    ((Fin 2 → K × K) × (Fin 2 → K)) ≃ₗ[K]
      sixSubmodule ((-(w 1) / w 0 : Kˣ) : K) :=
  let : Fact (¬ IsSquare ((-(w 1) / w 0 : Kˣ) : K)) := ⟨binary_tail_nonsquare w ha⟩
  (planesBinaryCoordinates (w 0) (-(w 1) / w 0)).trans (sixCoordinates _ h2)

theorem planesBinaryToSix_val (w : Fin 2 → Kˣ)
    (ha : (weightedSumSquares K w).Anisotropic) (h2 : (2 : K) ≠ 0)
    (x : (Fin 2 → K × K) × (Fin 2 → K)) :
    (planesBinaryToSix w ha h2 x).val =
      sixCoordinateMatrix ((-(w 1) / w 0 : Kˣ) : K)
        ![(x.1 0).1, -(x.1 0).2 / (w 0 : K), x.2 0, x.2 1,
          (x.1 1).1, -(x.1 1).2 / ((w 0 : K) * ((-(w 1) / w 0 : Kˣ) : K))] := rfl

theorem planesBinaryToSix_form (w : Fin 2 → Kˣ)
    (ha : (weightedSumSquares K w).Anisotropic) (h2 : (2 : K) ≠ 0)
    (x : (Fin 2 → K × K) × (Fin 2 → K)) :
    ((hyperbolicSumForm K 2).prod (weightedSumSquares K w)) x =
      (-(w 0) : Kˣ) * sixForm ((-(w 1) / w 0 : Kˣ) : K)
        (planesBinaryToSix w ha h2 x) := by
  let : Fact (¬ IsSquare ((-(w 1) / w 0 : Kˣ) : K)) := ⟨binary_tail_nonsquare w ha⟩
  change _ = -(w 0 : K) * sixForm _
    (sixCoordinates _ h2 (planesBinaryCoordinates (w 0) (-(w 1) / w 0) x))
  rw [sixForm_coordinates]
  exact planesBinaryCoordinates_form w x

variable [Finite K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_six_similarity (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 6)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 3 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ (delta : Kˣ), ¬ IsSquare (delta : K) ∧
      ∃ (d : Kˣ) (psi : V ≃ₗ[K] sixSubmodule (delta : K)),
        ∀ v, Q v = (d : K) * sixForm (delta : K) (psi v) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨w, ha, ⟨e⟩⟩ := exists_two_planes_binary_isometry hodd Q hQ hdim hno
  refine ⟨-(w 1) / w 0, binary_tail_nonsquare w ha, -(w 0),
    e.toLinearEquiv.trans (planesBinaryToSix w ha h2), ?_⟩
  intro v
  change Q v = _ * sixForm _ (planesBinaryToSix w ha h2 (e v))
  rw [← planesBinaryToSix_form w ha h2 (e v), e.map_app]

theorem exists_six_similarity_and_orthogonal_equiv (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 6)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 3 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ (delta : Kˣ), ¬ IsSquare (delta : K) ∧
      ∃ (d : Kˣ) (psi : V ≃ₗ[K] sixSubmodule (delta : K))
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
          TauCeti.QuadraticMap.orthogonalGroup (sixForm (delta : K))),
        (∀ v, Q v = (d : K) * sixForm (delta : K) (psi v)) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : sixSubmodule (delta : K)),
          (e g).val X = psi (g.val (psi.symm X))) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup (sixForm (delta : K))) (v : V),
          (e.symm g).val v = psi.symm (g.val (psi v))) := by
  obtain ⟨delta, hns, d, psi, hpsi⟩ := exists_six_similarity hodd Q hQ hdim hno
  refine ⟨delta, hns, d, psi,
    CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv Q
      (sixForm (delta : K)) d psi hpsi, hpsi, ?_, ?_⟩
  · exact CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv_apply
      Q (sixForm (delta : K)) d psi hpsi
  · exact CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv_symm_apply
      Q (sixForm (delta : K)) d psi hpsi

theorem nonsplit_six_unitary_skew_form_similarity (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 6)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 3 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ (delta : Kˣ), ¬ IsSquare (delta : K) ∧
      ∃ (d : Kˣ) (psi : V ≃ₗ[K] sixSubmodule (delta : K))
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
          TauCeti.QuadraticMap.orthogonalGroup (sixForm (delta : K))),
        (∀ v, Q v = (d : K) * sixForm (delta : K) (psi v)) ∧
        (∀ v, algebraMap K (extension (delta : K)) (Q v) =
          algebraMap K (extension (delta : K)) (d : K) * pfaffian (psi v).val) ∧
        Nat.card (extension (delta : K)) = Nat.card K ^ 2 ∧
        (conjugation (delta : K)).toRingEquiv ≠ 1 ∧
        (∀ z : extension (delta : K), conjugation (delta : K) z = z ↔
          z ∈ Set.range (algebraMap K (extension (delta : K)))) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : sixSubmodule (delta : K)),
          (e g).val X = psi (g.val (psi.symm X))) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup (sixForm (delta : K))) (v : V),
          (e.symm g).val v = psi.symm (g.val (psi v))) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨delta, hns, d, psi, e, hpsi, he, he'⟩ :=
    exists_six_similarity_and_orthogonal_equiv hodd Q hQ hdim hno
  let : Fact (¬ IsSquare (delta : K)) := ⟨hns⟩
  refine ⟨delta, hns, d, psi, e, hpsi, ?_, extension_card _,
    conjugation_ne_one _ h2, conjugation_fixed_range _ h2, he, he'⟩
  intro v
  rw [hpsi, map_mul, sixForm_pfaffian _ h2]

end CFSG.ComponentClassification.CatalogueBOrthogonalSixSimilarity
