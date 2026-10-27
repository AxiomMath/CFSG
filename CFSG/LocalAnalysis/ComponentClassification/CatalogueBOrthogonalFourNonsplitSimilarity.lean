module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitHermitian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

open Matrix QuadraticMap CatalogueBOddQuadratic CFSG.ClassicalGroups.Orthogonal

universe u v

variable {K : Type u} [Field K]

theorem singular_plane_of_two_hypPairs {V : Type v} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P R : HypPair Q) (h : P.Orth R) :
    ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0 := by
  let t : Fin 2 → V := ![P.e, R.e]
  have ht : LinearIndependent K t := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [Fin.sum_univ_two] at ha
    have h0 := congrArg (fun x => polar Q x P.f) ha
    have h1 := congrArg (fun x => polar Q x R.f) ha
    simp only [t, Matrix.cons_val_zero, Matrix.cons_val_one,
      polar_add_left, polar_smul_left_eq, polar_zero_left, P.polar_ef, R.polar_ef,
      h.ef, h.symm.ef, mul_one, mul_zero, add_zero, zero_add] at h0 h1
    intro i
    fin_cases i
    · exact h0
    · exact h1
  refine ⟨Submodule.span K (Set.range t), by
    rw [finrank_span_eq_card ht, Fintype.card_fin], ?_⟩
  intro x hx
  apply map_eq_zero_of_mem_span (Q := Q) ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact P.Q_e
    · exact R.Q_e
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    fin_cases i <;> fin_cases j
    · exact P.polar_ee
    · exact h.ee
    · exact h.symm.ee
    · exact R.polar_ee

theorem exists_plane_binary_isometry [Finite K] {V : Type v} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ w : Fin 2 → Kˣ, (weightedSumSquares K w).Anisotropic ∧
      Nonempty (Q.IsometryEquiv
        ((hyperbolicSumForm K 1).prod (weightedSumSquares K w))) := by
  obtain ⟨m, k, w, hk, ha, hrank, ⟨e⟩⟩ := exists_hyperbolic_decomposition hodd Q hQ
  have hm : m < 2 := by
    by_contra hm
    have hm' : 2 ≤ m := by omega
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, by omega⟩
    apply hno
    exact singular_plane_of_two_hypPairs (originalHypPair e i) (originalHypPair e j)
      (originalHypPair_orth e (by
        intro hij
        have := congrArg Fin.val hij
        simp [i, j] at this))
  have hm' : m = 1 := by omega
  have hk' : k = 2 := by omega
  subst m
  subst k
  exact ⟨w, ha, ⟨e⟩⟩

theorem binary_tail_nonsquare (w : Fin 2 → Kˣ)
    (ha : (weightedSumSquares K w).Anisotropic) :
    ¬ IsSquare ((-(w 1) / w 0 : Kˣ) : K) := by
  rintro ⟨s, hs⟩
  have hv : weightedSumSquares K w ![s, 1] = 0 := by
    rw [weightedSumSquares_apply, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.smul_def, smul_eq_mul, one_mul]
    have hs' : -(w 1 : K) / (w 0 : K) = s * s := by simpa using hs
    field_simp at hs'
    linear_combination -hs'
  have hz := ha _ hv
  have := congrFun hz 1
  simp at this

@[expose] def planeBinaryCoordinates (a : Kˣ) :
    ((Fin 1 → K × K) × (Fin 2 → K)) ≃ₗ[K] (Fin 4 → K) where
  toFun x := ![(x.1 0).1, -(x.1 0).2 / (a : K), x.2 0, x.2 1]
  invFun x := (fun _ => (x 0, -(a : K) * x 1), ![x 2, x 3])
  left_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i
      apply Prod.ext
      · rfl
      · change -(a : K) * (-(x.1 0).2 / (a : K)) = (x.1 0).2
        field_simp
    · funext i
      fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i
    · rfl
    · change -(-(a : K) * x 1) / (a : K) = x 1
      field_simp
    · rfl
    · rfl
  map_add' x y := by
    funext i
    fin_cases i <;> simp [add_div]
    abel
  map_smul' c x := by
    funext i
    fin_cases i
    · rfl
    · change -(c * (x.1 0).2) / (a : K) = c * (-(x.1 0).2 / (a : K))
      ring
    · rfl
    · rfl

@[expose] def planeBinaryToHermitian (w : Fin 2 → Kˣ) (h2 : (2 : K) ≠ 0) :
    ((Fin 1 → K × K) × (Fin 2 → K)) ≃ₗ[K]
      hermitianSubmodule ((-(w 1) / w 0 : Kˣ) : K) :=
  (planeBinaryCoordinates (w 0)).trans (hermitianCoordinates _ h2)

theorem planeBinaryToHermitian_val (w : Fin 2 → Kˣ) (h2 : (2 : K) ≠ 0)
    (x : (Fin 1 → K × K) × (Fin 2 → K)) :
    (planeBinaryToHermitian w h2 x).val =
      !![algebraMap K _ ((x.1 0).1), ⟨x.2 0, x.2 1⟩;
        star (⟨x.2 0, x.2 1⟩ : extension ((-(w 1) / w 0 : Kˣ) : K)),
        algebraMap K _ (-(x.1 0).2 / (w 0 : K))] := rfl

theorem planeBinaryToHermitian_form (w : Fin 2 → Kˣ) (h2 : (2 : K) ≠ 0)
    (x : (Fin 1 → K × K) × (Fin 2 → K)) :
    ((hyperbolicSumForm K 1).prod (weightedSumSquares K w)) x =
      (-(w 0) : Kˣ) * hermitianForm ((-(w 1) / w 0 : Kˣ) : K)
        (planeBinaryToHermitian w h2 x) := by
  rw [QuadraticMap.prod_apply, hyperbolicSumForm_apply, Fin.sum_univ_one,
    weightedSumSquares_apply, Fin.sum_univ_two, hermitianForm_apply,
    planeBinaryToHermitian_val]
  simp only [Units.val_neg, Units.val_div_eq_div_val, Units.smul_def, smul_eq_mul]
  change (x.1 0).1 * (x.1 0).2 + ((w 0 : K) * (x.2 0 * x.2 0) +
    (w 1 : K) * (x.2 1 * x.2 1)) =
    -(w 0 : K) * ((x.1 0).1 * (-(x.1 0).2 / (w 0 : K)) -
      x.2 0 ^ 2 + (-(w 1 : K) / (w 0 : K)) * x.2 1 ^ 2)
  field_simp
  ring

theorem exists_hermitian_similarity [Finite K] {V : Type v} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ (delta : Kˣ), ¬ IsSquare (delta : K) ∧
      ∃ (d : Kˣ) (psi : V ≃ₗ[K] hermitianSubmodule (delta : K)),
        ∀ v, Q v = (d : K) * hermitianForm (delta : K) (psi v) := by
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨w, ha, ⟨e⟩⟩ := exists_plane_binary_isometry hodd Q hQ hdim hno
  refine ⟨-(w 1) / w 0, binary_tail_nonsquare w ha, -(w 0),
    e.toLinearEquiv.trans (planeBinaryToHermitian w h2), ?_⟩
  intro v
  change Q v = _ * hermitianForm _ (planeBinaryToHermitian w h2 (e v))
  rw [← planeBinaryToHermitian_form w h2 (e v), e.map_app]

theorem exists_hermitian_similarity_and_orthogonal_equiv [Finite K] {V : Type v}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 4)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ (delta : Kˣ), ¬ IsSquare (delta : K) ∧
      ∃ (d : Kˣ) (psi : V ≃ₗ[K] hermitianSubmodule (delta : K))
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
          TauCeti.QuadraticMap.orthogonalGroup (hermitianForm (delta : K))),
        (∀ v, Q v = (d : K) * hermitianForm (delta : K) (psi v)) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q)
          (X : hermitianSubmodule (delta : K)),
          (e g).val X = psi (g.val (psi.symm X))) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup (hermitianForm (delta : K)))
          (v : V), (e.symm g).val v = psi.symm (g.val (psi v))) := by
  obtain ⟨delta, hns, d, psi, hpsi⟩ := exists_hermitian_similarity hodd Q hQ hdim hno
  refine ⟨delta, hns, d, psi,
    CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv Q
      (hermitianForm (delta : K)) d psi hpsi, hpsi, ?_, ?_⟩
  · exact CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv_apply
      Q (hermitianForm (delta : K)) d psi hpsi
  · exact CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv_symm_apply
      Q (hermitianForm (delta : K)) d psi hpsi

theorem nonsplit_four_hermitian_determinant_similarity [Finite K] {V : Type v}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 4)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ (delta : Kˣ), ¬ IsSquare (delta : K) ∧
      ∃ (d : Kˣ) (psi : V ≃ₗ[K] hermitianSubmodule (delta : K))
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
          TauCeti.QuadraticMap.orthogonalGroup (hermitianForm (delta : K))),
        (∀ v, algebraMap K (extension (delta : K)) (Q v) =
          algebraMap K (extension (delta : K)) (d : K) * (psi v).val.det) ∧
        Nat.card (extension (delta : K)) = Nat.card K ^ 2 ∧
        (conjugation (delta : K)).toRingEquiv ≠ 1 ∧
        (∀ z : extension (delta : K), conjugation (delta : K) z = z ↔
          z ∈ Set.range (algebraMap K (extension (delta : K)))) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q)
          (X : hermitianSubmodule (delta : K)),
          (e g).val X = psi (g.val (psi.symm X))) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup (hermitianForm (delta : K)))
          (v : V), (e.symm g).val v = psi.symm (g.val (psi v))) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨delta, hns, d, psi, e, hpsi, he, he'⟩ :=
    exists_hermitian_similarity_and_orthogonal_equiv hodd Q hQ hdim hno
  refine ⟨delta, hns, d, psi, e, ?_, extension_card _,
    conjugation_ne_one _ h2, conjugation_fixed_range _ h2, he, he'⟩
  intro v
  rw [hpsi, map_mul, hermitianForm_det _ h2]

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
