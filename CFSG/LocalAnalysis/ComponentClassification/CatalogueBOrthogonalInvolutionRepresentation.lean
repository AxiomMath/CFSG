module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData CatalogueBStabilizerFamily
open CatalogueBOrthogonalInvolutionConjugacy
open CatalogueBOrthogonalPointAction (Points)

variable {K : Type} [Field K] {d : ℕ}

theorem conjugationHom_eq_one_iff (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hs : Function.Injective (projectivePointStabilizer Q)) (g : similarityPairs Q) :
    matrixProjectiveConjugationHom Q g = 1 ↔
      g.val.right = 1 ∧ ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = g.val.left := by
  rw [← CatalogueBOrthogonalPointKernel.similarityPointAction_eq_one_iff Q hQ hS]
  constructor
  · intro hg
    apply Equiv.ext
    intro L
    apply hs
    rw [← similarity_projective_stabilizer, hg]
    exact Subgroup.map_id _
  · intro hg
    apply MulEquiv.ext
    intro x
    apply CatalogueBOrthogonalPointKernel.projectivePointAction_injective Q hQ hS
    rw [← similarity_projective_covariance, hg, one_mul, inv_one, mul_one]
    rfl

theorem sq_val (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q) :
    (g * g).val.left =
        g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left ∧
      (g * g).val.right = g.val.right ^ 2 :=
  ⟨rfl, (sq g.val.right).symm⟩

theorem eq_one_or_eq_of_mem_zpowers {A : Type*} [Group A] {σ τ : A} (hσ : orderOf σ = 2)
    (hτ : τ ∈ Subgroup.zpowers σ) : τ = 1 ∨ τ = σ := by
  classical
  have hfin : IsOfFinOrder σ := orderOf_pos_iff.mp (by rw [hσ]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hσ] at hτ
  simp only [Finset.mem_image, Finset.mem_range] at hτ
  obtain ⟨i, hi, rfl⟩ := hτ
  interval_cases i
  · exact Or.inl (pow_zero σ)
  · exact Or.inr (pow_one σ)

theorem field_involution_facts [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    Nat.card K = Nat.card {c : K // σ c = c} ^ 2 ∧
      ∀ τ : K ≃+* K, τ ^ 2 = 1 → τ ≠ 1 → τ = σ := by
  obtain ⟨φ, -, -, htop, hcardAut, hfix⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hσord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  obtain ⟨hdvd, S, hS, hcardS⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσord] at hdvd hcardS
  have hSσ : ∀ c, c ∈ S ↔ σ c = c := by
    intro c
    rw [← SetLike.mem_coe, hS]
    constructor
    · intro hc
      exact hc σ (Subgroup.mem_zpowers σ)
    · intro hc τ hτ
      rcases eq_one_or_eq_of_mem_zpowers hσord hτ with rfl | rfl
      · rfl
      · exact hc
  have hcard : Nat.card {c : K // σ c = c} = p ^ (f / 2) := by
    rw [← hcardS]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => (hSσ c).symm)
  refine ⟨?_, fun τ hτ2 hτ1 => ?_⟩
  · rw [hcard, hK, ← pow_mul]
    congr 1
    omega
  · have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨φ, htop⟩
    have hτord : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ1
    have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
    have heq : Subgroup.zpowers τ = Subgroup.zpowers σ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hτord, hσord]
    have hmem : τ ∈ Subgroup.zpowers σ := heq ▸ Subgroup.mem_zpowers τ
    rcases eq_one_or_eq_of_mem_zpowers hσord hmem with h1 | h1
    · exact absurd h1 hτ1
    · exact h1

@[expose] def SemilinearRepresentation (Q : QuadraticForm K (Fin d → K)) : Prop :=
  (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 ↔
    g.val.right = 1 ∧ ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = g.val.left) ∧
  ∀ alpha : MulAut (matrixProjectiveDerived Q), alpha * alpha = 1 → alpha ≠ 1 →
    ∃ (beta : MulAut (matrixProjectiveDerived Q)) (g : similarityPairs Q),
      beta⁻¹ * alpha * beta = matrixProjectiveConjugationHom Q g ∧ g.val.right ^ 2 = 1 ∧
      (∃ c : Kˣ, g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
        g.val.left = GeneralLinearGroup.scalar (Fin d) c) ∧
      (g.val.right = 1 → ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left) ∧
      (g.val.right ≠ 1 → Nat.card K = Nat.card {c : K // g.val.right c = c} ^ 2 ∧
        ∀ τ : K ≃+* K, τ ^ 2 = 1 → τ ≠ 1 → τ = g.val.right)

theorem semilinearRepresentation_of_conjugacy [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hconj : ∀ alpha : MulAut (matrixProjectiveDerived Q), alpha * alpha = 1 →
      ∃ beta, beta⁻¹ * alpha * beta ∈ matrixProjectiveImage Q) :
    SemilinearRepresentation Q := by
  have hker := conjugationHom_eq_one_iff Q hQ hS hs
  refine ⟨hker, fun alpha halpha2 halpha1 => ?_⟩
  obtain ⟨beta, g, hg⟩ := hconj alpha halpha2
  have hsq : matrixProjectiveConjugationHom Q (g * g) = 1 := by
    rw [map_mul, hg]
    calc beta⁻¹ * alpha * beta * (beta⁻¹ * alpha * beta) = beta⁻¹ * (alpha * alpha) * beta := by
          group
      _ = 1 := by rw [halpha2]; group
  obtain ⟨hright, c, hc⟩ := (hker (g * g)).mp hsq
  obtain ⟨hl, hr⟩ := sq_val Q g
  refine ⟨beta, g, hg.symm, hr ▸ hright, ⟨c, hl ▸ hc.symm⟩, fun h1 a ha => ?_,
    fun h1 => field_involution_facts hp hf hK (hr ▸ hright) h1⟩
  apply halpha1
  have hone : matrixProjectiveConjugationHom Q g = 1 := (hker g).mpr ⟨h1, a, ha⟩
  rw [hone] at hg
  calc alpha = beta * (beta⁻¹ * alpha * beta) * beta⁻¹ := by group
    _ = beta * 1 * beta⁻¹ := by rw [← hg]
    _ = 1 := by group

theorem odd_orthogonal_involution_semilinear_representation {G : Type} [Group G]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) :
    match t with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
        SemilinearRepresentation (coordinateQuadOdd n K)
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
        SemilinearRepresentation (coordinateQuadPlus n K)
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
        SemilinearRepresentation (coordinateQuadMinus n K hn b c)
    | _ => False := by
  have hconj := odd_orthogonal_involutions_conjugate_into_semilinear_image t ht h
  rcases ht with rfl | rfl | rfl
  · intro K _ _ hK e
    obtain ⟨-, hQ, hS, -⟩ := coordinate_model_witness_odd h K hK e
    exact semilinearRepresentation_of_conjugacy h.1.1 h.1.2.1 hK _ hQ hS
      (coordinate_model_intrinsic_odd h K hK e).2.1.2.1 (hconj K hK e)
  · intro K _ _ hK e
    obtain ⟨-, hQ, hS, -⟩ := coordinate_model_witness_plus h K hK e
    exact semilinearRepresentation_of_conjugacy h.1.1 h.1.2.1 hK _ hQ hS
      (coordinate_model_intrinsic_plus h K hK e).2.1.2.1 (hconj K hK e).1
  · intro hn K _ _ hK b c hirr e
    obtain ⟨-, hQ, hS, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
    exact semilinearRepresentation_of_conjugacy h.1.1 h.1.2.1 hK _ hQ hS
      (coordinate_model_intrinsic_minus h K hK b c hirr e).2.1.2.1 (hconj hn K hK b c hirr e)

end CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
