module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBounds

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ}

theorem matrixDerivedConjugation_isometry_val (Q : QuadraticForm K (Fin d → K))
    (s : matrixIsometries Q) (A : matrixDerived Q) :
    (matrixDerivedConjugation Q (matrixIsometryInclusion Q s) A).val =
      (s : GL (Fin d) K) * A.val * (s : GL (Fin d) K)⁻¹ := by
  rw [matrixDerivedConjugation_val, matrixIsometryInclusion_val, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_one, MulAut.one_apply]

theorem card_fixedSubgroup_isometry_eq {Q : QuadraticForm K (Fin d → K)}
    (hZ : matrixDerivedScalars Q = ⊥) (s : matrixIsometries Q) :
    Nat.card (fixedSubgroup (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))) =
      Nat.card ↥(matrixDerived Q ⊓ Subgroup.centralizer {(s : GL (Fin d) K)}) := by
  set θ := matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) with hθ
  set π := matrixProjectiveProjection Q with hπ
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have hA' : A ∈ matrixDerivedScalars Q := (QuotientGroup.eq_one_iff A).mp hA
    rw [hZ, Subgroup.mem_bot] at hA'
    exact hA'
  have hact : ∀ A : matrixDerived Q, θ (π A) =
      π (matrixDerivedConjugation Q (matrixIsometryInclusion Q s) A) := fun A =>
    matrixProjectiveConjugation_mk Q _ A
  have hfix : ∀ A : matrixDerived Q, θ (π A) = π A ↔
      (s : GL (Fin d) K) * A.val = A.val * (s : GL (Fin d) K) := by
    intro A
    rw [hact]
    constructor
    · intro h
      have h1 := congrArg Subtype.val (hπinj h)
      rw [matrixDerivedConjugation_isometry_val] at h1
      calc (s : GL (Fin d) K) * A.val
          = (s : GL (Fin d) K) * A.val * (s : GL (Fin d) K)⁻¹ * (s : GL (Fin d) K) := by group
        _ = A.val * (s : GL (Fin d) K) := by rw [h1]
    · intro h
      congr 1
      apply Subtype.ext
      rw [matrixDerivedConjugation_isometry_val, h, mul_inv_cancel_right]
  let Φ : ↥(matrixDerived Q ⊓ Subgroup.centralizer {(s : GL (Fin d) K)}) →
      fixedSubgroup θ := fun x =>
    ⟨π ⟨x.1, x.2.1⟩, (hfix ⟨x.1, x.2.1⟩).mpr
      ((Subgroup.mem_centralizer_singleton_iff.mp x.2.2).symm)⟩
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · have h1 := hπinj (congrArg Subtype.val hxy)
      have h2 : ((⟨x.1, x.2.1⟩ : matrixDerived Q) : GL (Fin d) K) =
          ((⟨y.1, y.2.1⟩ : matrixDerived Q) : GL (Fin d) K) := congrArg Subtype.val h1
      exact Subtype.ext h2
    · obtain ⟨B, hB⟩ := matrixProjectiveProjection_surjective Q y.1
      have hy : θ (π B) = π B := by
        rw [← hπ] at hB
        rw [hB]
        exact y.2
      refine ⟨⟨B.val, B.2, Subgroup.mem_centralizer_singleton_iff.mpr
        ((hfix B).mp hy).symm⟩, Subtype.ext ?_⟩
      exact hB
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm

@[expose] def OmegaLinearInvolutionMatrixTwoPart (Q : QuadraticForm K (Fin d → K)) (n f : ℕ) :
    Prop :=
  ∀ s ∈ matrixIsometries Q, s * s = 1 → s ≠ 1 →
    ∃ R : Subgroup (GL (Fin d) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧
      2 ^ (f * (n * (n - 1) + 4)) ≤ Nat.card R ^ 2

theorem omegaLinearInvolutionTwoPart_of_matrix [Finite K] {Q : QuadraticForm K (Fin d → K)}
    (hZ : matrixDerivedScalars Q = ⊥) {n f : ℕ}
    (hM : OmegaLinearInvolutionMatrixTwoPart Q n f) : OmegaLinearInvolutionTwoPart Q n f := by
  intro s hss hs1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR2, hRle, hRcard⟩ := hM s.val s.2 (congrArg Subtype.val hss)
    (fun h => hs1 (Subtype.ext h))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
  rw [card_fixedSubgroup_isometry_eq hZ s]
  have hdvd : Nat.card R ∣
      Nat.card ↥(matrixDerived Q ⊓ Subgroup.centralizer {(s : GL (Fin d) K)}) :=
    Subgroup.card_dvd_of_le hRle
  have hle := factorization_two_le_of_dvd_ne_zero hdvd Nat.card_pos.ne'
  rw [hk, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hle
  rw [hk, ← pow_mul] at hRcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hRcard
  omega

end CFSG.SeitzReduction.OmegaPilot
