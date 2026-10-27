module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaHigherRank
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthogonalSymmetry
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace OmegaRadical

variable {K : Type} [Field K] {d : ℕ}

theorem exists_symmetry_of_rank_le_one [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) {s : GL (Fin d) K} (hs : s ∈ matrixIsometries Q)
    (hss : s * s = 1) (hs1 : s ≠ 1) (hr : ((s : Matrix (Fin d) (Fin d) K) - 1).rank ≤ 1) :
    ∃ v, Q v = 1 ∧ s = symmetryGL Q v := by
  set T := matrixLinearEquiv s with hTdef
  have hTT : ∀ x, T (T x) = x := fun x => by
    have h := congrArg (fun A : GL (Fin d) K => matrixLinearEquiv A x) hss
    simp only [matrixLinearEquiv_mul, LinearEquiv.mul_apply] at h
    rw [h]
    exact Matrix.one_mulVec x
  have hiso : ∀ x, Q (T x) = Q x := (mem_matrixIsometries_iff Q s).mp hs
  have hpol : ∀ x y, polar Q (T x) (T y) = polar Q x y := fun x y => by
    rw [polar, polar, ← map_add, hiso, hiso, hiso]
  have hadj : ∀ x y, polar Q (T x - x) y = polar Q x (T y - y) := fun x y => by
    rw [polar_sub_left, polar_sub_right]
    have h := hpol x (T y)
    rw [hTT] at h
    rw [← h]
  have hmemR : ∀ x, T x - x ∈
      LinearMap.range (((s : Matrix (Fin d) (Fin d) K) - 1).mulVecLin) := fun x =>
    ⟨x, by rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]; rfl⟩
  obtain ⟨x₁, hx₁⟩ : ∃ x, T x - x ≠ 0 := by
    by_contra! h
    apply hs1
    apply matrixLinearIso.injective
    rw [map_one]
    exact LinearEquiv.ext fun x => sub_eq_zero.mp (h x)
  have hu_mem := hmemR x₁
  generalize hu : T x₁ - x₁ = u at hx₁ hu_mem
  have hle : K ∙ u ≤ LinearMap.range (((s : Matrix (Fin d) (Fin d) K) - 1).mulVecLin) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hu_mem
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton hx₁]; exact hr)
  have hspan : ∀ x, ∃ c : K, c • u = T x - x := fun x => by
    have h := hmemR x
    rw [← heq, Submodule.mem_span_singleton] at h
    exact h
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hx₁
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, polar Q u y₀ = 1 :=
    ⟨(polar Q u y)⁻¹ • y, by rw [polar_smul_right_eq, inv_mul_cancel₀ hy]⟩
  obtain ⟨a, ha⟩ := hspan y₀
  have hform : ∀ x, T x - x = (a * polar Q x u) • u := fun x => by
    obtain ⟨c, hc⟩ := hspan x
    have h1 := hadj x y₀
    rw [← hc, ← ha, polar_smul_left_eq, polar_smul_right_eq, hy₀, mul_one] at h1
    rw [← hc, h1]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx₁
    have h := hform x₁
    rw [zero_mul, zero_smul, hu] at h
    exact h
  have hQu : a * Q u = 1 := by
    have h1 := hiso y₀
    rw [show T y₀ = y₀ + a • u by rw [ha]; abel, QuadraticMap.map_add Q, QuadraticMap.map_smul,
      smul_eq_mul, polar_smul_right_eq, polar_comm, hy₀] at h1
    have h2 : a * (a * Q u + 1) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.mp h2).resolve_left ha0
    linear_combination h3 - (CharTwo.two_eq_zero : (2 : K) = 0)
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  have hv : Q (c • u) = 1 := by
    rw [QuadraticMap.map_smul, smul_eq_mul, ← hc, hQu]
  refine ⟨c • u, hv, ?_⟩
  apply matrixLinearIso.injective
  apply LinearEquiv.ext
  intro x
  change T x = (symmetryGL Q (c • u) : Matrix (Fin d) (Fin d) K) *ᵥ x
  rw [symmetryGL_mulVec_of_charTwo hv, polar_smul_left_eq, smul_smul, ← sub_eq_iff_eq_add',
    hform x, hc, polar_comm Q x u]
  congr 1
  ring

@[expose] def LinearInvolutionOddCore (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ H : Subgroup (MulAut (matrixProjectiveDerived Q)), inner (matrixProjectiveDerived Q) ≤ H →
    H ≤ matrixProjectiveImage Q → ∀ g : similarityPairs Q, g.val.right = 1 →
      matrixProjectiveConjugationHom Q g ∈ H →
      orderOf (matrixProjectiveConjugationHom Q g) = 2 →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom Q g}) = ⊥

theorem linearInvolutionOddCore_of_regular {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) : LinearInvolutionOddCore Q := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  intro H hInn hHE g hg1 hgH hg2
  obtain ⟨-, -, -, -, F, hF, hker, -, -⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
  have hmem : (⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ : matrixProjectiveImage Q) ∈
      F.ker := by
    rw [MonoidHom.mem_ker, hF, hg1]
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
      matrixProjectiveConjugationHom Q g := hs
  rw [← hs'] at hgH hg2 ⊢
  have hss : s * s = 1 := by
    apply isometryKappa_injective hQ hT hE
    rw [map_mul, map_one]
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) *
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = 1
    have h2 := pow_orderOf_eq_one
      (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))
    rw [hg2] at h2
    rw [← pow_two]
    exact h2
  have hs1 : (s : GL (Fin (2 * n)) K) ≠ 1 := by
    intro h
    have h1 : s = 1 := Subtype.ext h
    rw [h1, map_one, map_one, orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  by_cases hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank
  · exact higherRankOddCore_of_regular hQ hT hE H hInn hHE s hgH hg2 hr
  · obtain ⟨v, hv, hsv⟩ := exists_symmetry_of_rank_le_one hQ s.2
      (congrArg Subtype.val hss) hs1 (by omega)
    have hincl : s = symmetryIsometry Q v := Subtype.ext hsv
    subst hincl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hodd⟩ :=
      evenOrthogonalSymmetryCentralizer_of_regular hf hK hn Q hQ hT hE v hv
    exact hodd H hInn hHE

end OmegaRadical

open OmegaRadical in
theorem even_orthogonal_linear_involution_semilinear_odd_core (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) :
    match t with
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          LinearInvolutionOddCore (coordinateQuadPlus n K)
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          LinearInvolutionOddCore (coordinateQuadMinus n K hn b c)
    | _ => False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, hf, hn⟩ := h.1
    intro K _ _ hK _
    have hreg := regular_coordinateQuadPlus n K (by omega)
    exact linearInvolutionOddCore_of_regular hf hK (by omega) hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega))
  · obtain ⟨-, hf, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr _
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    exact linearInvolutionOddCore_of_regular hf hK (by omega) hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr)

end CFSG.ComponentClassification.UnbalancedCatalog
