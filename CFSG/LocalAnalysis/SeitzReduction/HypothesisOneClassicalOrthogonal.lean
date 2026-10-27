module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalShear
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalShearCModel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalLagrangian
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalOuter
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalOuterReduction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFullCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonal
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow

public section

namespace CFSG.SeitzReduction

namespace OmegaAssembly

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.OrthogonalInvolutions (commSpace fixSpace)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

variable {K : Type} [Field K] {n : ℕ}

theorem rank_sub_one_eq_finrank_commSpace {d : ℕ} (s : GL (Fin d) K) :
    (((s : Matrix (Fin d) (Fin d) K) - 1).rank) =
      Module.finrank K (commSpace (matrixLinearEquiv s)) := by
  have h : ((s : Matrix (Fin d) (Fin d) K) - 1).mulVecLin =
      ((matrixLinearEquiv s : (Fin d → K) →ₗ[K] (Fin d → K)) - 1) := by
    refine LinearMap.ext fun v => ?_
    simp [matrixLinearEquiv_apply]
  rw [Matrix.rank, h]

theorem pow_two_eq_one_of_isometry {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {s : matrixIsometries Q} (hss : s * s = 1) (hs1 : s ≠ 1) :
    ∀ β ∈ matrixProjectiveImage Q,
      β * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) * β →
      (∀ c, matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) c = c →
        Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  intro β hβ hβx hβc
  set t := matrixLinearEquiv (s : GL (Fin (2 * n)) K) with htdef
  by_cases hr : (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank ≤ 1
  · exact OmegaOuter.reflection_pow_two_eq_one hf hK hn hQ hT hE hss hs1 hr β hβ hβx hβc
  have hW2 : 2 ≤ Module.finrank K (commSpace t) := by
    rw [← rank_sub_one_eq_finrank_commSpace]
    omega
  by_cases hlag : fixSpace t ≤ commSpace t
  · exact OrthogonalLagrangian.sq_eq_one_of_lagrangian hQ hT hE (by omega) s hss hlag hβ hβx hβc
  have hWL : commSpace t ≠ fixSpace t := fun h => hlag h.ge
  by_cases ha : ∀ x ∈ commSpace t, Q x = 0
  · exact pow_two_eq_one_of_kappa_of_ne_ab hQ hT hE hss hs1 hWL (Or.inl ha) β hβ hβx hβc
  push Not at ha
  have hs2 : (s : GL (Fin (2 * n)) K) * s = 1 := by
    rw [← Subgroup.coe_mul, hss, Subgroup.coe_one]
  exact OrthogonalShearC.kappa_sq_eq_one_of_commute_odd_of_finrank hQ hT hE (by omega) s hs2 ha
    hW2 hWL hβ hβx hβc

theorem pow_two_eq_one_of_mem_image {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    ∀ x ∈ matrixProjectiveImage Q, orderOf x = 2 → ∀ β ∈ matrixProjectiveImage Q,
      β * x = x * β → (∀ c, x c = c → Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  intro α hα hα2 β hβ hβα hβc
  obtain ⟨-, -, -, huniq, -, -, -, -, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
  obtain ⟨S, ⟨hS, hSα⟩, -⟩ := huniq α hα
  by_cases hσ : S.val.right = 1
  ·
    obtain ⟨hS2, -, -⟩ := hinv α hα hα2 S hS hSα
    have hA : S.val.left ∈ matrixIsometries Q := by
      rw [mem_matrixIsometries_iff]
      intro v
      have h := hS v
      rw [coordinateSemilinearMap_apply, hσ] at h
      exact h
    set s : matrixIsometries Q := ⟨S.val.left, hA⟩ with hsdef
    have hSs : S = matrixIsometryInclusion Q s := by
      apply Subtype.ext
      rw [matrixIsometryInclusion_val]
      exact SemidirectProduct.ext rfl hσ
    have hss : s * s = 1 := by
      apply Subtype.ext
      have h := congrArg (fun g : similarityPairs Q => g.val.left) hS2
      simp only [Subgroup.coe_mul, SemidirectProduct.mul_left, hσ, map_one, MulAut.one_apply,
        OneMemClass.coe_one, SemidirectProduct.one_left] at h
      exact h
    have hαs : α = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) := by
      rw [← hSα, hSs]
    have hs1 : s ≠ 1 := by
      rintro hs
      rw [hαs, hs, map_one, map_one, orderOf_one] at hα2
      exact absurd hα2 (by norm_num)
    subst hαs
    exact pow_two_eq_one_of_isometry hf hK hn hQ hT hE hss hs1 β hβ hβα hβc
  ·
    exact OmegaOuter.field_pow_two_eq_one hf hK hn hQ hT hE hα2 hS hSα hσ β hβ hβα hβc

theorem involutionCriterion_of_image_eq_top {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (htop : matrixProjectiveImage Q = ⊤)
    {x : MulAut (matrixProjectiveDerived Q)} (hx : orderOf x = 2) : InvolutionCriterion x :=
  fun β hβx hβc => pow_two_eq_one_of_mem_image hf hK hn hQ hT hE x (htop ▸ mem_top x) hx β
    (htop ▸ mem_top β) hβx hβc

theorem hypothesisOne_of_regular {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hcore : CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.FullInvolutionOddCore Q)
    (hconj : ∀ P : Subgroup (MulAut (matrixProjectiveDerived Q)), IsPGroup 2 P →
      ∃ ψ : MulAut (matrixProjectiveDerived Q),
        P.map (MulAut.conj ψ⁻¹).toMonoidHom ≤ matrixProjectiveImage Q) :
    HypothesisOne (matrixProjectiveDerived Q) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact OmegaOuter.hypothesisOne_of_conj_le
    (OmegaOuter.conj_injective_of_regular hQ hT hE (by omega)) hcore hconj
    (pow_two_eq_one_of_mem_image hf hK hn hQ hT hE)

section Coordinate

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_orthogonal_all_involution_full_centralizer_odd_core)
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical (FullInvolutionOddCore)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_plus
  matrixProjectiveImage_eq_top_minus)

variable [Finite K]

theorem fullInvolutionOddCore_coordinatePlus {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) : FullInvolutionOddCore (coordinateQuadPlus n K) :=
  even_orthogonal_all_involution_full_centralizer_odd_core
    (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus (Or.inl rfl) n f
    ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩ K hK
    (MulEquiv.refl _)

theorem fullInvolutionOddCore_coordinateMinus {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    FullInvolutionOddCore (coordinateQuadMinus n K (by omega) b c) :=
  even_orthogonal_all_involution_full_centralizer_odd_core
    (StatedProj (StatedOmega (StatedQuadMinus n K b c))) .POmegaMinus (Or.inr rfl) n f
    ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirr,
      ⟨MulEquiv.refl _⟩⟩ (by omega) K hK b c hirr (MulEquiv.refl _)

theorem exists_conj_le_image_coordinatePlus {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (P : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))))
    (hP : IsPGroup 2 P) :
    ∃ ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      P.map (MulAut.conj ψ⁻¹).toMonoidHom ≤ matrixProjectiveImage (coordinateQuadPlus n K) := by
  rcases Nat.lt_or_ge n 5 with h4 | h5
  · obtain rfl : n = 4 := by omega
    exact CFSG.ComponentClassification.RankTwoHypIIOrthogonal.exists_conj_le_image_plus_four
      hf hK P hP
  · refine ⟨1, ?_⟩
    rw [matrixProjectiveImage_eq_top_plus K n h5]
    exact le_top

theorem hypothesisOne_coordinatePlus {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) : HypothesisOne (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  exact hypothesisOne_of_regular hf hK hn hreg.1 hreg.2
    (commutator_coordinateQuadPlus n K (by omega)) (fullInvolutionOddCore_coordinatePlus hf hK hn)
    (exists_conj_le_image_coordinatePlus hf hK hn)

theorem hypothesisOne_coordinateMinus {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    HypothesisOne (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) := by
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  exact hypothesisOne_of_regular hf hK hn hreg.1 hreg.2
    (commutator_coordinateQuadMinus n K b c hn hirr)
    (fullInvolutionOddCore_coordinateMinus hf hK hn hirr) fun _ _ =>
      ⟨1, by rw [matrixProjectiveImage_eq_top_minus K n hn b c hirr]; exact le_top⟩

theorem pow_two_eq_one_of_two_power_coordinatePlus {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {x : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hx : orderOf x = 2)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} {k : ℕ}
    (hβk : orderOf β = 2 ^ k) (hβx : β * x = x * β)
    (hβ : ∀ c, x c = c → Odd (orderOf c) → β c = c) : β ^ 2 = 1 := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  exact OmegaOuter.pow_two_eq_one_of_conj_le (exists_conj_le_image_coordinatePlus hf hK hn)
    (pow_two_eq_one_of_mem_image hf hK hn hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega))) hx hβk hβx hβ

theorem involutionCriterion_coordinatePlus {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n) {x : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (hx : orderOf x = 2) : InvolutionCriterion x := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  exact involutionCriterion_of_image_eq_top hf hK (by omega) hreg.1 hreg.2
    (commutator_coordinateQuadPlus n K (by omega)) (matrixProjectiveImage_eq_top_plus K n hn) hx

theorem involutionCriterion_coordinateMinus {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))}
    (hx : orderOf x = 2) : InvolutionCriterion x := by
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  exact involutionCriterion_of_image_eq_top hf hK hn hreg.1 hreg.2
    (commutator_coordinateQuadMinus n K b c hn hirr)
    (matrixProjectiveImage_eq_top_minus K n hn b c hirr) hx

end Coordinate

end OmegaAssembly

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv)
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

theorem hypothesisOne_of_lieModel_POmegaPlus {Y : Type} [Group Y] {n f : ℕ}
    (h : CFSG.Blueprint.LieModel Y .POmegaPlus n 2 f) : HypothesisOne Y := by
  rcases h with ⟨-, ⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
      (OmegaAssembly.hypothesisOne_coordinatePlus hf hK hn)
  · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · cases ht

theorem hypothesisOne_of_lieModel_POmegaMinus {Y : Type} [Group Y] {n f : ℕ}
    (h : CFSG.Blueprint.LieModel Y .POmegaMinus n 2 f) : HypothesisOne Y := by
  rcases h with ⟨-, ⟨-, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ |
    ⟨-, ht, -⟩
  · exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv
      (coordinateMinusWitnessEquiv K (by omega) b c e).symm
      (OmegaAssembly.hypothesisOne_coordinateMinus hf hK hn hirr)
  · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · cases ht

end CFSG.SeitzReduction
