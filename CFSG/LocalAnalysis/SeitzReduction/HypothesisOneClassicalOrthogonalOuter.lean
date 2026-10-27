module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearOuterBasic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonalRigid
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaLinearInvolution
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags

public section

namespace CFSG.SeitzReduction

namespace OmegaOuter

open Subgroup

theorem comap_conj_le_closure_odd_fixed {C : Type*} [Group C] [Finite C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {x : MulAut C}
    {N : Subgroup (MulAut C)} (hNinn : N ≤ (MulAut.conj : C →* MulAut C).range)
    (hNx : N ≤ centralizer ({x} : Set (MulAut C))) (hNp : ⁅N, N⁆ = N) :
    N.comap (MulAut.conj : C →* MulAut C) ≤ closure {c : C | x c = c ∧ Odd (orderOf c)} := by
  refine le_closure_odd_fixed_of_perfect (fun c hc => apply_eq_of_mem_comap_conj hinj hNx hc) ?_
  apply map_injective hinj
  rw [map_commutator, map_comap_conj_eq_of_le_range hNinn, hNp]

theorem pow_two_eq_one_of_inner_perfect {C : Type*} [Group C] [Finite C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {x : MulAut C} (hx : x ^ 2 = 1)
    {N : Subgroup (MulAut C)} (hNinn : N ≤ (MulAut.conj : C →* MulAut C).range)
    (hNx : N ≤ centralizer ({x} : Set (MulAut C))) (hNp : ⁅N, N⁆ = N)
    {E : Subgroup (MulAut C)}
    (hcent : E ⊓ centralizer ({x} : Set (MulAut C)) ⊓ centralizer (N : Set (MulAut C)) ≤
      zpowers x)
    {β : MulAut C} (hβE : β ∈ E) (hβx : β * x = x * β)
    (hβ : ∀ c : C, x c = c → Odd (orderOf c) → β c = c) : β ^ 2 = 1 := by
  have hD := comap_conj_le_closure_odd_fixed hinj hNinn hNx hNp
  have hβN := mem_centralizer_of_forall_comap_conj hNinn fun c hc =>
    apply_eq_self_of_mem_closure (fun d hd => hβ d hd.1 hd.2) (hD hc)
  rcases eq_one_or_eq_of_mem_zpowers hx
      (hcent ⟨⟨hβE, mem_centralizer_singleton_iff.2 hβx⟩, hβN⟩) with h | h
  · rw [h, one_pow]
  · rw [h, hx]

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)

variable {K : Type} [Field K] {n : ℕ} {Q : QuadraticForm K (Fin (2 * n) → K)}

theorem conj_injective_of_regular [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hn : 1 ≤ n) :
    Function.Injective
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q y
  rw [← kappa_derived_eq_conj] at hy
  have h1 : (matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)
      (Subgroup.inclusion (matrixDerived_le_isometries Q) g) =
      (matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q) 1 := by
    rw [map_one]
    exact hy
  have h2 : g = 1 :=
    Subgroup.inclusion_injective _ ((kappa_inclusion_injective hQ hT hE (by omega) h1).trans
      (map_one _).symm)
  rw [h2, map_one]

section Field

theorem field_pow_two_eq_one {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {α : MulAut (matrixProjectiveDerived Q)} (hα2 : orderOf α = 2) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ : S.val.right ≠ 1) :
    ∀ β ∈ matrixProjectiveImage Q, β * α = α * β →
      (∀ c, α c = c → Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hα2' : α ^ 2 = 1 := by
    have h := pow_orderOf_eq_one α
    rwa [hα2] at h
  obtain ⟨-, -, hsimp, -, ext, -, -, hinj, hinner, hle, -, hcent⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α ⟨S, hSα⟩ hα2 S hS hSα hσ
  set N := (extKappa Q ext).range with hNdef
  have hαX : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := fun hX =>
    hσ (RankTwoHypIIOrthogonal.right_eq_one_of_mem_inner hQ hT hE (by omega) hS (hSα ▸ hX))
  have eN : pairDescentDerived hS ≃* N := MonoidHom.ofInjective hinj
  have hNs : IsSimpleGroup N := eN.symm.isSimpleGroup
  have hnc : ¬ ∀ a b : N, a * b = b * a := by
    intro hcomm
    have hNC : N ≤ centralizer (N : Set (MulAut (matrixProjectiveDerived Q))) := fun y hy =>
      mem_centralizer_iff.mpr fun z hz => congrArg Subtype.val (hcomm ⟨z, hz⟩ ⟨y, hy⟩)
    have hNz : N ≤ zpowers α := by
      rw [← hcent]
      exact le_inf hle hNC
    have hbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases eq_one_or_eq_of_mem_zpowers hα2' (hNz hy) with h1 | h1
      · exact (mem_bot).mpr h1
      · exact absurd (h1 ▸ hinner hy) hαX
    have := hNs.toNontrivial
    rw [hbot] at this
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this
  have hNp : ⁅N, N⁆ = N := RankTwoHypIIY.commutator_eq_self_of_isSimpleGroup hNs hnc
  intro β hβ hβα hβc
  exact pow_two_eq_one_of_inner_perfect (conj_injective_of_regular hQ hT hE (by omega)) hα2'
    hinner (hle.trans inf_le_right) hNp hcent.le hβ hβα hβc

theorem involutionCriterion_field_of_image_eq_top {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (htop : matrixProjectiveImage Q = ⊤)
    {α : MulAut (matrixProjectiveDerived Q)} (hα2 : orderOf α = 2) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ : S.val.right ≠ 1) : InvolutionCriterion α := fun β hβα hβc =>
  field_pow_two_eq_one hf hK hn hQ hT hE hα2 hS hSα hσ β (htop ▸ mem_top β) hβα hβc

end Field

section Symmetry

theorem symmetryAut_pow_two_eq_one {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {v : Fin (2 * n) → K} (hv : Q v = 1) :
    ∀ β ∈ matrixProjectiveImage Q, β * symmetryAut Q v = symmetryAut Q v * β →
      (∀ c, symmetryAut Q v c = c → Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hd : 1 ≤ 2 * n := by omega
  set α := symmetryAut Q v with hαdef
  set N := OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓ centralizer {α} with hNdef
  have hα2 : α ^ 2 = 1 := symmetryAut_sq Q v
  have hαX : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    RankTwoHypIIOrthogonal.symmetryAut_not_mem_inner hQ hT hE (by omega) hv
  have hinj : Function.Injective (EvenOrthSelector.symKappa Q v) :=
    (kappa_inclusion_injective hQ hT hE hd).comp (Subgroup.inclusion_injective _)
  obtain ⟨eB⟩ := EvenOrthSelector.exists_derivedSymmetryEquiv hQ hT hE hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hdim : Module.finrank K (vQuot Q v) = 2 * (n - 1) := by
    have := finrank_vQuot hQ hv
    omega
  obtain ⟨hsI, -⟩ := RankTwoHypIIOrthogonal.isometryGroup_simple (vQuotForm_isAlt Q v)
    (vQuotForm_nondegenerate hQ hv0) hK (by omega : 3 ≤ n - 1) hdim
  have eN : CatalogueBAlternatingIsometry.isometryGroup (vQuotForm Q v) ≃* N :=
    ((eB.trans (bilinIsometryGroupEquiv _)).symm.trans (MonoidHom.ofInjective hinj)).trans
      (MulEquiv.subgroupCongr (EvenOrthSelector.range_symKappa hQ hT hE hd v))
  have hNs : IsSimpleGroup N := eN.symm.isSimpleGroup
  have hcent : matrixProjectiveImage Q ⊓ centralizer ({α} : Set _) ⊓
      centralizer (N : Set (MulAut (matrixProjectiveDerived Q))) ≤ zpowers α := fun e he =>
    RankTwoHypIIOrthogonal.mem_zpowers_of_commute hQ hT hE (by omega) hv he.1.1
      (mem_centralizer_singleton_iff.mp he.1.2) he.2
  have hnc : ¬ ∀ a b : N, a * b = b * a := by
    intro hcomm
    have hbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyN : y ∈ centralizer (N : Set (MulAut (matrixProjectiveDerived Q))) :=
        mem_centralizer_iff.mpr fun z hz => congrArg Subtype.val (hcomm ⟨z, hz⟩ ⟨y, hy⟩)
      rcases eq_one_or_eq_of_mem_zpowers hα2
          (hcent ⟨⟨matrixProjective_inner_le_image Q hy.1, hy.2⟩, hyN⟩) with h1 | h1
      · exact (mem_bot).mpr h1
      · exact absurd (h1 ▸ hy.1) hαX
    have := hNs.toNontrivial
    rw [hbot] at this
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this
  have hNp : ⁅N, N⁆ = N := RankTwoHypIIY.commutator_eq_self_of_isSimpleGroup hNs hnc
  intro β hβ hβα hβc
  exact pow_two_eq_one_of_inner_perfect (conj_injective_of_regular hQ hT hE (by omega)) hα2
    inf_le_left inf_le_right hNp hcent hβ hβα hβc

theorem involutionCriterion_symmetryAut_of_image_eq_top {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (htop : matrixProjectiveImage Q = ⊤) {v : Fin (2 * n) → K}
    (hv : Q v = 1) : InvolutionCriterion (symmetryAut Q v) := fun β hβα hβc =>
  symmetryAut_pow_two_eq_one hf hK hn hQ hT hE hv β (htop ▸ mem_top β) hβα hβc

theorem reflection_pow_two_eq_one {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {s : matrixIsometries Q} (hss : s * s = 1) (hs1 : s ≠ 1)
    (hr : (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank ≤ 1) :
    ∀ β ∈ matrixProjectiveImage Q,
      β * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) * β →
      (∀ c, matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) c = c →
        Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hss' : (s : GL (Fin (2 * n)) K) * s = 1 := by
    rw [← Subgroup.coe_mul, hss, Subgroup.coe_one]
  have hs1' : (s : GL (Fin (2 * n)) K) ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨v, hv, hsv⟩ := OmegaRadical.exists_symmetry_of_rank_le_one hQ s.2 hss' hs1' hr
  have hs : s = symmetryIsometry Q v := Subtype.ext hsv
  subst hs
  exact symmetryAut_pow_two_eq_one hf hK hn hQ hT hE hv

end Symmetry

section Coordinate

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem involutionCriterion_field_plus [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n) {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (hα2 : orderOf α = 2) {S : similarityPairs (coordinateQuadPlus n K)}
    (hS : S ∈ unitMultiplierPairs (coordinateQuadPlus n K))
    (hSα : matrixProjectiveConjugationHom (coordinateQuadPlus n K) S = α)
    (hσ : S.val.right ≠ 1) : InvolutionCriterion α := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  exact involutionCriterion_field_of_image_eq_top hf hK (by omega) hreg.1 hreg.2
    (commutator_coordinateQuadPlus n K (by omega))
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn) hα2 hS hSα
    hσ

theorem involutionCriterion_symmetryAut_plus [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) {v : Fin (2 * n) → K}
    (hv : coordinateQuadPlus n K v = 1) :
    InvolutionCriterion (symmetryAut (coordinateQuadPlus n K) v) := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  exact involutionCriterion_symmetryAut_of_image_eq_top hf hK (by omega) hreg.1 hreg.2
    (commutator_coordinateQuadPlus n K (by omega))
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn) hv

theorem involutionCriterion_field_minus [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))}
    (hα2 : orderOf α = 2) {S : similarityPairs (coordinateQuadMinus n K (by omega) b c)}
    (hS : S ∈ unitMultiplierPairs (coordinateQuadMinus n K (by omega) b c))
    (hSα : matrixProjectiveConjugationHom (coordinateQuadMinus n K (by omega) b c) S = α)
    (hσ : S.val.right ≠ 1) : InvolutionCriterion α := by
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  exact involutionCriterion_field_of_image_eq_top hf hK hn hreg.1 hreg.2
    (commutator_coordinateQuadMinus n K b c hn hirr)
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr)
    hα2 hS hSα hσ

theorem involutionCriterion_symmetryAut_minus [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {v : Fin (2 * n) → K} (hv : coordinateQuadMinus n K (by omega) b c v = 1) :
    InvolutionCriterion (symmetryAut (coordinateQuadMinus n K (by omega) b c) v) := by
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  exact involutionCriterion_symmetryAut_of_image_eq_top hf hK hn hreg.1 hreg.2
    (commutator_coordinateQuadMinus n K b c hn hirr)
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr) hv

end Coordinate

end OmegaOuter

end CFSG.SeitzReduction
