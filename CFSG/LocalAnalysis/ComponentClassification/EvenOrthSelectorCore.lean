module

public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelectorField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaLinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents

public noncomputable section

namespace CFSG.ComponentClassification.EvenOrthSelector

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (evenOrthogonalRealization_of_regular)

variable {K : Type} [Field K]

theorem linear_component {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : matrixIsometries Q}
    (hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2)
    {X : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hX : CFSG.Assembly.IsComponentOf X (inner (matrixProjectiveDerived Q) ⊓
      Subgroup.centralizer {matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)})) :
    IsSimpleGroup X ∧ Nonempty (X ≃* StatedSp (n - 1) K) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := OmegaRadical.finite_mulAut_matrixProjectiveDerived Q
  have hss : s * s = 1 := by
    apply OmegaRadical.isometryKappa_injective hQ hT hE
    rw [map_mul, map_one]
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) *
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = 1
    have h2 := pow_orderOf_eq_one
      (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))
    rw [hs2] at h2
    rw [← pow_two]
    exact h2
  have hs1 : (s : GL (Fin (2 * n)) K) ≠ 1 := by
    intro h
    have h1 : s = 1 := Subtype.ext h
    rw [h1, map_one, map_one, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  by_cases hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank
  · exfalso
    exact UnbalancingLocal.EvenOrthogonalComponents.no_component_of_two_le_rank hQ hT hE
      (inner (matrixProjectiveDerived Q)) le_rfl (matrixProjective_inner_le_image Q) s hs2 hr
      (X.subgroupOf _)
      ((LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hX.1).mp hX)
  · obtain ⟨v, hv, hsv⟩ := OmegaRadical.exists_symmetry_of_rank_le_one hQ s.2
      (congrArg Subtype.val hss) hs1 (by omega)
    have hincl : s = symmetryIsometry Q v := Subtype.ext hsv
    subst hincl
    exact symmetry_component hQ hT hE hK rfl hn hv hX

theorem semilinear_component {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {α : MulAut (matrixProjectiveDerived Q)} (hα : α ∈ matrixProjectiveImage Q)
    (hα2 : orderOf α = 2) {X : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hX : CFSG.Assembly.IsComponentOf X
      (inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {α})) :
    IsSimpleGroup X ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (g : ℕ), Nat.card k = 2 ^ g ∧
      ∃ ι : StatedSp (n - 1) k →* X, Function.Injective ι := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨S, hS, hSα⟩ := exists_unit_rep hα
  by_cases hσ : S.val.right = 1
  · obtain ⟨-, -, -, -, F, hF, hker, -, -⟩ :=
      evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
    have hmem : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) ∈
        F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = α :=
      hs.trans hSα
    rw [← hs'] at hα2 hX
    obtain ⟨hXs, ⟨eX⟩⟩ := linear_component hf hK hn hQ hT hE hα2 hX
    exact ⟨hXs, K, inferInstance, inferInstance, f, hK, eX.symm.toMonoidHom, eX.symm.injective⟩
  · exact field_component hf hK hn hQ hT hE hα hα2 hS hSα hσ hX

end CFSG.ComponentClassification.EvenOrthSelector
