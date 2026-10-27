module

public import CFSG.ClassicalGroups.Orthogonal.RootInvolutionClass
public import CFSG.ClassicalGroups.Orthogonal.RootInvolutionAxis
public import CFSG.ClassicalGroups.Orthogonal.RootInvolutionSL2
public import CFSG.ClassicalGroups.Orthogonal.RootInvolutionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitCoordinates

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Module QuadraticMap CFSG.RankThree.GF2n.Smith81

section Generic

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_hypPairs_eq_eichler_of_isOrthA2 [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {t : V ≃ₗ[K] V} (ht : IsOrthA2 Q t) :
    ∃ P R : HypPair Q, P.Orth R ∧ t = eichler Q P.e R.e := by
  obtain ⟨a, b, hli, ha, hb, hab, rfl⟩ := ht.exists_eq_eichler hQ
  obtain ⟨P, R, hPa, hRb, hPR⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit.exists_two_hypPairs_of_family hQ hli
      (fun i => by fin_cases i <;> simp [ha, hb])
      (fun i j => by
        fin_cases i <;> fin_cases j <;>
          simp [polar_self_eq_zero ha, polar_self_eq_zero hb, hab, polar_comm Q b a])
  exact ⟨P, R, hPR, by simp [hPa, hRb]⟩

variable [Finite K] [CharP K 2] [FiniteDimensional K V]

theorem exists_rootRadical_of_elementaryGroup (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hm : finrank K V = 2 * m) (hm3 : 3 ≤ m) {t : V ≃ₗ[K] V} (htE : t ∈ elementaryGroup Q)
    (ht : orderOf t = 2)
    (hord : ∀ g ∈ elementaryGroup Q,
      orderOf (t * (g * t * g⁻¹)) ∣ 4 ∨ Odd (orderOf (t * (g * t * g⁻¹)))) :
    ∃ P R : Subgroup (V ≃ₗ[K] V), P ≤ elementaryGroup Q ∧ P ≤ Subgroup.centralizer {t} ∧
      Subgroup.closure {g | g ∈ P ∧ orderOf g = 2} = P ∧ R ≤ P ∧
      (∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) ∧ IsPGroup 2 R ∧ R ≤ ⁅P, P⁆ ∧
      Nat.card ↥(Subgroup.centralizer (R : Set (V ≃ₗ[K] V)) ⊓ elementaryGroup Q) = Nat.card K := by
  obtain ⟨P, R, hPR, rfl⟩ := exists_hypPairs_eq_eichler_of_isOrthA2 hQ
    (isOrthA2_of_forall_orderOf_mul_conj hQ hm hm3 htE ht hord)
  have hV : 6 ≤ finrank K V := by omega
  exact ⟨axisParabolic Q P R, axisRadical Q P.e R.e, axisParabolic_le_elementaryGroup P R,
    axisParabolic_le_centralizer hPR, closure_involutions_axisParabolic P R,
    axisRadical_le_axisParabolic P R, fun p hp r hr => conj_mem_axisRadical hPR hp hr,
    isPGroup_axisRadical hPR, axisRadical_le_commutator hQ hPR hV,
    card_centralizer_axisRadical_inf hQ hPR hV⟩

theorem exists_inv_conj_of_elementaryGroup (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hm : finrank K V = 2 * m) (hm3 : 3 ≤ m) {t : V ≃ₗ[K] V} (htE : t ∈ elementaryGroup Q)
    (ht : orderOf t = 2)
    (hord : ∀ g ∈ elementaryGroup Q,
      orderOf (t * (g * t * g⁻¹)) ∣ 4 ∨ Odd (orderOf (t * (g * t * g⁻¹)))) :
    ∃ g ∈ elementaryGroup Q, orderOf g = Nat.card K + 1 ∧ t * g * t⁻¹ = g⁻¹ := by
  obtain ⟨P, R, hPR, rfl⟩ := exists_hypPairs_eq_eichler_of_isOrthA2 hQ
    (isOrthA2_of_forall_orderOf_mul_conj hQ hm hm3 htE ht hord)
  exact exists_orderOf_eq_card_add_one_conj_eichler hPR

end Generic

private theorem exists_injective_of_rootInvolutionModel {X : Type} [Group X] {m x : ℕ}
    (hΩ : CFSG.Blueprint.LieModel X .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel X .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel X .PSU 4 2 x)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module K V) (_ : FiniteDimensional K V) (Q : QuadraticForm K V)
      (ψ : X →* (V ≃ₗ[K] V)), Nat.card K = 2 ^ x ∧ (polarBilin Q).Nondegenerate ∧
        finrank K V = 2 * m ∧ 3 ≤ m ∧ Function.Injective ψ ∧ ψ.range = elementaryGroup Q := by
  obtain ⟨K, _, _, _, V, _, _, _, Q, hK, hQ, hm, hm3, ⟨φ⟩⟩ :=
    exists_quadraticSpace_of_rootInvolutionModel hΩ
  refine ⟨K, inferInstance, inferInstance, inferInstance, V, inferInstance, inferInstance,
    inferInstance, Q, (elementaryGroup Q).subtype.comp φ.toMonoidHom, hK, hQ, hm, hm3,
    Subtype.val_injective.comp φ.injective, ?_⟩
  ext g
  refine ⟨?_, fun hg => ⟨φ.symm ⟨g, hg⟩, by simp⟩⟩
  rintro ⟨y, rfl⟩
  exact (φ y).2

theorem exists_rootRadical_of_lieModel_omega {X : Type} [Group X] [Finite X] {m x : ℕ}
    (hΩ : CFSG.Blueprint.LieModel X .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel X .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel X .PSU 4 2 x))
    {t : X} (ht : orderOf t = 2)
    (hord : ∀ g : X, orderOf (t * (g * t * g⁻¹)) ∣ 4 ∨ Odd (orderOf (t * (g * t * g⁻¹)))) :
    ∃ P R : Subgroup X, P ≤ Subgroup.centralizer {t} ∧
      Subgroup.closure {g : X | g ∈ P ∧ orderOf g = 2} = P ∧
      R ≤ P ∧ (∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) ∧ IsPGroup 2 R ∧ R ≤ ⁅P, P⁆ ∧
      Nat.card (Subgroup.centralizer (R : Set X)) = 2 ^ x := by
  obtain ⟨K, _, _, _, V, _, _, _, Q, ψ, hK, hQ, hm, hm3, hψ, hrange⟩ :=
    exists_injective_of_rootInvolutionModel hΩ
  have hord' := forall_orderOf_mul_conj_of_injective hψ hord
  rw [hrange] at hord'
  have htE : ψ t ∈ elementaryGroup Q := by
    rw [← hrange]
    exact ⟨t, rfl⟩
  obtain ⟨P, R, hPE, hPt, hPgen, hRP, hRn, hR2, hRc, hC⟩ :=
    exists_rootRadical_of_elementaryGroup hQ hm hm3 htE
      (by rw [orderOf_injective ψ hψ, ht]) hord'
  rw [← hrange] at hPE hC
  rw [hK] at hC
  exact exists_rootRadical_of_injective hψ hPE hPt hPgen hRP hRn hR2 hRc hC

theorem exists_inv_conj_of_lieModel_omega {X : Type} [Group X] [Finite X] {m x : ℕ}
    (hΩ : CFSG.Blueprint.LieModel X .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel X .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel X .PSU 4 2 x))
    {t : X} (ht : orderOf t = 2)
    (hord : ∀ g : X, orderOf (t * (g * t * g⁻¹)) ∣ 4 ∨ Odd (orderOf (t * (g * t * g⁻¹)))) :
    ∃ g : X, orderOf g = 2 ^ x + 1 ∧ t * g * t⁻¹ = g⁻¹ := by
  obtain ⟨K, _, _, _, V, _, _, _, Q, ψ, hK, hQ, hm, hm3, hψ, hrange⟩ :=
    exists_injective_of_rootInvolutionModel hΩ
  have hord' := forall_orderOf_mul_conj_of_injective hψ hord
  rw [hrange] at hord'
  have htE : ψ t ∈ elementaryGroup Q := by
    rw [← hrange]
    exact ⟨t, rfl⟩
  obtain ⟨g, hgE, hgo, hinv⟩ :=
    exists_inv_conj_of_elementaryGroup hQ hm hm3 htE (by rw [orderOf_injective ψ hψ, ht]) hord'
  rw [hK] at hgo
  exact exists_inv_conj_of_injective hψ (by rw [hrange]; exact hgE) hgo hinv

end CFSG.ClassicalGroups.Orthogonal
