module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
open CFSG.LocalAnalysis.ComponentInitial

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]

@[expose] def plusBasisIsometry {n : ℕ} {Q₀ : QuadraticForm k W}
    (b : Module.Basis (Fin n ⊕ Fin n) k W)
    (hb : ∀ x y : Fin n → k,
      Q₀ (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) = ∑ i, x i * y i) :
    Q₀.IsometryEquiv (quadPlus n k) where
  toLinearEquiv := b.equivFun
  map_app' w := by
    have hw : w = ∑ i, b.repr w (.inl i) • b (.inl i) + ∑ i, b.repr w (.inr i) • b (.inr i) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Fintype.sum_sum_type]
    change quadPlus n k (b.equivFun w) = Q₀ w
    conv_rhs => rw [hw]
    rw [hb, quadPlus_apply]
    rfl

@[expose] def minusBasisIsometry {n : ℕ} {Q₀ : QuadraticForm k W} {β γ : k}
    (b : Module.Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) k W)
    (hb : ∀ (x y : Fin (n - 1) → k) (s t : k),
      Q₀ (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr (.inl i)) + s • b (.inr (.inr 0)) +
        t • b (.inr (.inr 1))) = ∑ i, x i * y i + s ^ 2 + β * s * t + γ * t ^ 2) :
    Q₀.IsometryEquiv (quadMinus n k β γ) where
  toLinearEquiv := b.equivFun
  map_app' w := by
    have hw : w = ∑ i, b.repr w (.inl i) • b (.inl i) +
        ∑ i, b.repr w (.inr (.inl i)) • b (.inr (.inl i)) +
          b.repr w (.inr (.inr 0)) • b (.inr (.inr 0)) +
            b.repr w (.inr (.inr 1)) • b (.inr (.inr 1)) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
      abel
    change quadMinus n k β γ (b.equivFun w) = Q₀ w
    conv_rhs => rw [hw]
    rw [hb, quadMinus_apply]
    rfl

theorem exists_coordinate_isometry [Finite k] [CharP k 2] [FiniteDimensional k W] {n : ℕ}
    (hn : 4 ≤ n) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 2 * n) :
    ∃ Qc : QuadraticForm k (Fin (2 * n) → k), Nonempty (Q₀.IsometryEquiv Qc) ∧
      Qc.polarBilin.Nondegenerate ∧
      (∃ T : Submodule k (Fin (2 * n) → k), Module.finrank k T = 3 ∧ ∀ x ∈ T, Qc x = 0) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup Qc, TauCeti.QuadraticMap.orthogonalGroup Qc⁆ =
        elementaryGroup Qc := by
  rcases (finite_even_regular_quadratic_normal_forms Q₀ hQ₀).2.2.1 n (by omega) hdim with
    ⟨b, hb⟩ | ⟨β, γ, -, hroot, b, hb⟩
  · have hreg := regular_coordinateQuadPlus n k (by omega)
    exact ⟨coordinateQuadPlus n k,
      ⟨(plusBasisIsometry b hb).trans (coordinatePlusIsometry n k)⟩, hreg.1, hreg.2,
      commutator_coordinateQuadPlus n k (by omega)⟩
  · have hreg := regular_coordinateQuadMinus n k β γ hn hroot
    exact ⟨coordinateQuadMinus n k (by omega) β γ,
      ⟨(minusBasisIsometry b hb).trans (coordinateMinusIsometry n k (by omega) β γ)⟩, hreg.1,
      hreg.2, commutator_coordinateQuadMinus n k β γ hn hroot⟩

theorem derived_simple_even [Finite k] [CharP k 2] [FiniteDimensional k W] {n : ℕ}
    (hn : 4 ≤ n) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 2 * n) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q₀, TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ =
        elementaryGroup Q₀ ∧
      IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ ∧
      Even (Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆) := by
  obtain ⟨Qc, ⟨ψ⟩, -, -, hEc⟩ := exists_coordinate_isometry hn Q₀ hQ₀ hdim
  have hE₀ := derived_eq_elementary_isometry ψ.symm hEc
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ :=
    (finite_even_regular_quadratic_normal_forms Q₀ hQ₀).2.2.2.2.2 n hdim hn
  have hsimple := isSimpleGroup_projElementary_of_hypPairs hQ₀ h12 h13 h23
  have hscal : (scalars k W).subgroupOf (elementaryGroup Q₀) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hg)
    have hgO : (g : W ≃ₗ[k] W) ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀ :=
      elementaryGroup_le_orthogonalGroup Q₀ g.2
    have hv : Q₀ (P₁.e + P₁.f) = 1 := by
      rw [QuadraticMap.map_add Q₀, P₁.Q_e, P₁.Q_f, P₁.polar_ef, zero_add, zero_add]
    have h1 := map_of_mem hgO (P₁.e + P₁.f)
    rw [hc, QuadraticMap.map_smul, hv, smul_eq_mul, mul_one] at h1
    have hc1 : c = 1 := UnitaryHigher.eq_one_of_mul_self_eq_one_of_charTwo h1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    rw [hc, hc1, one_smul]
    rfl
  have e₂ : ↥(elementaryGroup Q₀) ≃* ProjElementary Q₀ :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hscal.symm)
  have e₁ : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀, TauCeti.QuadraticMap.orthogonalGroup Q₀⁆
      ≃* ↥(elementaryGroup Q₀) := MulEquiv.subgroupCongr hE₀
  refine ⟨hE₀, (e₁.trans e₂).isSimpleGroup, ?_⟩
  have hne : P₂.e ≠ 0 := fun h => by
    have h1 := P₂.polar_ef
    rw [h, polar_zero_left] at h1
    exact zero_ne_one h1
  have hE2 : eichler Q₀ P₁.e P₂.e ^ 2 = 1 := by
    rw [pow_two, eichler_mul h12.ee h12.ee, ← two_smul k P₂.e, CharTwo.two_eq_zero, zero_smul,
      eichler_zero_right]
  have hE1 : eichler Q₀ P₁.e P₂.e ≠ 1 := by
    intro h
    have h1 : eichler Q₀ P₁.e P₂.e P₁.f = P₁.f := by rw [h]; rfl
    rw [eichler_apply P₁.Q_e h12.ee, P₁.polar_fe, h12.fe, P₂.Q_e,
      zero_mul, add_zero, zero_smul, sub_zero, one_smul, add_eq_left] at h1
    exact hne h1
  have hord : orderOf (eichler Q₀ P₁.e P₂.e) = 2 := orderOf_eq_prime hE2 hE1
  have hmem : eichler Q₀ P₁.e P₂.e ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
      TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ := hE₀ ▸ eichler_mem_elementaryGroup Q₀ _ _
  exact even_iff_two_dvd.mpr (hord ▸ Subgroup.orderOf_dvd_natCard _ hmem)

end CFSG.ComponentClassification.UnbalancedCatalog
