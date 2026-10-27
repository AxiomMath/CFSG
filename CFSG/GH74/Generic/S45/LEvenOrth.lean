module

public import CFSG.GH74.Generic.S45.LEvenClassical
public import CFSG.LocalAnalysis.SteinbergBTEvenOrthogonalFixedNoSL2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaInvolutionConjugacy

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup Matrix QuadraticMap Module CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)

variable {D : Type} [Group D]

theorem orthogonal_component_false {f r : ℕ} {ya : MulAut D} (hya2 : ya * ya = 1) (hya1 : ya ≠ 1)
    {L' : Subgroup (MulAut D)}
    (hL' : CFSG.Assembly.IsComponentOf L'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner D ⊓
        Subgroup.centralizer ({ya} : Set (MulAut D))))
    (h4 : ∀ x : ↥L', orderOf x ≠ 4) {F : Type} [Field F] [Finite F]
    {Q : QuadraticForm F (Fin (2 * r) → F)} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) (hr : 4 ≤ r)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule F (Fin (2 * r) → F), Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (θ : D ≃* matrixProjectiveDerived Q)
    (hconj : ∀ β : MulAut (matrixProjectiveDerived Q), β * β = 1 →
      ∃ γ, γ⁻¹ * β * γ ∈ matrixProjectiveImage Q) : False := by
  classical
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hF
  let ψ : MulAut D ≃* MulAut (matrixProjectiveDerived Q) := MulAut.congr θ
  have hββ : ψ ya * ψ ya = 1 := by rw [← map_mul, hya2, map_one]
  obtain ⟨γ, hγ⟩ := hconj _ hββ
  let Θ : MulAut D ≃* MulAut (matrixProjectiveDerived Q) := ψ.trans (MulAut.conj γ⁻¹)
  have hΘya : Θ ya = γ⁻¹ * ψ ya * γ := by
    show (MulAut.conj γ⁻¹) (ψ ya) = _
    rw [MulAut.conj_apply, inv_inv]
  have hα'E : Θ ya ∈ matrixProjectiveImage Q := by rw [hΘya]; exact hγ
  have hα'2 : Θ ya * Θ ya = 1 := by rw [← map_mul, hya2, map_one]
  have hα'1 : Θ ya ≠ 1 := fun h => hya1 (Θ.injective (by rw [h, map_one]))
  have hα'o : orderOf (Θ ya) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hα'2) hα'1
  have hinner : (CFSG.ComponentClassification.OuterAutomorphisms.inner D).map Θ.toMonoidHom =
      CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    have h1 : (CFSG.ComponentClassification.OuterAutomorphisms.inner D).map ψ.toMonoidHom =
        CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr θ
    have hn : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived Q)).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    show (CFSG.ComponentClassification.OuterAutomorphisms.inner D).map
      (((MulAut.conj γ⁻¹ : MulAut (MulAut (matrixProjectiveDerived Q))).toMonoidHom).comp
        ψ.toMonoidHom) = _
    rw [← Subgroup.map_map, h1]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hn.conj_mem y hy γ⁻¹
    · intro hx
      refine ⟨γ * x * γ⁻¹, hn.conj_mem x hx γ, ?_⟩
      simp
      group
  have hcent : (Subgroup.centralizer ({ya} : Set (MulAut D))).map Θ.toMonoidHom =
      Subgroup.centralizer ({Θ ya} : Set (MulAut (matrixProjectiveDerived Q))) := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg Θ h
      simpa using this
    · intro h
      apply Θ.injective
      simpa using h
  have hD : (CFSG.ComponentClassification.OuterAutomorphisms.inner D ⊓
      Subgroup.centralizer ({ya} : Set (MulAut D))).map Θ.toMonoidHom =
      CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓
        Subgroup.centralizer ({Θ ya} : Set (MulAut (matrixProjectiveDerived Q))) := by
    rw [Subgroup.map_inf _ _ _ Θ.injective, hinner, hcent]
  have hL'' : CFSG.Assembly.IsComponentOf (L'.map Θ.toMonoidHom)
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓
        Subgroup.centralizer ({Θ ya} : Set (MulAut (matrixProjectiveDerived Q)))) := by
    rw [← hD]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff Θ.injective).2 hL'
  have h4'' : ∀ x : ↥(L'.map Θ.toMonoidHom), orderOf x ≠ 4 := by
    intro x hx
    obtain ⟨l, hl, hlx⟩ := x.2
    apply h4 ⟨l, hl⟩
    have h1 : orderOf (x : MulAut (matrixProjectiveDerived Q)) = 4 := by
      rw [Subgroup.orderOf_coe]
      exact hx
    rw [← hlx] at h1
    rw [← Subgroup.orderOf_coe]
    simpa [MulEquiv.orderOf_eq] using h1
  obtain ⟨S₀, hS₀, hS₀α⟩ := exists_unit_rep hα'E
  by_cases hσ : S₀.val.right = 1
  · exact CFSG.LocalAnalysis.SteinbergBT.orthogonal_fixed_linear_false hf hF hr hQ hT hE hα'o
      hS₀α hσ hL'' h4''
  · obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.SteinbergBT.orthogonal_fixed_field_orderOf_four hf hF hr
      hQ hT hE hα'E hα'o hS₀ hS₀α hσ hL''
    exact h4'' x hx

theorem orthogonal_false {S : Type} [Group S] (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {r f : ℕ} (hmodel : StatedClassicalModel S t r 2 f) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : False := by
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hSs hSnab
  have hconjE := (even_orthogonal_involutions_conjugate_into_semilinear_image S t ht r f hmodel).1
  rcases ht with rfl | rfl
  · obtain ⟨⟨-, hf, hr⟩, F, _, _, hF, ⟨θ₀⟩⟩ := id hmodel
    have hreg := regular_coordinateQuadPlus r F (by omega)
    obtain ⟨L', φ, ρ, hL', h4, -⟩ := even_apply hZ (coordinatePlusWitnessEquiv F θ₀) hQ
    exact orthogonal_component_false hQ.sq hQ.ne hL' h4 hF hf hr hreg.1 hreg.2
      (commutator_coordinateQuadPlus r F (by omega)) (coordinatePlusWitnessEquiv F θ₀)
      ((hconjE F hF θ₀).1)
  · obtain ⟨⟨-, hf, hr⟩, F, _, _, hF, b, c, hirr, ⟨θ₀⟩⟩ := id hmodel
    have hreg := regular_coordinateQuadMinus r F b c hr hirr
    obtain ⟨L', φ, ρ, hL', h4, -⟩ := even_apply hZ (coordinateMinusWitnessEquiv F (by omega) b c θ₀) hQ
    exact orthogonal_component_false hQ.sq hQ.ne hL' h4 hF hf hr hreg.1 hreg.2
      (commutator_coordinateQuadMinus r F b c hr hirr)
      (coordinateMinusWitnessEquiv F (by omega) b c θ₀) (hconjE (by omega) F hF b c hirr θ₀)

end CFSG.GH74.Generic.S45
