module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEndFieldBasic
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAut
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldPair)
open CFSG.SeitzReduction.F4Pilot (normalizerMulAut)

section FieldHom

variable (F : Type) [Field F] (n : ℕ)

theorem fieldPair_mul (σ τ : F ≃+* F) :
    fieldPair (coordinateQuadPlus n F) (σ * τ) (E7Pilot.coordinateQuadPlus_fieldMap n (σ * τ)) =
      fieldPair (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ) *
        fieldPair (coordinateQuadPlus n F) τ (E7Pilot.coordinateQuadPlus_fieldMap n τ) := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change (1 : GL (Fin (2 * n)) F) = 1 * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
      (Fin (2 * n)) F σ 1
    rw [map_one, one_mul]
  · rfl

theorem fieldPair_one :
    fieldPair (coordinateQuadPlus n F) 1 (E7Pilot.coordinateQuadPlus_fieldMap n 1) = 1 := by
  apply Subtype.ext
  apply SemidirectProduct.ext <;> rfl

@[expose] noncomputable def fieldAutHom :
    (F ≃+* F) →* MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)) where
  toFun σ := fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ)
  map_one' := by
    change matrixProjectiveConjugationHom _ (fieldPair _ _ _) = 1
    rw [fieldPair_one, map_one]
  map_mul' σ τ := by
    change matrixProjectiveConjugationHom _ (fieldPair _ _ _) =
      matrixProjectiveConjugationHom _ (fieldPair _ _ _) *
        matrixProjectiveConjugationHom _ (fieldPair _ _ _)
    rw [fieldPair_mul, map_mul]

theorem fieldAutHom_apply (σ : F ≃+* F) :
    fieldAutHom F n σ =
      fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ) :=
  rfl

end FieldHom

@[expose] def OmegaPlusAutNormalFormInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 5 ≤ n →
    ∃ (Φ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)) →* (F ≃+* F))
      (γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))),
      (∀ g, Φ (MulAut.conj g) = 1) ∧ (∀ σ : F ≃+* F, Φ (fieldAutHom F n σ) = σ) ∧
      γ * γ = 1 ∧ Φ γ = 1 ∧ (∀ σ : F ≃+* F, γ * fieldAutHom F n σ = fieldAutHom F n σ * γ) ∧
      ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)), ∃ g, ∃ σ : F ≃+* F,
        α = MulAut.conj g * fieldAutHom F n σ ∨ α = MulAut.conj g * γ * fieldAutHom F n σ

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldRow_omegaPlus_of_unique (hNF : OmegaPlusAutNormalFormInput)
    (hset : SeitzSetting G L) {n : ℕ} (hn : 5 ≤ n) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {G₀ : Subgroup G} (hLG : L ≤ G₀) (htN : t ∈ normalizer (G₀ : Set G))
    {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus n F))
    (hψ : MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
      fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) →
      g ∈ normalizer (G₀ : Set G)) : False := by
  have : IsSimpleGroup G := hset.1
  obtain ⟨Φ, γ, hΦInn, hΦs, hγ2, hΦγ, hγs, hform⟩ := hNF F n hn
  obtain ⟨g, hg, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨σ₀, -, -, hzp, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hg hFc
  have : IsCyclic (F ≃+* F) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, hzp⟩
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  set ρ := normalizerMulAut ψ with hρ
  have hρt : ρ ⟨t, htN⟩ = fieldAutHom F n σ := hψ
  have hout : ρ ⟨t, htN⟩ ∉ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range := by
    rintro ⟨x, hx⟩
    apply hσ1
    rw [← hΦs σ, ← hρt, ← hx, hΦInn]
  have htZ : t ∉ centralizer (G₀ : Set G) := by
    intro htZ
    apply hout
    refine ⟨1, ?_⟩
    rw [map_one]
    refine MulEquiv.ext fun x => ?_
    apply ψ.symm.injective
    apply Subtype.ext
    rw [F4Pilot.coe_symm_normalizerMulAut_apply, MulAut.one_apply]
    have hc := mem_centralizer_iff.1 htZ ((ψ.symm x : G₀) : G) (ψ.symm x).2
    change ((ψ.symm x : G₀) : G) = t * ((ψ.symm x : G₀) : G) * t⁻¹
    rw [← hc, mul_inv_cancel_right]
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLG ht htN htZ
  have hker : Odd (Nat.card ρ.ker) := by
    rw [hρ, EPilot.card_ker_normalizerMulAut]
    exact hZ
  have htG : t ∉ G₀ := EPilot.not_mem_of_normalizerMulAut_not_mem_range ψ htN hout
  apply CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_odd_centralizer hZ ht htG)
  refine exists_normal_index_two_of_graphField ρ hker (EPilot.exists_normalizerMulAut_eq_conj ψ)
    Φ hΦInn (fieldAutHom F n) hΦs γ hγ2 hΦγ hγs (fun α => ?_) htN ht ⟨σ, hρt.symm⟩
    (by rw [hρt, hΦs]; exact hσ1) huniq
  obtain ⟨x, τ, h⟩ := hform α
  exact ⟨x, τ, h⟩

end Endgame

end CFSG.SeitzReduction.OmegaPilot
