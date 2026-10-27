module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHabel
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Row

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_omegaRowAt_pairTorus_four (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃ r : OmegaRow,
      OmegaRowAt t (modelToG e (pairTorus (K := K) k)) (modelToG e (pairPerp (K := K) k)) r := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, htX, -⟩ := neighbour_data_pairTorus_four hKc hq k e htC rfl rfl
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting_four hset hKc hq k e htC ht rfl htX rfl
  have ht' : orderOf (⟨t, htX⟩ : centralizer ((((pairTorus (K := K) k).map
      e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ht
  have hs2 := orderOf_mk_oddCore ht'
  have hs2' : (QuotientGroup.mk' (oddCore (centralizer ((((pairTorus (K := K) k).map
      e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (QuotientGroup.mk' (oddCore (centralizer ((((pairTorus (K := K)
      k).map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))) ⟨t, htX⟩)
    rwa [hs2] at h
  have hDs := hcomp.1
  have hDc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  obtain ⟨-, Kc, hKc', -, hDKK, -⟩ := CFSG.SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hs2' hDs hDc
  by_cases hKt : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
      ((((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
        Set G))) ⟨t, htX⟩)).toMonoidHom = Kc
  · exact ⟨.field, htX, Kc, hKc', hDKK, iff_of_true rfl hKt⟩
  · exact ⟨.swap, htX, Kc, hKc', hDKK, iff_of_false (by decide) hKt⟩

end Row

@[expose] def OmegaPlusFourResidualInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      Even f → ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) (t : G),
      orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) ∧
        ∃ y ∈ (S : Subgroup G), ∃ w ∈ (S : Subgroup G), y * w * y⁻¹ * w⁻¹ ∉ L) →
      ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
        (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
        (∃ hz : z ∈ CFSG.conjugate L x,
          IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
        ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹

@[expose] def OmegaPlusFourCoverInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K)) (t : G),
      orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      ∀ k : Fin (3 + 1),
      ¬ (((modelToG e (pairPerp (K := K) k)).subgroupOf
          (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
            Set G))))).Normal →
      OmegaRowAt t (modelToG e (pairTorus (K := K) k)) (modelToG e (pairPerp (K := K) k))
          .field →
        ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
          orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
          Nonempty (PlusFieldCover e ι k)

@[expose] def OmegaPlusFourUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K)) (t : G),
      orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
        ∀ G₀ : Subgroup G, G₀ = ⨆ j, plusNode e j →
          Nonempty (G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F)) →
          ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)

@[expose] def OmegaPlusFourEndInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ t : G, orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ G₀ : Subgroup G, L ≤ G₀ → ∀ htN : t ∈ normalizer (G₀ : Set G),
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F), orderOf σ = 2 →
    ∀ ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F),
      MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
          fieldAutT (coordinateQuadPlus 4 F) σ (E7Pilot.coordinateQuadPlus_fieldMap 4 σ) →
      (∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) → False

@[expose] def OmegaPlusFourSwapInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K)) (t : G),
      orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
        (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
        (∃ hz : z ∈ CFSG.conjugate L x,
          IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
        ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹) →
      (∀ k : Fin (3 + 1),
        ¬ (((modelToG e (pairPerp (K := K) k)).subgroupOf
            (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
              Set G))))).Normal) →
      (∀ k : Fin (3 + 1), OmegaRowAt t (modelToG e (pairTorus (K := K) k))
        (modelToG e (pairPerp (K := K) k)) .swap) → False

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_pairTorus_four_of_inputs (hlevi : PlusFourLeviInput)
    (hF6 : PlusFourRefinedF6Input) (hres : OmegaPlusFourResidualInput) (hset : SeitzSetting G L)
    {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (k : Fin 4) :
    ¬ (((modelToG e (pairPerp (K := K) k)).subgroupOf
        (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
          Set G))))).Normal := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  by_cases habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L
  · exact not_normal_neighbour_pairTorus_of_habel_four hlevi hF6 hset hKc hq e htC ht habel k rfl
      rfl
  · rcases Nat.even_or_odd f with hfe | hfo
    · push Not at habel
      obtain ⟨S, hS, y, hy, w, hw, hyw⟩ := habel
      exact not_normal_neighbour_pairTorus_of_twoSided_four hlevi hF6 hset hKc hq e htC ht
        (hres G L hset f K hKc hf hfe e t ht hKt ⟨S, hS, y, hy, w, hw, hyw⟩) k rfl rfl
    · exact absurd (habel_plus_of_odd_four hset hfo hKc e ht hKt) habel

theorem exists_conj_eq_mul_longRoot_twoSided_four_of_inputs (hres : OmegaPlusFourResidualInput)
    (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  by_cases habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L
  · exact exists_conj_eq_mul_longRoot_twoSided_plus_of_habel_four hset hKc hq e ht hKt habel
  · rcases Nat.even_or_odd f with hfe | hfo
    · push Not at habel
      obtain ⟨S, hS, y, hy, w, hw, hyw⟩ := habel
      exact hres G L hset f K hKc hf hfe e t ht hKt ⟨S, hS, y, hy, w, hw, hyw⟩
    · exact absurd (habel_plus_of_odd_four hset hfo hKc e ht hKt) habel

end Main

end CFSG.SeitzReduction.OmegaPilot
