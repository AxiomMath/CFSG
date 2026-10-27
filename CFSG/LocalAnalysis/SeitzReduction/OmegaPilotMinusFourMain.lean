module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Main
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEight
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open scoped MatrixGroups

section Row

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_omegaRowAt_minusPairTorus_four (hset : SeitzSetting G L) {f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (4 - 1)) :
    ∃ r : OmegaRow, OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
      (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) r := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, htX, -⟩ := neighbour_data_minusPairTorus_of_four_le hKc hq le_rfl hirr k e htC rfl rfl
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le hset hKc hq
    le_rfl hirr k e htC ht rfl htX rfl
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hs2 : (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e (minusPairTorus (K := K) (by norm_num) b c k) : Set G))) ⟨t, htX⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have h1 : (⟨t, htX⟩ : centralizer
        (modelToG e (minusPairTorus (K := K) (by norm_num) b c k) : Set G)) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact ht2)
    rw [h1, map_one]
  have hDs := hcomp.1
  have hDc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  obtain ⟨-, Kc, hKc', -, hDKK, -⟩ :=
    CFSG.SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer
      (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hs2 hDs hDc
  by_cases hKt : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e (minusPairTorus (K := K) (by norm_num) b c k) : Set G))) ⟨t, htX⟩)).toMonoidHom =
      Kc
  · exact ⟨.field, htX, Kc, hKc', hDKK, iff_of_true rfl hKt⟩
  · exact ⟨.swap, htX, Kc, hKc', hDKK, iff_of_false (by decide) hKt⟩

end Row

@[expose] def OmegaMinusFourSwapRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .swap) → False

@[expose] def OmegaMinusFourCoverInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .field) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
        Nonempty (MinusFieldCover (r := 2) e ι 0)

@[expose] def OmegaMinusFourRootParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .field) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
        Nonempty (MinusRootFieldParam (n := 2 + 2) le_rfl hirr e t ι σ ⟨0, by omega⟩
          ⟨1, by omega⟩)

@[expose] def OmegaMinusFourForkSwapInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .field) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
      ∀ C₀ : MinusFieldCover (r := 2) e ι 0,
        (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom = minusNode C₀ 3

@[expose] def OmegaMinusFourEdgeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .field) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
      ∀ C₀ : MinusFieldCover (r := 2) e ι 0,
        ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = minusNode C₀ 0 ∧
          (B23 F).map θ = minusNode C₀ 1

@[expose] def OmegaMinusFourUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → ∀ (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι),
      ∀ (C₀ : MinusFieldCover (r := 2) e ι 0) (G₀ : Subgroup G), G₀ = ⨆ j, minusNode C₀ j →
        L ≤ G₀ → center G₀ = ⊥ → LieModel G₀ .POmegaPlus 4 2 (2 * f) →
      ∀ (htN : t ∈ normalizer (G₀ : Set G))
        (ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus 4 F (by norm_num) (ι b) (ι c))),
        MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
          fieldAutT (coordinateQuadMinus 4 F (by norm_num) (ι b) (ι c)) σ
            (coordinateQuadMinus_fieldMap_of_fixed (by norm_num) ((hfix _).2 ⟨b, rfl⟩)
              ((hfix _).2 ⟨c, rfl⟩)) →
        ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)

@[expose] def OmegaMinusFourEndInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (t : G), orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (G₀ : Subgroup G), L ≤ G₀ → ∀ htN : t ∈ normalizer (G₀ : Set G),
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F), orderOf σ = 2 →
    ∀ (β γ : F) (hβ : σ β = β) (hγ : σ γ = γ), (∀ s : F, σ s = s → s ^ 2 + β * s + γ ≠ 0) →
    ∀ ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus 4 F (by norm_num) β γ),
      MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
        fieldAutT (coordinateQuadMinus 4 F (by norm_num) β γ) σ
          (coordinateQuadMinus_fieldMap_of_fixed (by norm_num) hβ hγ) →
      (∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) → False

@[expose] def OmegaMinusFourSignInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (β γ : F) (σ : F ≃+* F),
    orderOf σ = 2 → ∀ (hβ : σ β = β) (hγ : σ γ = γ), (∀ s : F, σ s = s → s ^ 2 + β * s + γ ≠ 0) →
    ∃ E : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadMinus 4 F (by norm_num) β γ))),
      E.index = 2 ∧ (∀ x, MulAut.conj x ∈ E) ∧
      fieldAutT (coordinateQuadMinus 4 F (by norm_num) β γ) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by norm_num) hβ hγ) ∉ E

theorem omegaMinusFourEndInput_of_sign (hχ : OmegaMinusFourSignInput) :
    OmegaMinusFourEndInput := by
  intro G _ _ L hset t ht hKt G₀ hLG htN F _ _ _ σ hσ β γ hβ hγ hirr ψ hψ huniq
  have : IsSimpleGroup G := hset.1
  obtain ⟨E, hE2, hEInn, hEσ⟩ := hχ F β γ σ hσ hβ hγ hirr
  have : E.Normal := Subgroup.normal_of_index_eq_two hE2
  have : E.FiniteIndex := ⟨by rw [hE2]; norm_num⟩
  have hρt : F4Pilot.normalizerMulAut ψ ⟨t, htN⟩ =
      fieldAutT (coordinateQuadMinus 4 F (by norm_num) β γ) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by norm_num) hβ hγ) := hψ
  have hQ : ¬ 4 ∣ Nat.card (MulAut (matrixProjectiveDerived
      (coordinateQuadMinus 4 F _ β γ)) ⧸ E) := by
    change ¬ 4 ∣ E.index
    rw [hE2]
    decide
  refine EPilot.false_of_simple_of_mulAut_hom ψ htN ht huniq (QuotientGroup.mk' E) hQ
    (fun x => (QuotientGroup.eq_one_iff _).2 (hEInn x)) ?_
  rw [hρt]
  exact fun h => hEσ ((QuotientGroup.eq_one_iff _).1 h)

section Main


theorem omegaMinusFourInput_of_inputs (hswap : OmegaMinusFourSwapRowInput)
    (hcov : OmegaMinusFourCoverInput)
    (hparam : OmegaMinusFourRootParamInput) (hfork : OmegaMinusFourForkSwapInput)
    (hedge : OmegaMinusFourEdgeInput) (huniq : OmegaMinusFourUniqueInput)
    (hend : OmegaMinusFourEndInput) : OmegaMinusFourInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf2
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨r, hr⟩ := exists_omegaRowAt_minusPairTorus_four hset hKc hq hirr e htC ht 0
  have hall : ∀ k : Fin (4 - 1), OmegaRowAt t
      (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
      (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) r := fun k =>
    (omegaRowAt_minusPairTorus_iff le_rfl hirr e htC 0 k r).1 hr
  cases r with
  | swap =>
    exact hswap G L hset f K b c hirr hKc hf2 e t ht hKt hall
  | field =>
    obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
    have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
    have hF : Nat.card F = 2 ^ (2 * f) :=
      SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
    have hF4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hσ
      omega
    have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    obtain ⟨C₀⟩ := hcov G L hset f K b c hirr hKc hf2 e t ht hKt hall F ι σ hσ hfix
    obtain ⟨P⟩ := hparam G L hset f K b c hirr hKc hf2 e t ht hKt hall F ι σ hσ hfix
    have htU := hfork G L hset f K b c hirr hKc hf2 e t ht hKt hall F ι σ hσ hfix C₀
    have h01 := hedge G L hset f K b c hirr hKc hf2 e t ht hKt hall F ι σ hσ hfix C₀
    have hcomm := minusNode_le_centralizer_four_field_of_swap hset hKc hq hirr e ht hKt hσ1 hσσ
      hfix P C₀ htU
    obtain ⟨-, hG₀q, hZ, hG₀L, -, htN⟩ := exists_weakCT_minus_four hKc hq hF C₀ rfl hcomm h01 htC
    have hLG := le_iSup_minusNode_four hirr C₀ hq hF4
    obtain ⟨-, -, ψ, hψ⟩ := minusFieldRow_class_four hset hKc hirr e htC ht ι hσ hfix hG₀q hZ
      hG₀L hLG htN
    have hu := huniq G L hset f K b c hirr hKc hf2 e t ht hKt F ι σ hσ hfix C₀ _ rfl hLG hZ hG₀L
      htN ψ hψ
    have hirr' : ∀ s : F, σ s = s → s ^ 2 + ι b * s + ι c ≠ 0 := by
      intro s hs h0
      obtain ⟨s', rfl⟩ := (hfix s).1 hs
      apply hirr s'
      apply ι.injective
      rw [map_zero, ← h0, map_add, map_add, map_mul, map_pow]
    exact hend G L hset t ht hKt _ hLG htN F σ hσ (ι b) (ι c) ((hfix _).2 ⟨b, rfl⟩)
      ((hfix _).2 ⟨c, rfl⟩) hirr' ψ hψ hu

end Main

end CFSG.SeitzReduction.OmegaPilot
