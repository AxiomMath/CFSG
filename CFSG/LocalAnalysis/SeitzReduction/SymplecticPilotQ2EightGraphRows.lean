module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTQuotRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def SpTwoUnitaryCoverEightInput (κ : Sp2mKind) (ε : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k κ) → NsUnitaryCover e (2 * 4 + ε)

@[expose] def SpTwoUnitaryEvenSecondClassQuotEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k .unitaryEven) → NsRowGlobalQuot e t .unitaryEven →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
        ¬ IsCharacteristicP 2
          (fixedSubgroup (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩))

@[expose] def SpTwoOmegaKindEightInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k κ) → Sp2mKindType (nsGlobal e) 4 1 (q2GlobalKind κ)

@[expose] def SpTwoOmegaClassEightInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k κ) → NsRowGlobal e t (q2GlobalKind κ) →
      ∀ (htN : t ∈ normalizer (nsGlobal e : Set G)) (g : G)
        (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
        ∃ β : MulAut (nsGlobal e), β * (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
          (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β

section Rows


theorem spTwoRowEightInput_unitaryOdd_of_cover (hc : SpTwoUnitaryCoverEightInput .unitaryOdd 1) :
    SpTwoRowEightInput .unitaryOdd := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  subst hn
  exact false_of_nsCoverType_unitaryOdd hset hK le_rfl e ht hKt
    (nsCoverType_of_nsUnitaryCover (Or.inr ⟨rfl, rfl⟩) (by omega)
      (hc G L hset K hK e t ht hKt hroot))

theorem spTwoRowEightInput_unitaryEven_of_cover (hc : SpTwoUnitaryCoverEightInput .unitaryEven 0)
    (h2 : SpTwoUnitaryEvenSecondClassQuotEightInput) : SpTwoRowEightInput .unitaryEven := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  subst hn
  exact false_of_nsCoverType_unitaryEven hset hK le_rfl e ht hKt
    (nsCoverType_of_nsUnitaryCover (Or.inl ⟨rfl, rfl⟩) (by omega)
      (hc G L hset K hK e t ht hKt hroot))
    (fun hglob => h2 G L hset K hK e t ht hKt hroot hglob)

theorem spTwoRowEightInput_omegaPlus_of_inputs (hkind : SpTwoOmegaKindEightInput .omegaPlus)
    (hcls : SpTwoOmegaClassEightInput .omegaPlus) : SpTwoRowEightInput .omegaPlus := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  subst hn
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hty : Sp2mKindType (nsGlobal e) 4 1 .omegaMinus := hkind G L hset K hK e t ht hKt hroot
  have hglob := nsRowGlobal_of_sp2mKindType_omega hset hK le_rfl e ht hKt (Or.inr rfl) hty
  obtain ⟨hout, hfix⟩ := hglob.2 htN
  exact false_of_omegaMinusRow_of_subgroup hset (le_nsGlobal hK le_rfl e) ht hKt htN hty
    hout hfix fun g hg => by
      obtain ⟨β, hβ⟩ := hcls G L hset K hK e t ht hKt hroot hglob htN g hg
      exact mem_normalizer_nsGlobal_of_conj_mulAut hset hK le_rfl e ht hKt htN hg β hβ

theorem spTwoRowEightInput_omegaMinus_of_inputs (hkind : SpTwoOmegaKindEightInput .omegaMinus)
    (hcls : SpTwoOmegaClassEightInput .omegaMinus) : SpTwoRowEightInput .omegaMinus := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  subst hn
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hty : Sp2mKindType (nsGlobal e) 4 1 .omegaPlus := hkind G L hset K hK e t ht hKt hroot
  have hglob := nsRowGlobal_of_sp2mKindType_omega hset hK le_rfl e ht hKt (Or.inl rfl) hty
  obtain ⟨hout, hfix⟩ := hglob.2 htN
  exact false_of_omegaPlusRow_of_subgroup hset ht htN (by omega) hty hout hfix fun g hg => by
    obtain ⟨β, hβ⟩ := hcls G L hset K hK e t ht hKt hroot hglob htN g hg
    exact mem_normalizer_nsGlobal_of_conj_mulAut hset hK le_rfl e ht hKt htN hg β hβ

theorem spTwoRowInput_unitaryOdd_of_covers (h8 : SpTwoUnitaryCoverEightInput .unitaryOdd 1)
    (hc : SpTwoUnitaryCoverInput .unitaryOdd 1) : SpTwoRowInput .unitaryOdd :=
  spTwoRowInput_of_eight_of_four_le (spTwoRowEightInput_unitaryOdd_of_cover h8)
    (spTwoRowInput_unitaryOdd_of_coverInput hc)

theorem spTwoRowInput_unitaryEven_of_covers (h8 : SpTwoUnitaryCoverEightInput .unitaryEven 0)
    (h8' : SpTwoUnitaryEvenSecondClassQuotEightInput) (hc : SpTwoUnitaryCoverInput .unitaryEven 0)
    (h2 : SpTwoUnitaryEvenSecondClassQuotInput) : SpTwoRowInput .unitaryEven :=
  spTwoRowInput_of_eight_of_four_le (spTwoRowEightInput_unitaryEven_of_cover h8 h8')
    (spTwoRowInput_unitaryEven_of_coverInput hc h2)

theorem spTwoRowInput_omegaPlus_of_all (h8 : SpTwoOmegaKindEightInput .omegaPlus)
    (h8' : SpTwoOmegaClassEightInput .omegaPlus) (hk : SpTwoOmegaKindInput .omegaPlus)
    (hcls : SpTwoOmegaClassInput .omegaPlus) : SpTwoRowInput .omegaPlus :=
  spTwoRowInput_of_eight_of_four_le (spTwoRowEightInput_omegaPlus_of_inputs h8 h8')
    (spTwoRowInput_omegaPlus_of_four_le hk hcls)

theorem spTwoRowInput_omegaMinus_of_all (h8 : SpTwoOmegaKindEightInput .omegaMinus)
    (h8' : SpTwoOmegaClassEightInput .omegaMinus) (hk : SpTwoOmegaKindInput .omegaMinus)
    (hcls : SpTwoOmegaClassInput .omegaMinus) : SpTwoRowInput .omegaMinus :=
  spTwoRowInput_of_eight_of_four_le (spTwoRowEightInput_omegaMinus_of_inputs h8 h8')
    (spTwoRowInput_omegaMinus_of_four_le hk hcls)

end Rows

end CFSG.SeitzReduction.SymplecticPilot
