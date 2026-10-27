module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSyl
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCMatch
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveEEnd
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveESwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBFinal

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)

@[expose] def LFiveNotNormalSwapInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ¬ ((((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
            (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))).map
        (QuotientGroup.mk' (oddCore (normalizer (W₁ : Set G) ⧸
          W₁.subgroupOf (normalizer (W₁ : Set G)))))).Normal

@[expose] def LFiveSOneNotSylowSwapInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ normalizer (W₁ : Set G) ∧ 2 ^ 15 < Nat.card P

theorem lFiveNotNormalSwapInput_of_notSylow (h : LFiveSOneNotSylowSwapInput) :
    LFiveNotNormalSwapInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  obtain ⟨P, hP, hPN, hPc⟩ := h G L hset K hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  exact not_normal_leviHat_five_of_lt_card hset hK e ht hKt c hW₁c hW₁2 hW₁t htW₁ hLW hP hPN hPc

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem lFiveSwapNOneHyp_of_swap
    (hcat : SLmCatalogueClausesAt 4) (hdet : SLmEvenTypeDetAt 4)
    (hspor : SporadicFixedLFourTwoInput) (hNV : LFiveNormalizerPointRadicalInput)
    (hnn : LFiveNotNormalSwapInput)
    (hschurF : ∀ (X : Type) [Group X], LieModel X .PSL 4 2 2 → OddSchurTrivial X)
    (hKM : LFiveFieldNOneLiftInput) (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    LFiveSwapNOneHyp G L K t := by
  intro e' hall' c
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨W₁, hW₁c, hW₁2, hW₁t, htN, hLN⟩ := lFiveWOneInput G L hset K hK e' t ht hKt c
  refine ⟨W₁, hW₁c, hW₁2, hW₁t, htN, hLN, ?_⟩
  obtain ⟨⟨Kc, hKc, hDKK, hfield | hsw⟩, -⟩ := neighbourOvergroupSLmField_nOneBar hset hcat hdet
    hspor hK e' ht hKt c hW₁c hW₁2 hW₁t htN hLN (hNV G L hset K hK e' t ht hKt c)
    (hnn G L hset K hK e' t ht hKt hall' c W₁ hW₁c hW₁2 hW₁t htN hLN)
  ·
    exfalso
    obtain ⟨-, hDK, -, hsN, hout, -, hmodel, -⟩ := hfield
    obtain ⟨hLq, hLZ, -, -, hLs⟩ := leviBar_facts e' hK htC hW₁c hLN htN
    have hs := orderOf_mk_wOne_eq_two e' hK ht hW₁c hW₁2 hW₁t htN
    have hCs := centralizer_bar_le_sup e' hK ht hW₁c hW₁2 hW₁t htN hLN
      (hNV G L hset K hK e' t ht hKt c)
    have hsC : QuotientGroup.mk' (oddCore (seitzBar W₁))
        (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩) ∉
          centralizer (Kc : Set (seitzHat W₁)) := by
      intro hc'
      apply hout
      have h1 : (⟨_, hsN⟩ : normalizer (Kc : Set (seitzHat W₁))) ∈
          Kc.normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        exact hc'
      exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
    obtain ⟨hcomp, -, -, -, -, hLm⟩ :=
      exists_lift_field_of_le_sup hs hLs hLq hLZ hCs hschurF hKc hsN hsC hmodel
    have hLp := isPerfect_iff.mp ⟨hLq.1⟩
    have hLK := F4Pilot.le_oddCoreLift_of_perfect hLp hDK.le
    obtain ⟨a, b, hab, hca, hcb⟩ := exists_ne_ne_of_fin_five c
    obtain ⟨X₀, hX₀, -, hX₀c⟩ := exists_torusQ1 (K := K) (n := 5) hab
    have htX : t ∈ centralizer (modelToG e' X₀ : Set G) := centralizer_le (modelToG_le e' X₀) htC
    obtain ⟨P, hPX, hPperf, h5⟩ := hKM G L hset K hK e' t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN
      (oddCoreLift Kc) hcomp hLm hLK a b hab hca hcb X₀ hX₀ hX₀c
    obtain ⟨Kx, hKx, hDKKx, hne, hcommx, -, hiso⟩ := hall' a b hab X₀ hX₀ hX₀c htX
    exact not_five_dvd_card_of_perfect_of_swap hset hK e' htC ht hab hX₀ hX₀c rfl htX rfl hKx
      hDKKx hne hcommx hiso hPX hPperf h5
  · obtain ⟨hKt', hcomm, hZ, hφ⟩ := hsw
    refine ⟨Kc, hKc, ?_, hKt', hcomm, hZ, ?_⟩
    · rw [seitzLeviHat_eq_map_map]
      exact hDKK
    · rw [seitzLeviHat_eq_map_map]
      exact hφ

theorem linearTwoSwapRowAtInput_five_of_swap
    (hcat : SLmCatalogueClausesAt 4)
    (hdet : SLmEvenTypeDetAt 4) (hspor : SporadicFixedLFourTwoInput)
    (hNV : LFiveNormalizerPointRadicalInput) (hnn : LFiveNotNormalSwapInput)
    (hschurF : ∀ (X : Type) [Group X], LieModel X .PSL 4 2 2 → OddSchurTrivial X)
    (hKM : LFiveFieldNOneLiftInput) (hE : LFiveSwapGOneInput) : LinearTwoSwapRowAtInput 5 := by
  intro G _ _ L hset n K _ _ hK hn e t ht hKt hall
  subst hn
  obtain ⟨G₁, hperf, h₁₂, hδ, hsurj⟩ := hE G L hset K hK t ht hKt
    (lFiveSwapNOneHyp_of_swap hcat hdet hspor hNV hnn hschurF hKM hset hK ht hKt) e hall
  exact false_of_swapRow_of_gOne_linear_two hset (by norm_num) hK e ht hKt hall hperf h₁₂ hδ hsurj

end Assembly

end CFSG.SeitzReduction.LinearPilot
