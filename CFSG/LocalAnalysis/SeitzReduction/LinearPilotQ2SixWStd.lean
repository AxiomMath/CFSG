module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWKM
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWMove
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCKind
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindLinearCentre

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem open_isQuasisimple_and_center_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X ∧ center X = ⊥ := by
  obtain ⟨a, b, hab⟩ := hX
  have hZ : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · exact absurd (mem_center_iff.mp (by rw [h]; exact mem_top b) a) hab
  refine ⟨⟨?_, ?_⟩, hZ⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      apply hab
      have h1 : a * b * a⁻¹ * b⁻¹ ∈ commutator X := by
        rw [_root_.commutator_def]
        have := commutator_mem_commutator (G := X) (mem_top a) (mem_top b)
        rwa [commutatorElement_def] at this
      rw [h, mem_bot] at h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

noncomputable abbrev seitzLeviBar {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type}
    [Field K] (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) (W : Subgroup G) :
    Subgroup (seitzBar W) :=
  ((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n)))).subgroupOf
    (normalizer (W : Set G))).map (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))

@[expose] def LSixNOneCentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 6 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 6) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 10 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) →
      centralizer ({QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩} :
          Set (seitzBar W₁)) ≤
        seitzLeviBar e c W₁ ⊔
          zpowers (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩)

@[expose] def LSixNOneNotNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 6 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
    ∀ (c : Fin 6) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 10 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ _htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) →
      ¬ (seitzLeviHat e c W₁).Normal

theorem isSimpleGroup_seitzLeviBar {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) (c : Fin 6)
    {W : Subgroup G} (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W : Set G)) :
    IsSimpleGroup (seitzLeviBar e c W) ∧ ∃ a b : seitzLeviBar e c W, a * b ≠ b * a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) with hL₁
  obtain ⟨hq, -⟩ := isQuasisimple_and_lieModel_levi_six hK e c
  have hcard : (({c}ᶜ : Finset (Fin 6))).card = 5 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have φ : L₁ ≃* Matrix.SpecialLinearGroup (Fin 5) K :=
    (linearModelToGEquiv e _).symm.trans
      (blockSLEquivOfEquiv (K := K) (by rw [hcard]; norm_num) (Finset.equivFinOfCardEq hcard)).symm
  have hZSL : center (Matrix.SpecialLinearGroup (Fin 5) K) = ⊥ :=
    SymplecticPilot.center_specialLinear_eq_bot_of_coprime (by rw [hK]; norm_num)
  have hZ : center L₁ = ⊥ := by
    have h := map_center_eq φ
    rw [hZSL] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (f := φ.toMonoidHom) φ.injective).1 h
  have hsL : IsSimpleGroup L₁ := by
    have : IsSimpleGroup (L₁ ⧸ center L₁) := hq.2.1
    exact (quotientCenterMulEquiv hZ).symm.isSimpleGroup
  have hnonab : ∃ a b : L₁, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center L₁) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center L₁) b
    exact ⟨a', b', fun h => hab (by rw [← map_mul, h, map_mul])⟩
  have e₁ : L₁.subgroupOf (normalizer (W : Set G)) ≃* L₁ := subgroupOfEquivOfLe hLN
  have hsL' : IsSimpleGroup (L₁.subgroupOf (normalizer (W : Set G))) := e₁.isSimpleGroup
  have hne : seitzLeviBar e c W ≠ ⊥ := by
    intro hbot
    obtain ⟨a, b, hab⟩ := hnonab
    have hmem : ∀ x : L₁, (x : G) ∈ W := fun x => by
      have hx : QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))
          ⟨(x : G), hLN x.2⟩ ∈ seitzLeviBar e c W :=
        ⟨⟨(x : G), hLN x.2⟩, mem_subgroupOf.2 x.2, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        mem_subgroupOf] at hx
      exact hx
    exact hab (Subtype.ext (hWc _ (hmem a) _ (hmem b)))
  obtain ⟨e₂⟩ := F4Pilot.nonempty_mulEquiv_map_of_isSimpleGroup
    (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))) hsL' hne
  have hs : IsSimpleGroup (seitzLeviBar e c W) := e₂.symm.isSimpleGroup
  refine ⟨hs, ?_⟩
  obtain ⟨a, b, hab⟩ := hnonab
  refine ⟨e₂ (e₁.symm a), e₂ (e₁.symm b), fun h => hab ?_⟩
  have h' := congrArg (fun x => e₁ (e₂.symm x)) h
  simpa only [map_mul, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] using h'

theorem lSixNOneStandardInput_of (hA8 : LSixNOneCentralizerInput)
    (hC1 : LSixNOneNotNormalInput) : LSixNOneStandardInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htN hLN
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have htW : t ∉ W₁ := fun h => by
    have h' : t ∈ W₁ ⊓ centralizer ({t} : Set G) :=
      Subgroup.mem_inf.2 ⟨h, mem_centralizer_singleton_iff.2 rfl⟩
    rw [hW₁t] at h'
    exact not_mem_of_mem_centralizer hset.center_eq_bot htC ht1 (modelToG_le e _ h')
  have hWc : ∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₁2 hv hw
  set s : seitzBar W₁ := QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩
    with hs_def
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : orderOf s = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hs_def, ← map_pow]
      have : (⟨t, htN⟩ : normalizer (W₁ : Set G)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [this, map_one]
    · intro h1
      rw [hs_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact htW h1
  have hLs : seitzLeviBar e c W₁ ≤ centralizer ({s} : Set (seitzBar W₁)) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_singleton_iff, hs_def, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 htC) _ (modelToG_le e _ (mem_subgroupOf.1 hl))
  obtain ⟨hsimp, hnonab⟩ := isSimpleGroup_seitzLeviBar hK e c hWc hLN
  obtain ⟨hLq, hLZ⟩ := open_isQuasisimple_and_center_of_isSimpleGroup
    (X := seitzLeviBar e c W₁) hnonab
  obtain ⟨hcomp, hsyl, hstd⟩ := inheritance_of_centralizer_le_sup hs hLs hLq hLZ
    (hA8 G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN)
  have hmap : (seitzLeviBar e c W₁).map (QuotientGroup.mk' (oddCore (seitzBar W₁))) =
      seitzLeviHat e c W₁ := by
    rw [seitzLeviBar, seitzLeviHat, Subgroup.map_map]
    rfl
  rw [hmap] at hcomp hsyl hstd
  exact ⟨hcomp, hsyl, hstd, hC1 G L hset K hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htN hLN⟩

theorem linearTwoSwapRowAtInput_six_of_std
    (hcat : SLmCatalogueClausesAt 5) (hdet : SLmEvenTypeDetAt 5)
    (hA8 : LSixNOneCentralizerInput) (hC1 : LSixNOneNotNormalInput)
    (hlift : LSixFieldNOneLiftInput) (hswap : LSixSwapNOneInput) : LinearTwoSwapRowAtInput 6 :=
  linearTwoSwapRowAtInput_six_of_lift linearTwoWOneAtInput_six hcat hdet
    (lSixNOneStandardInput_of hA8 hC1) hlift hswap

end CFSG.SeitzReduction.LinearPilot
