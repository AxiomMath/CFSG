module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWCat
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2FiveSixKinds
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWOne

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

noncomputable abbrev seitzLeviHat {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) (W : Subgroup G) : Subgroup (seitzHat W) :=
  ((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n)))).subgroupOf
    (normalizer (W : Set G))).map (seitzHatMap W)

@[expose] def LinearTwoSwapKindAt {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type}
    [Field K] (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (a b : Fin n)
    (X₀ : Subgroup (LinearFlag.projectiveSL n K))
    (htX : t ∈ centralizer (modelToG e X₀ : Set G)) : Prop :=
  ∃ Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G))),
    IsComponent Kc ∧
    ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
    Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
    ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
    center Kc = ⊥ ∧
    Nonempty (Kc ≃* ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))))

@[expose] def LSixNOneStandardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 6 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
    ∀ (c : Fin 6) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 10 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) →
      CFSG.Open.IsComponentOf (seitzLeviHat e c W₁)
          (centralizer ({seitzHatMap W₁ ⟨t, htN⟩} : Set (seitzHat W₁))) ∧
        (∀ U : Subgroup (seitzHat W₁), IsPGroup 2 U →
          U ≤ centralizer (seitzLeviHat e c W₁ : Set (seitzHat W₁)) → Nat.card U ≤ 2) ∧
        CFSG.Open.standardComponentIsStandard (seitzLeviHat e c W₁) ∧
        ¬ (seitzLeviHat e c W₁).Normal

@[expose] def LSixFieldNOneExclusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 6 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 6) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 10 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsComponent Kc → seitzLeviHat e c W₁ < Kc →
      Kc.map (MulAut.conj (seitzHatMap W₁ ⟨t, htN⟩)).toMonoidHom = Kc →
      seitzHatMap W₁ ⟨t, htN⟩ ∉ Kc → center Kc = ⊥ → LieModel Kc .PSL 5 2 2 →
    ∀ (a b : Fin 6), a ≠ b → c ≠ a → c ≠ b → ∀ X₀ : Subgroup (LinearFlag.projectiveSL 6 K),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
    ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), ¬ LinearTwoSwapKindAt e t a b X₀ htX

@[expose] def LinearTwoSwapTypeAtNOne {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type}
    [Field K] (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (c : Fin n) (W₁ : Subgroup G)
    (htN : t ∈ normalizer (W₁ : Set G)) : Prop :=
  ∃ Kc : Subgroup (seitzHat W₁), IsComponent Kc ∧
    seitzLeviHat e c W₁ ≤ Kc ⊔ Kc.map (MulAut.conj (seitzHatMap W₁ ⟨t, htN⟩)).toMonoidHom ∧
    Kc.map (MulAut.conj (seitzHatMap W₁ ⟨t, htN⟩)).toMonoidHom ≠ Kc ∧
    ⁅Kc, Kc.map (MulAut.conj (seitzHatMap W₁ ⟨t, htN⟩)).toMonoidHom⁆ = ⊥ ∧
    center Kc = ⊥ ∧ Nonempty (Kc ≃* seitzLeviHat e c W₁)

@[expose] def LSixSwapNOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → ∀ (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ e' : L ≃* LinearFlag.projectiveSL 6 K,
        (∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
          X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
          ∀ htX : t ∈ centralizer (modelToG e' X₀ : Set G), LinearTwoSwapKindAt e' t a b X₀ htX) →
        ∀ c : Fin 6, ∃ W₁ : Subgroup G, Nat.card W₁ = 2 ^ 10 ∧ (∀ w ∈ W₁, w * w = 1) ∧
          W₁ ⊓ centralizer ({t} : Set G) = modelToG e' (pointRadical c) ∧
          ∃ htN : t ∈ normalizer (W₁ : Set G),
            modelToG e' (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) ∧
            LinearTwoSwapTypeAtNOne e' t c W₁ htN) →
      ∀ e : L ≃* LinearFlag.projectiveSL 6 K,
        (∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
          X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
          ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
        False

section Assembly

theorem exists_ne_ne_of_fin_six (c : Fin 6) : ∃ a b : Fin 6, a ≠ b ∧ c ≠ a ∧ c ≠ b := by
  revert c
  decide

variable {G : Type} [Group G] {L : Subgroup G}

theorem isQuasisimple_and_lieModel_levi_six {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL 6 K) (c : Fin 6) :
    CFSG.IsQuasisimple (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6)))) ∧
      LieModel (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ⧸
        center (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))))) .PSL 5 2 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hcard : (({c}ᶜ : Finset (Fin 6))).card = 5 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  refine ⟨isQuasisimple_map_blockSL e (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
    (Or.inl (by rw [hcard]; norm_num)), ?_⟩
  have φ : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≃*
      Matrix.SpecialLinearGroup (Fin 5) K :=
    (linearModelToGEquiv e _).symm.trans
      (blockSLEquivOfEquiv (K := K) (by rw [hcard]; norm_num) (Finset.equivFinOfCardEq hcard)).symm
  exact lieModel_quotient_center_of_mulEquiv_specialLinear (by rw [hK, pow_one]) (by norm_num) φ

variable [Finite G]

theorem orderOf_seitzHatMap_eq_two {W : Subgroup G} {t : G} (htN : t ∈ normalizer (W : Set G))
    (ht : orderOf t = 2) (htW : t ∉ W) : orderOf (seitzHatMap W ⟨t, htN⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htN⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : (⟨t, htN⟩ : normalizer (W : Set G)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [this, map_one]
    · intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact htW h1
  exact orderOf_mk_oddCore h2

theorem linearTwoSwapRowAtInput_six_of (hW : LinearTwoWOneAtInput 6)
    (hcat : SLmCatalogueClausesAt 5) (hdet : SLmEvenTypeDetAt 5) (hstd : LSixNOneStandardInput)
    (hKM : LSixFieldNOneExclusionInput) (hswap : LSixSwapNOneInput) :
    LinearTwoSwapRowAtInput 6 := by
  intro G _ _ L hset n K _ _ hK hn e t ht hKt hall
  subst hn
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  refine hswap G L hset K hK t ht hKt (fun e' hall' c => ?_) e hall
  obtain ⟨W₁, hW₁c, hW₁2, hW₁t, htN, hLN⟩ := hW G L hset K hK e' t ht hKt c
  refine ⟨W₁, hW₁c, hW₁2, hW₁t, htN, hLN, ?_⟩
  have htW : t ∉ W₁ := fun h => by
    have h' : t ∈ W₁ ⊓ centralizer ({t} : Set G) :=
      Subgroup.mem_inf.2 ⟨h, mem_centralizer_singleton_iff.2 rfl⟩
    rw [hW₁t] at h'
    exact not_mem_of_mem_centralizer hset.center_eq_bot htC ht1 (modelToG_le e' _ h')
  have hW₁ne : W₁ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hW₁c
    norm_num at hW₁c
  have hWc : ∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₁2 hv hw
  obtain ⟨hcomp, hsyl, hstd', hnn⟩ :=
    hstd G L hset K hK e' t ht hKt hall' c W₁ hW₁c hW₁2 hW₁t htN hLN
  obtain ⟨hLq, hLm⟩ := isQuasisimple_and_lieModel_levi_six hK e' c
  obtain ⟨⟨Kc, hKc, hLKK, hfield | hsw⟩, -⟩ := neighbourOvergroupSLmField_five_seitzHat hcat hdet
    hset.standardSetting.simple hset.standardSetting.nonab hset.standardSetting.kProper hW₁ne hWc
    htN (orderOf_seitzHatMap_eq_two htN ht htW) hLN hLq hLm hcomp hsyl hstd' hnn
  ·
    exfalso
    obtain ⟨hKt', hLK, htK, -, -, hZ, hmodel, -⟩ := hfield
    obtain ⟨a, b, hab, hca, hcb⟩ := exists_ne_ne_of_fin_six c
    obtain ⟨X₀, hX₀, -, hX₀c⟩ := exists_torusQ1 (K := K) (n := 6) hab
    have htX : t ∈ centralizer (modelToG e' X₀ : Set G) := centralizer_le (modelToG_le e' X₀) htC
    exact hKM G L hset K hK e' t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc hLK hKt' htK hZ hmodel
      a b hab hca hcb X₀ hX₀ hX₀c htX (hall' a b hab X₀ hX₀ hX₀c htX)
  · obtain ⟨hKt', hcomm, hZ, hφ⟩ := hsw
    exact ⟨Kc, hKc, hLKK, hKt', hcomm, hZ, hφ⟩

end Assembly

end CFSG.SeitzReduction.LinearPilot
