module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveD
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveESwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSyl

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

@[expose] def LinearTwoFieldKindAtRoot {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type}
    [Field K] (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (a b : Fin n)
    (X₀ : Subgroup (LinearFlag.projectiveSL n K))
    (htX : t ∈ centralizer (modelToG e X₀ : Set G)) : Prop :=
  center (((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
      (centralizer (modelToG e X₀ : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) = ⊥ ∧
    ∃ Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G))), IsComponent Kc ∧
      ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e X₀ : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ Kc ∧
      ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∈
          normalizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
            oddCore (centralizer (modelToG e X₀ : Set G)))),
        Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
        LieModel Kc .PSL (n - 2) 2 (2 * 1)

@[expose] def LFiveNotNormalFieldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoFieldKindAtRoot e t a b X₀ htX →
    ∀ (c : Fin 5), c ≠ a → c ≠ b →
    ∀ (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ¬ ((((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
            (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))).map
        (QuotientGroup.mk' (oddCore (normalizer (W₁ : Set G) ⧸
          W₁.subgroupOf (normalizer (W₁ : Set G)))))).Normal

@[expose] def LFiveSOneNotSylowFieldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoFieldKindAtRoot e t a b X₀ htX →
    ∀ (c : Fin 5), c ≠ a → c ≠ b →
    ∀ (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ normalizer (W₁ : Set G) ∧ 2 ^ 15 < Nat.card P

theorem lFiveNotNormalFieldInput_of_notSylowField (h : LFiveSOneNotSylowFieldInput) :
    LFiveNotNormalFieldInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt a b hab X₀ hX₀ hX₀c htX hfk c hca hcb W₁ hW₁c hW₁2 hW₁t
    htW₁ hLW
  obtain ⟨P, hP, hPN, hPc⟩ := h G L hset K hK e t ht hKt a b hab X₀ hX₀ hX₀c htX hfk c hca hcb W₁
    hW₁c hW₁2 hW₁t htW₁ hLW
  exact not_normal_leviHat_five_of_lt_card hset hK e ht hKt c hW₁c hW₁2 hW₁t htW₁ hLW hP hPN hPc

theorem exists_pair_ne_ne_of_fin_five {a b : Fin 5} (hab : a ≠ b) :
    ∃ c₀ c₁ : Fin 5, c₀ ≠ c₁ ∧ c₀ ≠ a ∧ c₀ ≠ b ∧ c₁ ≠ a ∧ c₁ ≠ b := by
  have h : ∀ a b : Fin 5, a ≠ b →
      ∃ c₀ c₁ : Fin 5, c₀ ≠ c₁ ∧ c₀ ≠ a ∧ c₀ ≠ b ∧ c₁ ≠ a ∧ c₁ ≠ b := by decide
  exact h a b hab

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem linearTwoSwapTypeAtNOne_of_fieldRoot (hcat : SLmCatalogueClausesAt 4)
    (hdet : SLmEvenTypeDetAt 4) (hspor : SporadicFixedLFourTwoInput)
    (hnnF : LFiveNotNormalFieldInput) (hD : LFiveFieldNOneInput) (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin 5} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hfk : LinearTwoFieldKindAtRoot e t a b X₀ htX) {c : Fin 5} (hca : c ≠ a) (hcb : c ≠ b)
    {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G)) :
    LinearTwoSwapTypeAtNOne e t c W₁ htN := by
  obtain ⟨⟨Kc, hKc, hDKK, hfield | hsw⟩, -⟩ := neighbourOvergroupSLmField_nOneBar hset hcat hdet
    hspor hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN
    (lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c)
    (hnnF G L hset K hK e t ht hKt a b hab X₀ hX₀ hX₀c htX hfk c hca hcb W₁ hW₁c hW₁2 hW₁t htN
      hLN)
  · exfalso
    obtain ⟨hKt', hDK, hsK, hsN, hout, hZ, hmodel, -⟩ := hfield
    refine hD G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN
      ⟨Kc, hKc, ?_, hKt', hsK, hZ, hmodel, hsN, hout⟩
    rw [seitzLeviHat_eq_map_map]
    exact hDK
  · obtain ⟨hKt', hcomm, hZ, hφ⟩ := hsw
    refine ⟨Kc, hKc, ?_, hKt', hcomm, hZ, ?_⟩
    · rw [seitzLeviHat_eq_map_map]
      exact hDKK
    · rw [seitzLeviHat_eq_map_map]
      exact hφ

end Assembly

end CFSG.SeitzReduction.LinearPilot
