module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSOne
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveHCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

@[expose] def SOneSwapData {G : Type*} [Group G] (W C S₀ F W₀ A X : Subgroup G) (t : G)
    (k : ℕ) : Prop :=
  IsPGroup 2 C ∧ C ≤ normalizer (W : Set G) ∧ C ≤ centralizer ({t} : Set G) ∧
  C ⊓ centralizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ ∧
  W ≤ S₀ ∧ S₀ ≤ W ⊔ C ∧ S₀ ≤ centralizer (W₀ : Set G) ∧ C ≤ S₀ ⊔ F ∧
  2 * Nat.card W * Nat.card C ≤ k * Nat.card S₀ ∧
  A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥ ∧
  (∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a) ∧
  t ∈ normalizer (W₀ : Set G) ∧ W₀ ⊓ A ≠ ⊥ ∧
  F ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom ∧ F ≤ normalizer (W₀ : Set G) ∧
  IsPGroup 2 X ∧ X ≤ A ∧ X ≤ normalizer (W₀ : Set G) ∧
  X ⊓ centralizer ((W₀ ⊓ A : Subgroup G) : Set G) = ⊥ ∧ k < 2 * Nat.card X ^ 2 ∧
  ∀ c ∈ C, c * c = 1 → Nat.card (W ⊓ centralizer ({c * t} : Set G) : Subgroup G) ≤
    Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G)

theorem exists_isPGroup_lt_card_of_sOneSwapData {G : Type*} [Group G] [Finite G]
    {W C S₀ F W₀ A X : Subgroup G} {t : G} {k : ℕ} (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) (htW' : t ∉ W)
    (hWV : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hV2 : 2 < Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G))
    (hD : SOneSwapData W C S₀ F W₀ A X t k) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ normalizer (W : Set G) ∧
      2 * Nat.card W * Nat.card C < Nat.card P := by
  obtain ⟨hC2, hCW, hCt, hCV, hWS₀, hS₀, hS₀C, hCgen, hScard, hinf, hc, htW₀, hE1, hFA, hFW₀,
    hX2, hXA, hXW₀, hXE, hk, hkey⟩ := hD
  exact exists_isPGroup_lt_card_of_swap hW ht htW htW' hWV hV2 hC2 hCW hCt hCV hWS₀ hS₀ hS₀C
    hCgen hScard hinf hc htW₀ hE1 hFA hFW₀ hX2 hXA hXW₀ hXE hk hkey

section Seitz

@[expose] def LFiveSOneSwapDataInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
      (∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        modelToG e (rootSL2 (K := K) a b) ≤
          centralizer (centralizerPerfectCore (modelToG e X₀) : Set G)) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ∃ (C S₀ F W₀ A X : Subgroup G) (k : ℕ), Nat.card C = 2 ^ 6 ∧
        SOneSwapData W₁ C S₀ F W₀ A X t k

@[expose] def LSixSOneSwapDataInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 6 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
    ∀ (c : Fin 6) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 10 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) →
      ∃ (C S₀ F W₀ A X : Subgroup G) (k : ℕ), Nat.card C = 2 ^ 10 ∧
        SOneSwapData W₁ C S₀ F W₀ A X t k

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_mem_and_card_of_wOne (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (c : Fin n)
    {W₁ : Subgroup G} (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c)) :
    t ∉ W₁ ∧ Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ (n - 1) := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  refine ⟨fun h => ?_, ?_⟩
  · have h' : t ∈ W₁ ⊓ centralizer ({t} : Set G) :=
      Subgroup.mem_inf.2 ⟨h, mem_centralizer_singleton_iff.2 rfl⟩
    rw [hW₁t] at h'
    exact not_mem_of_mem_centralizer hset.center_eq_bot htC ht1 (modelToG_le e _ h')
  · have hcc : c ∉ ({c}ᶜ : Finset (Fin n)) := by simp
    rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]

theorem lFiveSOneNotSylowCoreInput_of_swapData (h : LFiveSOneSwapDataInput) :
    LFiveSOneNotSylowCoreInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hall hcore c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  obtain ⟨C, S₀, F, W₀, A, X, k, hCc, hD⟩ :=
    h G L hset K hK e t ht hKt hall hcore c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨htW, hV₁⟩ := not_mem_and_card_of_wOne hset hK e ht hKt c hW₁t
  obtain ⟨P, hP, hPN, hPc⟩ := exists_isPGroup_lt_card_of_sOneSwapData hW₁2 ht2 htW₁ htW
    (by rw [hW₁c, hV₁]; norm_num) (by rw [hV₁]; norm_num) hD
  refine ⟨P, hP, hPN, ?_⟩
  rw [hW₁c, hCc] at hPc
  norm_num at hPc ⊢
  omega

theorem lSixSOneNotSylowInput_of_swapData (h : LSixSOneSwapDataInput) :
    LSixSOneNotSylowInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  obtain ⟨C, S₀, F, W₀, A, X, k, hCc, hD⟩ :=
    h G L hset K hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨htW, hV₁⟩ := not_mem_and_card_of_wOne hset hK e ht hKt c hW₁t
  obtain ⟨P, hP, hPN, hPc⟩ := exists_isPGroup_lt_card_of_sOneSwapData hW₁2 ht2 htW₁ htW
    (by rw [hW₁c, hV₁]; norm_num) (by rw [hV₁]; norm_num) hD
  refine ⟨P, hP, hPN, ?_⟩
  rw [hW₁c, hCc] at hPc
  norm_num at hPc ⊢
  omega

end Seitz

end CFSG.SeitzReduction.LinearPilot
