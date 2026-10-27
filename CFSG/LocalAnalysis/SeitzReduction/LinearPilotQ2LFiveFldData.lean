module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFldInput
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFldAbs
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

@[expose] def LFiveSOneSylowPartAtInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (a b c d d' : Fin 5) (hab : a ≠ b) (hdd' : d ≠ d'), c ≠ a → c ≠ b →
      ({c}ᶜ : Finset (Fin 5)) \ {a, b} = {d, d'} →
    ∀ X₀ : Subgroup (LinearFlag.projectiveSL 5 K), X₀ ≤ rootSL2 a b →
      Nat.card X₀ = Nat.card K + 1 →
    ∀ (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ((e.symm (xab hab 1) : L) : G) ∈
        centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) →
      ∃ C S₀ : Subgroup G, Nat.card C = 2 ^ 6 ∧ IsPGroup 2 C ∧
        C ≤ normalizer (W₁ : Set G) ∧ C ≤ centralizer ({t} : Set G) ∧
        C ⊓ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ ∧
        W₁ ≤ S₀ ∧ S₀ ≤ W₁ ⊔ C ∧
        S₀ ≤ centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ∧
        C ≤ S₀ ⊔ zpowers ((e.symm (xab hdd' 1) : L) : G) ∧
        2 ^ 15 ≤ 4 * Nat.card S₀ ∧
        ∀ h ∈ C, h * h = 1 → Nat.card (W₁ ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
          Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G)

@[expose] def LFiveFieldRootStepInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (a b : Fin 5) (hab : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoFieldKindAtRoot e t a b X₀ htX →
    ∀ (c : Fin 5), c ≠ a → c ≠ b →
    ∀ (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ((e.symm (xab hab 1) : L) : G) ∈
        centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G)

@[expose] def LFiveFieldPartInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoFieldKindAtRoot e t a b X₀ htX →
    ∀ (c d d' : Fin 5) (hdd' : d ≠ d'), c ≠ a → c ≠ b →
      ({c}ᶜ : Finset (Fin 5)) \ {a, b} = {d, d'} →
    ∀ (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ∃ R₀ T₀ : Subgroup G,
        centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ≤ R₀ ∧
        ((e.symm (xab hdd' 1) : L) : G) ∈ R₀ ∧ t ∈ normalizer (R₀ : Set G) ∧ t ∉ R₀ ∧
        IsPGroup 2 T₀ ∧ T₀ ≤ R₀ ∧
        T₀ ≤ normalizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ∧
        t ∈ normalizer (T₀ : Set G) ∧
        4 * Nat.card (T₀ ⊓ centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) :
          Subgroup G) : Set G) : Subgroup G) ≤ Nat.card T₀

theorem exists_sdiff_eq_pair_of_fin_five {a b c : Fin 5} (hab : a ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) : ∃ d d' : Fin 5, d ≠ d' ∧ ({c}ᶜ : Finset (Fin 5)) \ {a, b} = {d, d'} := by
  have hcsub : ({a, b} : Finset (Fin 5)) ⊆ {c}ᶜ := by
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton]
    intro hjc
    rcases Finset.mem_insert.1 hj with h | h
    · exact hca (hjc ▸ h)
    · exact hcb (hjc ▸ Finset.mem_singleton.1 h)
  have hcard : (({c}ᶜ : Finset (Fin 5)) \ {a, b}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hcsub, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨d, d', hdd', h⟩ := Finset.card_eq_two.1 hcard
  exact ⟨d, d', hdd', h⟩

theorem lFiveSOneNotSylowFieldInput_of_parts (hsyl : LFiveSOneSylowPartAtInput)
    (hroot : LFiveFieldRootStepInput) (hfp : LFiveFieldPartInput) :
    LFiveSOneNotSylowFieldInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt a b hab X₀ hX₀ hX₀c htX hfk c hca hcb W₁ hW₁c hW₁2 hW₁t
    htW₁ hLW
  obtain ⟨d, d', hdd', hS⟩ := exists_sdiff_eq_pair_of_fin_five hab hca hcb
  have hj := hroot G L hset K hK e t ht hKt a b hab X₀ hX₀ hX₀c htX hfk c hca hcb W₁ hW₁c hW₁2
    hW₁t htW₁ hLW
  obtain ⟨C, S₀, hCc, hC2, hCW, hCt, hCV, hWS₀, hS₀, hS₀C, hCgen, hS₀c, hkey⟩ :=
    hsyl G L hset K hK e t ht hKt a b c d d' hab hdd' hca hcb hS X₀ hX₀ hX₀c W₁ hW₁c hW₁2 hW₁t
      htW₁ hLW hj
  obtain ⟨R₀, T₀, hCR₀, huR₀, htNR₀, htR₀, hT₀2, hT₀R₀, hT₀W₀, htT₀, hT₀m⟩ :=
    hfp G L hset K hK e t ht hKt a b hab X₀ hX₀ hX₀c htX hfk c d d' hdd' hca hcb hS W₁ hW₁c
      hW₁2 hW₁t htW₁ hLW
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨htW, hV₁⟩ := not_mem_and_card_of_wOne hset hK e ht hKt c hW₁t
  have htW₀ : t ∈ normalizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) :
      Set G) :=
    mem_normalizer_inf_of_mem htW₁ (le_normalizer htX)
  obtain ⟨P, hP, hPN, hPc⟩ := exists_isPGroup_lt_card_of_field (k := 4) (m := 4) hW₁2 ht2 htW₁
    htW (by rw [hW₁c, hV₁]; norm_num) (by rw [hV₁]; norm_num) hC2 hCW hCt hCV hWS₀ hS₀ hS₀C
    hCgen (by rw [hW₁c, hCc]; norm_num; omega) hCR₀ ((zpowers_le).2 huR₀) htNR₀ htR₀ hT₀2
    hT₀R₀ hT₀W₀ htW₀ htT₀ hT₀m (by norm_num) hkey
  refine ⟨P, hP, hPN, ?_⟩
  rw [hW₁c, hCc] at hPc
  norm_num at hPc ⊢
  omega

theorem lFiveNotNormalFieldInput_of_parts (hsyl : LFiveSOneSylowPartAtInput)
    (hroot : LFiveFieldRootStepInput) (hfp : LFiveFieldPartInput) :
    LFiveNotNormalFieldInput :=
  lFiveNotNormalFieldInput_of_notSylowField (lFiveSOneNotSylowFieldInput_of_parts hsyl hroot hfp)

end CFSG.SeitzReduction.LinearPilot
