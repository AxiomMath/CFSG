module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFldInput
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBFinal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMDual

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section FieldKind

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

@[expose] def FieldKindOver (H D : Subgroup G) (t : G) (htX : t ∈ centralizer (H : Set G))
    (m : ℕ) : Prop :=
  center ((D.subgroupOf (centralizer (H : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (H : Set G))))) = ⊥ ∧
    ∃ Kc : Subgroup (centralizer (H : Set G) ⧸ oddCore (centralizer (H : Set G))),
      IsComponent Kc ∧
      (D.subgroupOf (centralizer (H : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (H : Set G)))) ≤ Kc ∧
      ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (H : Set G))) ⟨t, htX⟩ ∈
          normalizer (Kc : Set (centralizer (H : Set G) ⧸ oddCore (centralizer (H : Set G)))),
        Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
        LieModel Kc .PSL m 2 (2 * 1)

theorem linearTwoFieldKindAtRoot_iff_fieldKindOver (e : L ≃* LinearFlag.projectiveSL n K) (t : G)
    (a b : Fin n) (X₀ : Subgroup (LinearFlag.projectiveSL n K))
    (htX : t ∈ centralizer (modelToG e X₀ : Set G)) :
    LinearTwoFieldKindAtRoot e t a b X₀ htX ↔
      FieldKindOver (modelToG e X₀) (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))) t
        htX (n - 2) :=
  Iff.rfl

theorem fieldKindOver_congr {H H' D D' : Subgroup G} {t : G} {m : ℕ} (hH : H = H') (hD : D = D')
    (htX : t ∈ centralizer (H : Set G)) (htX' : t ∈ centralizer (H' : Set G))
    (h : FieldKindOver H D t htX m) : FieldKindOver H' D' t htX' m := by
  subst hH
  subst hD
  exact h

theorem linearTwoFieldKindAtRoot_congr {e e' : L ≃* LinearFlag.projectiveSL n K} {t : G}
    {a b : Fin n} {X₀ X₀' : Subgroup (LinearFlag.projectiveSL n K)}
    (hX : modelToG e X₀ = modelToG e' X₀')
    (hD : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) =
      modelToG e' (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))))
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (htX' : t ∈ centralizer (modelToG e' X₀' : Set G))
    (h : LinearTwoFieldKindAtRoot e t a b X₀ htX) : LinearTwoFieldKindAtRoot e' t a b X₀' htX' :=
  (linearTwoFieldKindAtRoot_iff_fieldKindOver e' t a b X₀' htX').2
    (fieldKindOver_congr hX hD htX htX'
      ((linearTwoFieldKindAtRoot_iff_fieldKindOver e t a b X₀ htX).1 h))

theorem modelToG_trans_dualAut_map (e : L ≃* LinearFlag.projectiveSL n K)
    (A : Subgroup (LinearFlag.projectiveSL n K)) :
    modelToG (e.trans (LinearFlag.dualAut n K)) (A.map (LinearFlag.dualAut n K).toMonoidHom) =
      modelToG e A := by
  rw [modelToG_trans_eq, Subgroup.map_map]
  have hid : (LinearFlag.dualAut n K).symm.toMonoidHom.comp (LinearFlag.dualAut n K).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp
  rw [hid, Subgroup.map_id]

theorem map_dualAut_le_rootSL2 [Finite K] {a b : Fin n}
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b) :
    X₀.map (LinearFlag.dualAut n K).toMonoidHom ≤ rootSL2 a b := by
  have h := map_mono (f := (LinearFlag.dualAut n K).toMonoidHom) hX₀
  rwa [rootSL2_eq, map_blockSL_dualAut] at h

theorem card_map_dualAut (X₀ : Subgroup (LinearFlag.projectiveSL n K)) :
    Nat.card (X₀.map (LinearFlag.dualAut n K).toMonoidHom) = Nat.card X₀ :=
  Subgroup.card_map_of_injective (f := (LinearFlag.dualAut n K).toMonoidHom)
    (LinearFlag.dualAut n K).injective

theorem linearTwoFieldKindAtRoot_trans_dualAut [Finite K] {e : L ≃* LinearFlag.projectiveSL n K}
    {t : G} {a b : Fin n} {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hfk : LinearTwoFieldKindAtRoot e t a b X₀ htX) :
    ∃ htX' : t ∈ centralizer (modelToG (e.trans (LinearFlag.dualAut n K))
        (X₀.map (LinearFlag.dualAut n K).toMonoidHom) : Set G),
      LinearTwoFieldKindAtRoot (e.trans (LinearFlag.dualAut n K)) t a b
        (X₀.map (LinearFlag.dualAut n K).toMonoidHom) htX' := by
  have hX := modelToG_trans_dualAut_map e X₀
  have htX' : t ∈ centralizer (modelToG (e.trans (LinearFlag.dualAut n K))
      (X₀.map (LinearFlag.dualAut n K).toMonoidHom) : Set G) := hX ▸ htX
  exact ⟨htX', linearTwoFieldKindAtRoot_congr hX.symm (modelToG_trans_dualAut_blockSL e _).symm
    htX htX' hfk⟩

end FieldKind

section GOne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K] [CharP K 2]

theorem exists_gOne_of_labelDual_of_two
    (hlab : LinearTwoSwapLabelDualAtInput n) (hset : SeitzSetting G L) (hn : 5 ≤ n)
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hfact : ∀ k, k ∣ 2 ^ (2 * (n - 1)) →
      Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) K) ∣ (k - 1).factorial → 2 ^ (n - 1) ≤ k)
    {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁)
    {W₀ : Subgroup G} (hW₀c : Nat.card W₀ = 2 ^ (2 * (n - 1))) (hW₀2 : ∀ w ∈ W₀, w * w = 1)
    (hW₀t : W₀ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c₀))
    (htN₀ : t ∈ normalizer (W₀ : Set G))
    (hLW₀ : modelToG e (blockSL (K := K) ({c₀}ᶜ : Finset (Fin n))) ≤ normalizer (W₀ : Set G))
    (hs₀ : LinearTwoSwapTypeAtNOne e t c₀ W₀ htN₀)
    {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ (2 * (n - 1))) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) =
      modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical c₁))
    (htN₁ : t ∈ normalizer (W₁ : Set G))
    (hLW₁ : modelToG (e.trans (LinearFlag.dualAut n K))
      (blockSL (K := K) ({c₁}ᶜ : Finset (Fin n))) ≤ normalizer (W₁ : Set G))
    (hs₁ : LinearTwoSwapTypeAtNOne (e.trans (LinearFlag.dualAut n K)) t c₁ W₁ htN₁) :
    ∃ G₁ : Subgroup G, ⁅G₁, G₁⁆ = G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set e' := e.trans (LinearFlag.dualAut n K) with he'
  obtain ⟨X₀, hX₀⟩ :=
    exists_swapModuleData_of_swapType_of_dvd hset hn hK e ht hKt hW₀c hW₀2 hW₀t htN₀ hLW₀ hfact hs₀
  obtain ⟨X₁, hX₁⟩ :=
    exists_swapModuleData_of_swapType_of_dvd hset hn hK e' ht hKt hW₁c hW₁2 hW₁t htN₁ hLW₁ hfact hs₁
  have hd₀ : LinearTwoSwapModuleData e t c₀ W₀ X₀ := ⟨hW₀2, hW₀c, hW₀t, htN₀, hLW₀, hX₀⟩
  have hd₁ : LinearTwoSwapModuleData e' t c₁ W₁ X₁ := ⟨hW₁2, hW₁c, hW₁t, htN₁, hLW₁, hX₁⟩
  have hlab' : ∃ X₁' : Subgroup G, LinearTwoSwapModuleData e' t c₁ W₁ X₁' ∧
      X₁'.map (MulAut.conj t).toMonoidHom ≤ centralizer (X₀ : Set G) := by
    rcases hlab G L hset K hK t ht hKt e c₀ c₁ W₀ X₀ W₁ X₁ hc hd₀ hd₁ ⟨htN₀, hs₀⟩
        ⟨htN₁, hs₁⟩ with h | h
    · refine ⟨X₁.map (MulAut.conj t).toMonoidHom, hd₁.map_conj htt, ?_⟩
      rw [map_conj_map_conj_eq_of_mul_self htt]
      exact h
    · exact ⟨X₁, hd₁, h⟩
  obtain ⟨X₁', hd₁', h01⟩ := hlab'
  have hlevi : ∀ i : Fin 2, modelToG (![e, e'] i)
      (blockSL (K := K) ({![c₀, c₁] i}ᶜ : Finset (Fin n))) =
        modelToG (![e, e'] 0) (blockSL (K := K) ({![c₀, c₁] i}ᶜ : Finset (Fin n))) := by
    intro i
    fin_cases i
    · rfl
    · exact modelToG_trans_dualAut_blockSL e _
  refine exists_gOne_of_swapModuleData_of_levi hset (by omega) hK ![e, e'] ht hKt
    (c := ![c₀, c₁]) hc hlevi (W := ![W₀, W₁]) (X := ![X₀, X₁']) ?_ h01
  intro i
  fin_cases i
  · exact hd₀
  · exact hd₁'

end GOne

@[expose] def LFiveSwapTypeGOneDualTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c₀ c₁ : Fin 5), c₀ ≠ c₁ →
      (∀ W₁ : Subgroup G, Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
        W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c₀) →
        ∀ htN : t ∈ normalizer (W₁ : Set G),
        modelToG e (blockSL (K := K) ({c₀}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
        LinearTwoSwapTypeAtNOne e t c₀ W₁ htN) →
      (∀ W₁ : Subgroup G, Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
        W₁ ⊓ centralizer ({t} : Set G) =
          modelToG (e.trans (LinearFlag.dualAut 5 K)) (pointRadical c₁) →
        ∀ htN : t ∈ normalizer (W₁ : Set G),
        modelToG (e.trans (LinearFlag.dualAut 5 K)) (blockSL (K := K) ({c₁}ᶜ : Finset (Fin 5))) ≤
          normalizer (W₁ : Set G) →
        LinearTwoSwapTypeAtNOne (e.trans (LinearFlag.dualAut 5 K)) t c₁ W₁ htN) →
      ∃ G₁ : Subgroup G, ⁅G₁, G₁⁆ = G₁ ∧
        G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
        (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y

theorem lFiveSwapTypeGOneDualTwoInput_of_labelDual
    (hlab : LinearTwoSwapLabelDualAtInput 5) : LFiveSwapTypeGOneDualTwoInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c₀ c₁ hc hsw₀ hsw₁
  obtain ⟨W₀, hW₀c, hW₀2, hW₀t, htN₀, hLW₀⟩ := lFiveWOneInput G L hset K hK e t ht hKt c₀
  obtain ⟨W₁, hW₁c, hW₁2, hW₁t, htN₁, hLW₁⟩ :=
    lFiveWOneInput G L hset K hK (e.trans (LinearFlag.dualAut 5 K)) t ht hKt c₁
  exact exists_gOne_of_labelDual_of_two hlab hset (by norm_num) hK e ht hKt
    (two_pow_le_of_dvd_factorial_five hK) hc hW₀c hW₀2 hW₀t htN₀ hLW₀
    (hsw₀ W₀ hW₀c hW₀2 hW₀t htN₀ hLW₀) hW₁c hW₁2 hW₁t htN₁ hLW₁
    (hsw₁ W₁ hW₁c hW₁2 hW₁t htN₁ hLW₁)

theorem linearTwoFieldKindAtInput_five_of_dualTwo_field
    (hcat : SLmCatalogueClausesAt 4)
    (hdet : SLmEvenTypeDetAt 4) (hspor : SporadicFixedLFourTwoInput)
    (hnnF : LFiveNotNormalFieldInput) (hD : LFiveFieldNOneInput)
    (hE : LFiveSwapTypeGOneDualTwoInput) : LinearTwoFieldKindAtInput 5 := by
  intro G _ _ L hset n K _ _ hK hn e t ht hKt a b hab X₀ hX₀ hX₀c htX hZ Kc hKcomp hDK hsN hτ
    hmodel
  subst hn
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hfk : LinearTwoFieldKindAtRoot e t a b X₀ htX := ⟨hZ, Kc, hKcomp, hDK, hsN, hτ, hmodel⟩
  obtain ⟨htX', hfk'⟩ := linearTwoFieldKindAtRoot_trans_dualAut htX hfk
  have hX₀' := map_dualAut_le_rootSL2 (K := K) hX₀
  have hX₀'c : Nat.card (X₀.map (LinearFlag.dualAut 5 K).toMonoidHom) = Nat.card K + 1 := by
    rw [card_map_dualAut, hX₀c]
  obtain ⟨c₀, c₁, hc, h0a, h0b, h1a, h1b⟩ := exists_pair_ne_ne_of_fin_five hab
  obtain ⟨G₁, hperf, h₁₂, hδ, hsurj⟩ := hE G L hset K hK e t ht hKt c₀ c₁ hc
    (fun W₁ hW₁c hW₁2 hW₁t htN hLN => linearTwoSwapTypeAtNOne_of_fieldRoot hcat hdet hspor hnnF
      hD hset hK e ht hKt hab hX₀ hX₀c htX hfk h0a h0b hW₁c hW₁2 hW₁t htN hLN)
    (fun W₁ hW₁c hW₁2 hW₁t htN hLN => linearTwoSwapTypeAtNOne_of_fieldRoot hcat hdet hspor hnnF
      hD hset hK _ ht hKt hab hX₀' hX₀'c htX' hfk' h1a h1b hW₁c hW₁2 hW₁t htN hLN)
  exact false_of_fieldKind_of_gOne_five hset hK e ht hKt hab hX₀ hX₀c htX hKcomp hDK hsN hτ
    hmodel hperf h₁₂ hδ hsurj

theorem linearTwoFieldKindAtInput_five_of_labelDual_field
    (hcat : SLmCatalogueClausesAt 4)
    (hdet : SLmEvenTypeDetAt 4) (hspor : SporadicFixedLFourTwoInput)
    (hnnF : LFiveNotNormalFieldInput) (hD : LFiveFieldNOneInput)
    (hlab : LinearTwoSwapLabelDualAtInput 5) : LinearTwoFieldKindAtInput 5 :=
  linearTwoFieldKindAtInput_five_of_dualTwo_field hcat hdet hspor hnnF hD
    (lFiveSwapTypeGOneDualTwoInput_of_labelDual hlab)

end CFSG.SeitzReduction.LinearPilot
