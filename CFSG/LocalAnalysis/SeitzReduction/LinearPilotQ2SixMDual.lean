module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMGOne
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveESix

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem modelToG_trans_eq (e : L ≃* LinearFlag.projectiveSL n K)
    (σ : MulAut (LinearFlag.projectiveSL n K)) (A : Subgroup (LinearFlag.projectiveSL n K)) :
    modelToG (e.trans σ) A = modelToG e (A.map σ.symm.toMonoidHom) := by
  ext g
  rw [mem_modelToG, mem_modelToG]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ.symm x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem map_mulAut_symm_eq_of_map_eq {P : Type*} [Group P] {σ : MulAut P} {A : Subgroup P}
    (h : A.map σ.toMonoidHom = A) : A.map σ.symm.toMonoidHom = A := by
  calc A.map σ.symm.toMonoidHom = (A.map σ.toMonoidHom).map σ.symm.toMonoidHom := by rw [h]
    _ = A := by
      rw [Subgroup.map_map]
      have hid : σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [hid, Subgroup.map_id]

theorem modelToG_trans_dualAut_blockSL [Finite K] (e : L ≃* LinearFlag.projectiveSL n K)
    (I : Finset (Fin n)) :
    modelToG (e.trans (LinearFlag.dualAut n K)) (blockSL (K := K) I) =
      modelToG e (blockSL (K := K) I) := by
  rw [modelToG_trans_eq, map_mulAut_symm_eq_of_map_eq (map_blockSL_dualAut (K := K) I)]

@[expose] def SwapKindOver (H D : Subgroup G) (t : G) (htX : t ∈ centralizer (H : Set G)) : Prop :=
  ∃ Kc : Subgroup (centralizer (H : Set G) ⧸ oddCore (centralizer (H : Set G))),
    IsComponent Kc ∧
    (D.subgroupOf (centralizer (H : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (H : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (H : Set G)))
        ⟨t, htX⟩)).toMonoidHom ∧
    Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (H : Set G)))
      ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
    ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (H : Set G)))
      ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
    center Kc = ⊥ ∧
    Nonempty (Kc ≃* (D.subgroupOf (centralizer (H : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (H : Set G)))))

theorem linearTwoSwapKindAt_iff_swapKindOver (e : L ≃* LinearFlag.projectiveSL n K) (t : G)
    (a b : Fin n) (X₀ : Subgroup (LinearFlag.projectiveSL n K))
    (htX : t ∈ centralizer (modelToG e X₀ : Set G)) :
    LinearTwoSwapKindAt e t a b X₀ htX ↔
      SwapKindOver (modelToG e X₀) (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))) t
        htX :=
  Iff.rfl

theorem swapKindOver_congr {H H' D D' : Subgroup G} {t : G} (hH : H = H') (hD : D = D')
    (htX : t ∈ centralizer (H : Set G)) (htX' : t ∈ centralizer (H' : Set G))
    (h : SwapKindOver H D t htX) : SwapKindOver H' D' t htX' := by
  subst hH
  subst hD
  exact h

theorem linearTwoSwapKindAt_congr {e e' : L ≃* LinearFlag.projectiveSL n K} {t : G} {a b : Fin n}
    {X₀ X₀' : Subgroup (LinearFlag.projectiveSL n K)} (hX : modelToG e X₀ = modelToG e' X₀')
    (hD : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) =
      modelToG e' (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))))
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (htX' : t ∈ centralizer (modelToG e' X₀' : Set G))
    (h : LinearTwoSwapKindAt e t a b X₀ htX) : LinearTwoSwapKindAt e' t a b X₀' htX' :=
  (linearTwoSwapKindAt_iff_swapKindOver e' t a b X₀' htX').2
    (swapKindOver_congr hX hD htX htX' ((linearTwoSwapKindAt_iff_swapKindOver e t a b X₀ htX).1 h))

theorem linearTwoSwapKindAt_trans_dualAut [Finite K] {e : L ≃* LinearFlag.projectiveSL n K}
    {t : G}
    (hall : ∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) :
    ∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG (e.trans (LinearFlag.dualAut n K)) X₀ : Set G),
        LinearTwoSwapKindAt (e.trans (LinearFlag.dualAut n K)) t a b X₀ htX := by
  intro a b hab X₀ hX₀ hc htX
  have hX : modelToG (e.trans (LinearFlag.dualAut n K)) X₀ =
      modelToG e (X₀.map (LinearFlag.dualAut n K).symm.toMonoidHom) :=
    modelToG_trans_eq e _ X₀
  have hroot : (rootSL2 (K := K) a b).map (LinearFlag.dualAut n K).symm.toMonoidHom =
      rootSL2 a b := by
    rw [rootSL2_eq]
    exact map_mulAut_symm_eq_of_map_eq (map_blockSL_dualAut (K := K) _)
  have hX₀' : X₀.map (LinearFlag.dualAut n K).symm.toMonoidHom ≤ rootSL2 a b :=
    hroot ▸ map_mono hX₀
  have hc' : Nat.card (X₀.map (LinearFlag.dualAut n K).symm.toMonoidHom) = Nat.card K + 1 := by
    rw [Subgroup.card_map_of_injective (f := (LinearFlag.dualAut n K).symm.toMonoidHom)
      (LinearFlag.dualAut n K).symm.injective, hc]
  have htX' : t ∈ centralizer
      (modelToG e (X₀.map (LinearFlag.dualAut n K).symm.toMonoidHom) : Set G) := hX ▸ htX
  exact linearTwoSwapKindAt_congr hX.symm (modelToG_trans_dualAut_blockSL e _).symm htX' htX
    (hall a b hab _ hX₀' hc' htX')

end Transport

section Assembly

@[expose] def LinearTwoSwapLabelDualAtInput (n₀ : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → ∀ (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (e : L ≃* LinearFlag.projectiveSL n₀ K) (c₀ c₁ : Fin n₀) (W₀ X₀ W₁ X₁ : Subgroup G),
      c₀ ≠ c₁ → LinearTwoSwapModuleData e t c₀ W₀ X₀ →
      LinearTwoSwapModuleData (e.trans (LinearFlag.dualAut n₀ K)) t c₁ W₁ X₁ →
      (∃ htN : t ∈ normalizer (W₀ : Set G), LinearTwoSwapTypeAtNOne e t c₀ W₀ htN) →
      (∃ htN : t ∈ normalizer (W₁ : Set G),
        LinearTwoSwapTypeAtNOne (e.trans (LinearFlag.dualAut n₀ K)) t c₁ W₁ htN) →
      X₁ ≤ centralizer (X₀ : Set G) ∨
        X₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (X₀ : Set G)

@[expose] def LSixSwapLabelDualInput : Prop :=
  LinearTwoSwapLabelDualAtInput 6

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K] [CharP K 2]

theorem exists_gOne_of_labelDual_of_swapTypes
    (hlab : LinearTwoSwapLabelDualAtInput n) (hset : SeitzSetting G L) (hn : 5 ≤ n)
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hfact : ∀ k, k ∣ 2 ^ (2 * (n - 1)) →
      Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) K) ∣ (k - 1).factorial → 2 ^ (n - 1) ≤ k)
    (hsw₀ : ∀ c : Fin n, ∃ W₁ : Subgroup G, Nat.card W₁ = 2 ^ (2 * (n - 1)) ∧
      (∀ w ∈ W₁, w * w = 1) ∧ W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) ∧
      ∃ htN : t ∈ normalizer (W₁ : Set G),
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤ normalizer (W₁ : Set G) ∧
        LinearTwoSwapTypeAtNOne e t c W₁ htN)
    (hsw₁ : ∀ c : Fin n, ∃ W₁ : Subgroup G, Nat.card W₁ = 2 ^ (2 * (n - 1)) ∧
      (∀ w ∈ W₁, w * w = 1) ∧ W₁ ⊓ centralizer ({t} : Set G) =
        modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical c) ∧
      ∃ htN : t ∈ normalizer (W₁ : Set G),
        modelToG (e.trans (LinearFlag.dualAut n K)) (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤
          normalizer (W₁ : Set G) ∧
        LinearTwoSwapTypeAtNOne (e.trans (LinearFlag.dualAut n K)) t c W₁ htN) :
    ∃ G₁ : Subgroup G, ⁅G₁, G₁⁆ = G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set e' := e.trans (LinearFlag.dualAut n K) with he'
  set c₀ : Fin n := ⟨0, by omega⟩ with hc₀
  set c₁ : Fin n := ⟨1, by omega⟩ with hc₁
  have hc : c₀ ≠ c₁ := by
    intro h
    have h' := congrArg Fin.val h
    simp [hc₀, hc₁] at h'
  obtain ⟨W₀, hW₀c, hW₀2, hW₀t, htN₀, hLW₀, hs₀⟩ := hsw₀ c₀
  obtain ⟨X₀, hX₀⟩ :=
    exists_swapModuleData_of_swapType_of_dvd hset hn hK e ht hKt hW₀c hW₀2 hW₀t htN₀ hLW₀ hfact hs₀
  obtain ⟨W₁, hW₁c, hW₁2, hW₁t, htN₁, hLW₁, hs₁⟩ := hsw₁ c₁
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

theorem exists_gOne_of_labelDual_of_dvd
    (hlab : LinearTwoSwapLabelDualAtInput n) (hset : SeitzSetting G L) (hn : 5 ≤ n)
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hfact : ∀ k, k ∣ 2 ^ (2 * (n - 1)) →
      Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) K) ∣ (k - 1).factorial → 2 ^ (n - 1) ≤ k)
    (hsw : ∀ e' : L ≃* LinearFlag.projectiveSL n K,
      (∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e' X₀ : Set G), LinearTwoSwapKindAt e' t a b X₀ htX) →
      ∀ c : Fin n, ∃ W₁ : Subgroup G, Nat.card W₁ = 2 ^ (2 * (n - 1)) ∧
        (∀ w ∈ W₁, w * w = 1) ∧ W₁ ⊓ centralizer ({t} : Set G) = modelToG e' (pointRadical c) ∧
        ∃ htN : t ∈ normalizer (W₁ : Set G),
          modelToG e' (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤ normalizer (W₁ : Set G) ∧
          LinearTwoSwapTypeAtNOne e' t c W₁ htN)
    (hall : ∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) :
    ∃ G₁ : Subgroup G, ⁅G₁, G₁⁆ = G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact exists_gOne_of_labelDual_of_swapTypes hlab hset hn hK e ht hKt hfact (hsw e hall)
    (hsw _ (linearTwoSwapKindAt_trans_dualAut hall))

theorem lSixSwapGOneInput_of_labelDual
    (hlab : LSixSwapLabelDualInput) :
    LSixSwapGOneInput := by
  intro G _ _ L hset K _ _ hK t ht hKt hhyp e hall
  exact exists_gOne_of_labelDual_of_dvd hlab hset (by norm_num) hK e ht hKt
    (two_pow_le_of_dvd_factorial_six hK) hhyp hall

end Assembly

end CFSG.SeitzReduction.LinearPilot
