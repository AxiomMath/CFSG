module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2e

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Case2

variable (C : S.Case2)

section V

variable {V : Subgroup X} (hT₁V : C.T₁ ≤ V) (hVN : V ≤ normalizer (S.E C.yb : Set X))
  (hVc : Nat.card V = 4 * Nat.card S.data.T) (hVp : IsPGroup 2 V)
  (hVE : ∀ v ∈ V, (∀ e ∈ S.E C.yb, v * e = e * v) → v ∈ S.E C.yb)

include hVE in
theorem mem_E_of_π_eq_one {v : X} (hv : v ∈ V) (h : C.π (C.ofV hVN hv) = 1) :
    v ∈ S.E C.yb := by
  refine hVE v hv fun e he => ?_
  have := (C.π_eq_one_iff (C.ofV hVN hv)).mp h e he
  change v * e * v⁻¹ = e at this
  calc v * e = v * e * v⁻¹ * v := by group
    _ = e * v := by rw [this]

include hT₁V hVc hVp hVE in
theorem exists_s : ∃ (s : X) (hs : s ∈ V), C.π (C.ofV hVN hs) = swap 0 2 * swap 1 3 ∧
    s ^ 2 = 1 := by
  obtain ⟨s₀, hs₀, hπs₀⟩ := C.exists_s₀ hT₁V hVN hVc hVp
  have hqV : s₀ * s₀ ∈ V := mul_mem hs₀ hs₀
  have hπq : C.π (C.ofV hVN hqV) = 1 := by
    have : C.ofV hVN hqV = C.ofV hVN hs₀ * C.ofV hVN hs₀ := rfl
    rw [this, map_mul, hπs₀]
    decide
  have hqE := C.mem_E_of_π_eq_one hVN hVE hqV hπq
  obtain ⟨v, hv⟩ := C.exists_wordV hqE
  have hfix : Mσ (swap 0 2 * swap 1 3) v = v := by
    rw [← hπs₀, ← C.conj_wordV_eq_iff, ← hv]
    change s₀ * (s₀ * s₀) * s₀⁻¹ = s₀ * s₀
    group
  have hvE : C.wordV (v.1, v.2.1, 0, 0) ∈ S.E C.yb := C.wordV_mem _
  have hwV : C.wordV (v.1, v.2.1, 0, 0) ∈ V :=
    hT₁V (C.T_le (C.E_le_T hvE))
  refine ⟨C.wordV (v.1, v.2.1, 0, 0) * s₀, mul_mem hwV hs₀, ?_, ?_⟩
  · have : C.ofV hVN (mul_mem hwV hs₀) = ⟨_, Subgroup.le_normalizer hvE⟩ * C.ofV hVN hs₀ := rfl
    rw [this, map_mul, C.π_of_mem_E hvE, hπs₀, one_mul]
  · have hconj := C.conj_wordV (C.ofV hVN hs₀) (v.1, v.2.1, 0, 0)
    change s₀ * C.wordV (v.1, v.2.1, 0, 0) * s₀⁻¹ = _ at hconj
    rw [hπs₀] at hconj
    have key : ∀ v : V4, Mσ (swap 0 2 * swap 1 3) v = v →
        addV (addV (v.1, v.2.1, 0, 0) (Mσ (swap 0 2 * swap 1 3) (v.1, v.2.1, 0, 0))) v =
          (0, 0, 0, 0) := by decide
    calc (C.wordV (v.1, v.2.1, 0, 0) * s₀) ^ 2
        = C.wordV (v.1, v.2.1, 0, 0) * (s₀ * C.wordV (v.1, v.2.1, 0, 0) * s₀⁻¹) * (s₀ * s₀) := by
          rw [pow_two]; group
      _ = C.wordV (addV (addV (v.1, v.2.1, 0, 0)
            (Mσ (swap 0 2 * swap 1 3) (v.1, v.2.1, 0, 0))) v) := by
          rw [hconj, hv, C.wordV_add, C.wordV_add]
      _ = 1 := by rw [key v hfix]; simp [wordV, word]

include hT₁V hVN hVc hVp hVE in
theorem exists_E8 : ∃ E₈ : Subgroup X, E₈ ≤ V ∧ ElemAbelianTwo E₈ ∧ Nat.card E₈ = 8 ∧
    ∀ v ∈ V, (∀ e ∈ E₈, v * e = e * v) → v ∈ E₈ := by
  obtain ⟨s, hs, hπs, hs2⟩ := C.exists_s hT₁V hVN hVc hVp hVE
  set p := C.wordV (1, 0, 0, 1) with hp
  set q := C.wordV (0, 1, 1, 0) with hq
  have hpE : p ∈ S.E C.yb := C.wordV_mem _
  have hqE : q ∈ S.E C.yb := C.wordV_mem _
  have hp2 : p ^ 2 = 1 := S.E_sq C.yb_mem C.yb_sq hpE
  have hq2 : q ^ 2 = 1 := S.E_sq C.yb_mem C.yb_sq hqE
  have hEV : S.E C.yb ≤ V := C.E_le_T.trans (C.T_le.trans hT₁V)
  have h1 : C.wordV (0, 0, 0, 0) = 1 := by simp [wordV, word]
  have hp1 : p ≠ 1 := fun h => by
    have := C.wordV_injective (h.trans h1.symm)
    exact absurd this (by decide)
  have hpq : q ∉ (⊥ ⊔ zpowers p : Subgroup X) := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers hp2 ((sup_le bot_le le_rfl :
      (⊥ ⊔ zpowers p : Subgroup X) ≤ zpowers p) h) with h' | h'
    · exact absurd (C.wordV_injective (h'.trans h1.symm)) (by decide)
    · exact absurd (C.wordV_injective h') (by decide)
  have hsfix : ∀ w : V4, Mσ (swap 0 2 * swap 1 3) w = w →
      s * C.wordV w = C.wordV w * s := by
    intro w hw
    have := (C.conj_wordV_eq_iff (C.ofV hVN hs) w).mpr (by rw [hπs]; exact hw)
    change s * C.wordV w * s⁻¹ = C.wordV w at this
    calc s * C.wordV w = s * C.wordV w * s⁻¹ * s := by group
      _ = C.wordV w * s := by rw [this]
  have hsp : s * p = p * s := hsfix _ (by decide)
  have hsq : s * q = q * s := hsfix _ (by decide)
  have hsE : s ∉ S.E C.yb := by
    intro h
    have := C.π_of_mem_E h
    have heq : C.ofV hVN hs = ⟨s, Subgroup.le_normalizer h⟩ := rfl
    rw [← heq, hπs] at this
    exact absurd this (by decide)
  obtain ⟨hV1, hV1m, hV1c⟩ := ElemAbelianTwo.bot.sup_zpowers hp2 (fun h => hp1 (mem_bot.mp h))
    (fun a ha => by rw [mem_bot.mp ha, one_mul, mul_one])
  have hV1E : (⊥ ⊔ zpowers p : Subgroup X) ≤ S.E C.yb := sup_le bot_le (zpowers_le.mpr hpE)
  obtain ⟨hV2, hV2m, hV2c⟩ := hV1.sup_zpowers hq2 hpq
    (fun a ha => C.comm hqE (hV1E ha))
  have hV2E : (⊥ ⊔ zpowers p ⊔ zpowers q : Subgroup X) ≤ S.E C.yb :=
    sup_le hV1E (zpowers_le.mpr hqE)
  have hscomm : ∀ a ∈ (⊥ ⊔ zpowers p ⊔ zpowers q : Subgroup X), s * a = a * s := by
    intro a ha
    rcases hV2m a ha with h | h
    · rcases eq_one_or_eq_of_mem_zpowers hp2 ((sup_le bot_le le_rfl :
        (⊥ ⊔ zpowers p : Subgroup X) ≤ zpowers p) h) with rfl | rfl
      · group
      · exact hsp
    · have hap : a * q ∈ zpowers p := (sup_le bot_le le_rfl :
        (⊥ ⊔ zpowers p : Subgroup X) ≤ zpowers p) h
      have ha' : a = (a * q) * q := by
        rw [mul_assoc, ← pow_two, hq2, mul_one]
      rcases eq_one_or_eq_of_mem_zpowers hp2 hap with h' | h' <;> rw [ha', h']
      · rw [one_mul]; exact hsq
      · calc s * (p * q) = p * (s * q) := by rw [← mul_assoc, hsp, mul_assoc]
          _ = p * q * s := by rw [hsq, mul_assoc]
  obtain ⟨hV3, hV3m, hV3c⟩ := hV2.sup_zpowers hs2 (fun h => hsE (hV2E h)) hscomm
  refine ⟨⊥ ⊔ zpowers p ⊔ zpowers q ⊔ zpowers s,
    sup_le (hV2E.trans hEV) (zpowers_le.mpr hs), hV3, ?_, fun v hv hc => ?_⟩
  · rw [hV3c, hV2c, hV1c, Subgroup.card_bot]
  have hpE8 : p ∈ (⊥ ⊔ zpowers p ⊔ zpowers q ⊔ zpowers s : Subgroup X) :=
    mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers p)))
  have hqE8 : q ∈ (⊥ ⊔ zpowers p ⊔ zpowers q ⊔ zpowers s : Subgroup X) :=
    mem_sup_left (mem_sup_right (mem_zpowers q))
  have hsE8 : s ∈ (⊥ ⊔ zpowers p ⊔ zpowers q ⊔ zpowers s : Subgroup X) :=
    mem_sup_right (mem_zpowers s)
  have hvfix : ∀ w : V4, C.wordV w ∈ (⊥ ⊔ zpowers p ⊔ zpowers q ⊔ zpowers s : Subgroup X) →
      Mσ (C.π (C.ofV hVN hv)) w = w := by
    intro w hw
    rw [← C.conj_wordV_eq_iff]
    change v * C.wordV w * v⁻¹ = C.wordV w
    rw [hc _ hw]
    group
  have hπp := hvfix _ hpE8
  have hπq := hvfix _ hqE8
  have hvD := C.π_mem_D8 hT₁V hVN hVc hv
  have key : ∀ σ ∈ D8, Mσ σ (1, 0, 0, 1) = (1, 0, 0, 1) → Mσ σ (0, 1, 1, 0) = (0, 1, 1, 0) →
      σ = 1 ∨ σ = swap 0 2 * swap 1 3 := by decide
  have hEs : ∀ g ∈ S.E C.yb, s * g = g * s →
      g ∈ (⊥ ⊔ zpowers p ⊔ zpowers q ⊔ zpowers s : Subgroup X) := by
    intro g hg hgs
    obtain ⟨w, rfl⟩ := C.exists_wordV hg
    have hw : Mσ (swap 0 2 * swap 1 3) w = w := by
      rw [← hπs, ← C.conj_wordV_eq_iff]
      change s * C.wordV w * s⁻¹ = C.wordV w
      rw [hgs]
      group
    have key2 : ∀ w : V4, Mσ (swap 0 2 * swap 1 3) w = w →
        w = (0, 0, 0, 0) ∨ w = (1, 0, 0, 1) ∨ w = (0, 1, 1, 0) ∨ w = (1, 1, 1, 1) := by decide
    rcases key2 w hw with rfl | rfl | rfl | rfl
    · rw [h1]
      exact one_mem _
    · exact hpE8
    · exact hqE8
    · rw [show ((1, 1, 1, 1) : V4) = addV (1, 0, 0, 1) (0, 1, 1, 0) by decide, C.wordV_add]
      exact mul_mem hpE8 hqE8
  rcases key _ hvD hπp hπq with h | h
  · exact hEs v (C.mem_E_of_π_eq_one hVN hVE hv h) (hc _ hsE8).symm
  · have hvs : v * s ∈ V := mul_mem hv hs
    have hπvs : C.π (C.ofV hVN hvs) = 1 := by
      have : C.ofV hVN hvs = C.ofV hVN hv * C.ofV hVN hs := rfl
      rw [this, map_mul, h, hπs]
      decide
    have hvsE := C.mem_E_of_π_eq_one hVN hVE hvs hπvs
    have hcomm : s * (v * s) = v * s * s := by
      rw [← mul_assoc, ← hc _ hsE8]
    have hmem := hEs _ hvsE hcomm
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hs2])
    have : v = v * s * s := by rw [mul_assoc, ← pow_two, hs2, mul_one]
    rw [this]
    exact mul_mem hmem hsE8

end V

end Case2

end A7Base

end CFSG.ComponentClassification.HSFLit
