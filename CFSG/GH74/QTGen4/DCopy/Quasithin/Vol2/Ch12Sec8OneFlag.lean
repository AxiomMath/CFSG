module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneExist

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

section Hyp

variable {G : Type} [Group G]

theorem card_autOn_sylow_F4 (h1222 : Stmt12_2_2_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) : Nat.card (autOn T V) = 2 ^ Flag.tri n := by
  obtain ⟨hcard, hsq, -⟩ := h.card_sq
  obtain ⟨hc, hnat⟩ := h.natural
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hn : 1 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  have hle := card_autOn_le hsq hcard h.hyp.sylow.1 (T := T)
  have hL : 2 ^ Flag.tri n ∣ Nat.card (autOn L V) := by
    rw [card_eq_of_binaryNaturalSL hnat hn, tri_eq]
    exact dvd_mul_right _ _
  have hLT : 2 ^ Flag.tri n ∣ Nat.card (autOn (L ⊔ T) V) :=
    hL.trans (Subgroup.card_dvd_of_le (autOn_mono le_sup_left))
  have hodd : ¬ 2 ∣ (autOn T V).relIndex (autOn (L ⊔ T) V) := by
    intro h2
    apply h.hyp.sylow.2
    have hAB : T.subgroupOf (Subgroup.normalizer (V : Set G)) ≤
        (L ⊔ T).subgroupOf (Subgroup.normalizer (V : Set G)) := fun x hx =>
      Subgroup.mem_subgroupOf.2 ((le_sup_right : T ≤ L ⊔ T) (Subgroup.mem_subgroupOf.1 hx))
    have e1 := relIndex_map_dvd (conjAct V) hAB
    rw [Subgroup.relIndex_subgroupOf (sup_le hLV hTV)] at e1
    exact h2.trans (e1.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
  have hmul := Subgroup.relIndex_mul_card (autOn T V) (autOn (L ⊔ T) V)
  rw [inf_eq_left.2 (autOn_mono le_sup_right)] at hmul
  have hcop : Nat.Coprime (2 ^ Flag.tri n) ((autOn T V).relIndex (autOn (L ⊔ T) V)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hdvd : 2 ^ Flag.tri n ∣ Nat.card (autOn T V) := by
    rw [← hmul] at hLT
    exact hcop.dvd_of_dvd_mul_left hLT
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)

theorem tinv_comparable_of_hyp1281One_F4 (h1222 : Stmt12_2_2_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
    {n : ℕ} (h : Hyp1281One G T L V n) {W W' : Subgroup G} (hWV : W ≤ V) (hW'V : W' ≤ V)
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hTW' : T ≤ Subgroup.normalizer (W' : Set G)) :
    W ≤ W' ∨ W' ≤ W := by
  obtain ⟨hcard, hsq, -⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  exact tinv_comparable hsq hcard h.hyp.sylow.1 (card_autOn_sylow_F4 h1222 h) hWV hW'V hTW hTW'

theorem unique1282_F4 (h1222 : Stmt12_2_2_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
      ∀ (i : ℕ) (W W' : Subgroup G), IsTSub T V W i → IsTSub T V W' i → W = W' := by
  intro G _ _ T L V n h i W W' hW hW'
  rcases tinv_comparable_of_hyp1281One_F4 h1222 h hW.1 hW'.1 hW.2.2 hW'.2.2 with hle | hle
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hW.2.1, hW'.2.1])
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hW.2.1, hW'.2.1])).symm

end Hyp

section Exist

variable {G : Type} [Group G]

theorem exist1282g_F4 (h1222 : Stmt12_2_2_F4) : Exist1282g_F4 := by
  intro G _ _ T L V n h V₁ hV₁
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hn2 : 2 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  obtain ⟨V₂, hV₂, hV₁₂⟩ := exists_tsub_two_of_one h.hyp.sylow.1 hsq hab hTV hcard hn2 hV₁
  obtain ⟨v₁, hv₁, hv₁1⟩ : ∃ v ∈ V₁, v ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    have h1 := hV₁.2.1
    rw [hbot, Subgroup.card_bot] at h1
    norm_num at h1
  obtain ⟨v₂, hv₂, hv₂1⟩ : ∃ v ∈ V₂, v ∉ V₁ := by
    by_contra hne
    push Not at hne
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from hne)
    rw [hV₂.2.1, hV₁.2.1] at h1
    norm_num at h1
  have hv₁V := hV₁.1 hv₁
  have hv₂V := hV₂.1 hv₂
  let _ := zmodModuleOf hsq
  set a₁ : Additive ↥V := Additive.ofMul ⟨v₁, hv₁V⟩ with ha₁
  set a₂ : Additive ↥V := Additive.ofMul ⟨v₂, hv₂V⟩ with ha₂
  have ha : a₁ ∉ (ZMod 2) ∙ a₂ := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul] at hc
      apply hv₁1
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simpa [ha₁] using this.symm
    · rw [one_smul] at hc
      apply hv₂1
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₁, ha₂, toMul_ofMul] at this
      rw [this]
      exact hv₁
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem ha
  have hfa₂ : f a₂ = 0 := LinearMap.mem_ker.1 (hf2 (Submodule.mem_span_singleton_self a₂))
  have hfa₁ : f a₁ = 1 := Flag.zmod_two_eq_one hf1
  let τ0 : Additive ↥V →ₗ[ZMod 2] Additive ↥V := LinearMap.id + f.smulRight a₂
  have hτ0 : ∀ x, τ0 x = x + f x • a₂ := fun x => rfl
  have hinv : Function.Involutive τ0 := by
    intro x
    rw [hτ0, hτ0, map_add, map_smul, hfa₂, smul_zero, add_zero, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  let α : MulAut ↥V :=
    { toFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      invFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      left_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      right_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      map_mul' := fun x y => by simp only [ofMul_mul, map_add, toMul_add] }
  have hα : ∀ x : ↥V, ((α x : ↥V) : G) = (x : G) ∨ ((α x : ↥V) : G) = (x : G) * v₂ := by
    intro x
    have e : α x = x * Additive.toMul (f (Additive.ofMul x) • a₂) := by
      show Additive.toMul (τ0 (Additive.ofMul x)) = _
      rw [hτ0, toMul_add, toMul_ofMul]
    rcases zmod_two_cases (f (Additive.ofMul x)) with h0 | h1
    · left
      rw [e, h0, zero_smul, toMul_zero, mul_one]
    · right
      rw [e, h1, one_smul, Subgroup.coe_mul, ha₂, toMul_ofMul]
  have hα₁ : ((α ⟨v₁, hv₁V⟩ : ↥V) : G) = v₁ * v₂ := by
    show ((Additive.toMul (τ0 a₁) : ↥V) : G) = _
    rw [hτ0, hfa₁, one_smul, toMul_add, Subgroup.coe_mul, ha₁, ha₂, toMul_ofMul, toMul_ofMul]
  have hαL : α ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨g, hgN⟩, hgL, hgα⟩ := hαL
  have hconj : ∀ x (hx : x ∈ V), g * x * g⁻¹ = ((α ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hgα]
    rfl
  refine ⟨g, Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hgL),
    Subgroup.mem_iInf.2 fun Y => Subgroup.mem_iInf.2 fun hY => ?_⟩, fun hgV₁ => ?_⟩
  · obtain ⟨i, hi, hYi⟩ := hY
    have hV₂Y : V₂ ≤ Y := by
      rcases tinv_comparable_of_hyp1281One_F4 h1222 h hV₂.1 hYi.1 hV₂.2.2 hYi.2.2 with hle | hle
      · exact hle
      · have heq : Y = V₂ := Subgroup.eq_of_le_of_card_ge hle (by
          rw [hV₂.2.1, hYi.2.1]
          exact Nat.pow_le_pow_right (by norm_num) hi)
        rw [heq]
    have hv₂Y : v₂ ∈ Y := hV₂Y hv₂
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyV := hYi.1 hy
      rw [hconj y hyV]
      rcases hα ⟨y, hyV⟩ with e | e
      · rw [e]
        exact hy
      · rw [e]
        exact Y.mul_mem hy hv₂Y
    · intro hy
      have hyV : y ∈ V := (Subgroup.mem_normalizer_iff.1 hgN y).2 (hYi.1 hy)
      rw [hconj y hyV] at hy
      rcases hα ⟨y, hyV⟩ with e | e
      · rw [e] at hy
        exact hy
      · rw [e] at hy
        have := Y.mul_mem hy (Y.inv_mem hv₂Y)
        rwa [mul_inv_cancel_right] at this
  · have h1 : g * v₁ * g⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 hgV₁ v₁).1 hv₁
    rw [hconj v₁ hv₁V, hα₁] at h1
    apply hv₂1
    have := V₁.mul_mem (V₁.inv_mem hv₁) h1
    rwa [inv_mul_cancel_left] at this

end Exist

end CFSG.Quasithin.H13
