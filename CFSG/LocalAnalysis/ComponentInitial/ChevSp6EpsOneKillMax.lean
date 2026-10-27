
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillMaxBase

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillSylow

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ}
  {z l₁ l₂ : G} (h : KillData u Jh E cV cE z l₁ l₂)

include h

variable [Finite G]

theorem conj_le_Jh {A : Subgroup G} (hAJ : A ≤ Jh) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a * a = 1) (hcard : 2 ^ (if u then 9 else 12) ≤ Nat.card A) {g : G}
    (hg : g ∈ normalizer (h.SG : Set G)) : A.map (MulAut.conj g).toMonoidHom ≤ Jh := by
  by_contra hne
  have hS : A.map (MulAut.conj g).toMonoidHom ≤ h.SG := by
    rintro _ ⟨a, ha, rfl⟩
    exact (mem_normalizer_iff.1 hg a).1 (h.Jh_le_SG (hAJ ha))
  have h1 := h.card_lt_of_ea hS (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hcomm a ha b hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group) (by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group) hne
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1
  omega

theorem normalizer_le_L (hu : u = false) {g : G} (hg : g ∈ normalizer (h.SG : Set G)) :
    g ∈ normalizer (Jh : Set G) := by
  have hJl := h.conj_le_Jh h.Jl_le (h.Jl_ea hu).1 (h.Jl_ea hu).2
    (by rw [h.card_Jl, hu]; norm_num) hg
  have hJr := h.conj_le_Jh h.Jr_le (h.Jr_ea hu).1 (h.Jr_ea hu).2
    (by rw [h.card_Jr, hu]; norm_num) hg
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have hmem : g * x * g⁻¹ ∈ (h.Jl ⊔ h.Jr).map (MulAut.conj g).toMonoidHom :=
    ⟨x, h.Jh_le_sup hx, rfl⟩
  rw [Subgroup.map_sup] at hmem
  exact sup_le hJl hJr hmem

theorem normalizer_le_U (hu : u = true) {g : G} (hg : g ∈ normalizer (h.SG : Set G)) :
    g ∈ normalizer (Jh : Set G) := by
  have hEconj : ∀ {g' : G}, g' ∈ normalizer (h.SG : Set G) → ∀ e ∈ E, g' * e * g'⁻¹ ∈ E := by
    intro g' hg' e he
    have hle := h.conj_le_Jh h.E_le (fun a ha b hb => h.central a ha b (h.E_le hb))
      (fun a ha => h.E_sq ha) (by rw [h.card_E, hu]; norm_num) hg'
    have hy : g' * e * g'⁻¹ ∈ Jh := hle ⟨e, he, rfl⟩
    refine (h.cV_eq_zero _ hy).1 (aniso _ (h.cV_lt _ hy) ?_)
    rw [← hu, ← (h.sq _ hy).2,
      show g' * e * g'⁻¹ * (g' * e * g'⁻¹) = g' * (e * e) * g'⁻¹ by group, h.E_sq he]
    simp [h.cE_one]
  have hC : ∀ x ∈ h.SG, (∀ e ∈ E, x * e * x⁻¹ = e) → x ∈ Jh := by
    intro x hx hxE
    have hxX := h.SG_le_X hx
    set σ := h.ρV ⟨x, hxX⟩ with hσdef
    have hσ : σ ∈ Gq u := h.ρV_mem_Gq _
    have hE1 : ∀ y : Fin 512, eAct u σ y = y := by
      intro y
      rw [h.eAct_ρV, h.ρE_apply]
      show cE (x * h.liftE y * x⁻¹) = y
      rw [hxE _ (h.liftE_mem y), h.cE_liftE y.2]
    have hbid : bOf u (tupleOf σ) = idE := by
      apply List.ext_getElem
      · rw [length_bOf]; rfl
      · intro j hj _
        have hj9 : j < 9 := by rwa [length_bOf] at hj
        have := hE1 ⟨2 ^ j, by
          calc 2 ^ j < 2 ^ 9 := Nat.pow_lt_pow_right Nat.one_lt_two hj9
            _ = 512 := by norm_num⟩
        simp only [eAct] at this
        rw [evalE_two_pow hj9, List.getD_eq_getElem _ _ hj] at this
        rw [this]
        interval_cases j <;> rfl
    have hker := ker_of_mem hσ hu hbid
    have hk : ∃ k, σ ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := h.isPGroup_SG ⟨x, hx⟩
      have hxk : x ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hX1 : (⟨x, hxX⟩ : normalizer (Jh : Set G)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hxk)
      exact ⟨k, by rw [hσdef, ← map_pow, hX1, map_one]⟩
    obtain ⟨k, hk⟩ := hk
    have hσ1 : σ = 1 := by
      rcases hker with h0 | h0 | h0
      · exact tupleOf_injective hσ.1 (one_mem (Gq u)).1 (h0.trans tupleOf_one.symm)
      · exact eq_one_of_cube hσ hk (by rw [h0]; exact omT_order.1)
      · exact eq_one_of_cube hσ hk (by rw [h0]; exact om2T_order)
    have hxK : x ∈ h.Kk := ⟨⟨x, hxX⟩, MonoidHom.mem_ker.2 hσ1, rfl⟩
    exact (h.mem_Kk_iff_of_mem_SG hx).1 hxK
  refine mem_normalizer_of_conj_le fun y hy => ?_
  have hyS : g * y * g⁻¹ ∈ h.SG := (mem_normalizer_iff.1 hg y).1 (h.Jh_le_SG hy)
  refine hC _ hyS fun e he => ?_
  have he' := hEconj (inv_mem hg) e he
  rw [inv_inv] at he'
  have hc := h.central _ he' y hy
  calc g * y * g⁻¹ * e * (g * y * g⁻¹)⁻¹ = g * (y * (g⁻¹ * e * g)) * y⁻¹ * g⁻¹ := by group
    _ = g * ((g⁻¹ * e * g) * y) * y⁻¹ * g⁻¹ := by rw [hc]
    _ = e := by group

theorem SG_maximal : ∀ P : Subgroup G, IsPGroup 2 P → h.SG ≤ P → P = h.SG := by
  intro P hP hSP
  by_contra hne
  obtain ⟨n, hnP, hnN, hnS⟩ := exists_mem_normalizer_not_mem_of_lt hP
    (lt_of_le_of_ne hSP (Ne.symm hne))
  have hnX : n ∈ normalizer (Jh : Set G) := by
    cases u
    · exact h.normalizer_le_L rfl hnN
    · exact h.normalizer_le_U rfl hnN
  have hQ := h.SG_max (Q := h.SG ⊔ zpowers n)
    (hP.to_le (sup_le hSP (zpowers_le.2 hnP))) le_sup_left
    (sup_le h.SG_le_X (zpowers_le.2 hnX))
  exact hnS (hQ ▸ mem_sup_right (mem_zpowers n))

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
