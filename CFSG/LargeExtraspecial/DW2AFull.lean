module

public import CFSG.LargeExtraspecial.DW2AClosed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Transvections

variable {T : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {c : V}

theorem exists_fix_move (hTc : ∀ t ∈ T, t c = c)
    (hTW : ∀ t ∈ T, ∀ w ∈ W, t w = w ∨ t w = w + c) {u s : V} (hu : u ∈ W) (hs : s ∈ W)
    (hu' : u ∉ fixIn T W) (hs' : s ∉ fixIn T W) (hus : u + s ∉ fixIn T W) :
    ∃ t ∈ T, t u = u ∧ t s = s + c := by
  have hmove : ∀ {w : V}, w ∈ W → w ∉ fixIn T W → ∃ t ∈ T, t w = w + c := by
    intro w hw hw'
    rw [mem_fixIn] at hw'
    push Not at hw'
    obtain ⟨t, ht, htw⟩ := hw' hw
    exact ⟨t, ht, (hTW t ht w hw).resolve_left htw⟩
  have hcomp : ∀ t ∈ T, ∀ t' ∈ T, ∀ w : V, t' w = w + c → (t * t') w = t w + c := by
    intro t ht t' _ w h
    rw [LinearEquiv.mul_apply, h, map_add, hTc t ht]
  obtain ⟨t₁, ht₁, ht₁u⟩ := hmove hu hu'
  obtain ⟨t₂, ht₂, ht₂s⟩ := hmove hs hs'
  obtain ⟨t₃, ht₃, ht₃us⟩ := hmove (W.add_mem hu hs) hus
  have hcc : ∀ w : V, w + c + c = w := fun w => by rw [add_assoc, add_self_zmod2, add_zero]
  rcases hTW t₂ ht₂ u hu with h2u | h2u
  · exact ⟨t₂, ht₂, h2u, ht₂s⟩
  rcases hTW t₁ ht₁ s hs with h1s | h1s
  · refine ⟨t₁ * t₂, T.mul_mem ht₁ ht₂, ?_, ?_⟩
    · rw [hcomp t₁ ht₁ t₂ ht₂ u h2u, ht₁u, hcc]
    · rw [hcomp t₁ ht₁ t₂ ht₂ s ht₂s, h1s]
  rcases hTW t₃ ht₃ u hu with h3u | h3u
  · refine ⟨t₃, ht₃, h3u, ?_⟩
    rw [map_add, h3u] at ht₃us
    exact add_left_cancel (ht₃us.trans (by abel))
  · refine ⟨t₃ * t₂, T.mul_mem ht₃ ht₂, ?_, ?_⟩
    · rw [hcomp t₃ ht₃ t₂ ht₂ u h2u, h3u, hcc]
    · have h3s : t₃ s = s := by
        rw [map_add, h3u] at ht₃us
        exact add_left_cancel (ht₃us.trans (by abel))
      rw [hcomp t₃ ht₃ t₂ ht₂ s ht₂s, h3s]

theorem exists_eq_add_smul_of_dual [FiniteDimensional (ZMod 2) V] (hc : c ≠ 0)
    (hTc : ∀ t ∈ T, t c = c) (hTW : ∀ t ∈ T, ∀ w ∈ W, t w - w ∈ ZMod 2 ∙ c)
    (φ : Module.Dual (ZMod 2) W) (hφ : ∀ w : W, (w : V) ∈ fixIn T W → φ w = 0) :
    ∃ t ∈ T, ∀ w : W, t w = w + φ w • c := by
  classical
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hc
  have hcoef : ∀ t ∈ T, ∀ w ∈ W, t w - w = ψ (t w - w) • c := by
    intro t ht w hw
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (hTW t ht w hw)
    rw [← hμ, map_smul, hψ, smul_eq_mul, mul_one]
  let φ' : T → Module.Dual (ZMod 2) W := fun t =>
    ψ ∘ₗ (((t : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) ∘ₗ W.subtype
  have hφ' : ∀ (t : T) (w : W), φ' t w = ψ ((t : V ≃ₗ[ZMod 2] V) w - w) := fun _ _ => rfl
  have hmul : ∀ s t : T, φ' (s * t) = φ' s + φ' t := by
    intro s t
    ext w
    rw [LinearMap.add_apply, hφ', hφ', hφ']
    have e : ((s * t : T) : V ≃ₗ[ZMod 2] V) w - w =
        ((s : V ≃ₗ[ZMod 2] V) ((t : V ≃ₗ[ZMod 2] V) w - w)) + ((s : V ≃ₗ[ZMod 2] V) w - w) := by
      rw [map_sub]
      change (s : V ≃ₗ[ZMod 2] V) ((t : V ≃ₗ[ZMod 2] V) w) - w = _
      abel
    rw [e, hcoef t t.2 w w.2, map_smul, hTc s s.2, ← hcoef t t.2 w w.2, map_add, add_comm]
  set Ψ : Submodule (ZMod 2) (Module.Dual (ZMod 2) W) := Submodule.span (ZMod 2) (Set.range φ')
  have hrange : ∀ χ ∈ Ψ, ∃ t : T, φ' t = χ := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨1, LinearMap.ext fun w => ?_⟩
      rw [hφ']
      simp
    | add x y _ _ hx hy =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hy
      exact ⟨s * t, hmul s t⟩
    | smul a x _ hx =>
      obtain ⟨t, rfl⟩ := hx
      rcases zmod2_cases a with rfl | rfl
      · refine ⟨1, LinearMap.ext fun w => ?_⟩
        rw [hφ', zero_smul]
        simp
      · exact ⟨t, by rw [one_smul]⟩
  have hco : ∀ w : W, w ∈ Ψ.dualCoannihilator ↔ (w : V) ∈ fixIn T W := by
    intro w
    rw [Submodule.mem_dualCoannihilator]
    constructor
    · intro h
      refine ⟨w.2, fun t ht => ?_⟩
      have h0 := h (φ' ⟨t, ht⟩) (Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩)
      rw [hφ'] at h0
      have e := hcoef t ht w w.2
      rw [h0, zero_smul, sub_eq_zero] at e
      exact e
    · intro h χ hχ
      induction hχ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t, rfl⟩ := hx
        rw [hφ', h.2 t t.2, sub_self, map_zero]
      | zero => rfl
      | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
  have hmem : φ ∈ Ψ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Ψ), Submodule.mem_dualAnnihilator]
    intro w hw
    exact hφ w ((hco w).mp hw)
  obtain ⟨t, ht⟩ := hrange φ hmem
  refine ⟨t, t.2, fun w => ?_⟩
  have := hcoef t t.2 w w.2
  rw [← hφ', ht] at this
  rw [← this]
  abel

end Transvections

section Dichotomy

theorem sup_span_inf_sup_span_le {A B : Submodule (ZMod 2) V} {e : V} (he : e ∉ A ⊔ B) :
    (A ⊔ ZMod 2 ∙ e) ⊓ (B ⊔ ZMod 2 ∙ e) ≤ (A ⊓ B) ⊔ ZMod 2 ∙ e := by
  rintro v ⟨hvA, hvB⟩
  obtain ⟨a, ha, f, hf, rfl⟩ := Submodule.mem_sup.mp hvA
  obtain ⟨b, hb, f', hf', hab⟩ := Submodule.mem_sup.mp hvB
  obtain ⟨l₁, rfl⟩ := Submodule.mem_span_singleton.mp hf
  obtain ⟨l₂, rfl⟩ := Submodule.mem_span_singleton.mp hf'
  rcases zmod2_cases l₁ with rfl | rfl <;> rcases zmod2_cases l₂ with rfl | rfl
  · simp only [zero_smul, add_zero] at hab ⊢
    exact Submodule.mem_sup_left ⟨ha, hab ▸ hb⟩
  · exfalso
    apply he
    simp only [zero_smul, add_zero, one_smul] at hab
    have : e = a - b := by rw [← hab]; abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb)
  · exfalso
    apply he
    simp only [zero_smul, add_zero, one_smul] at hab
    have : e = b - a := by rw [hab]; abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_right hb) (Submodule.mem_sup_left ha)
  · simp only [one_smul] at hab ⊢
    have hab' : b = a := add_right_cancel hab
    subst hab'
    exact add_mem (Submodule.mem_sup_left ⟨ha, hb⟩)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self e))

theorem inf_span_singleton_eq_bot {S : Submodule (ZMod 2) V} {c : V} (hc : c ∉ S) :
    S ⊓ ZMod 2 ∙ c = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvS, hv⟩
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rcases zmod2_cases μ with rfl | rfl
  · rw [zero_smul]
    exact zero_mem _
  · rw [one_smul] at hvS
    exact absurd hvS hc

theorem finrank_sup_span_singleton [FiniteDimensional (ZMod 2) V] {S : Submodule (ZMod 2) V}
    {c : V} (hc : c ∉ S) :
    finrank (ZMod 2) (S ⊔ ZMod 2 ∙ c : Submodule (ZMod 2) V) = finrank (ZMod 2) S + 1 := by
  have hc0 : c ≠ 0 := fun h => hc (h ▸ zero_mem _)
  have h := Submodule.finrank_sup_add_finrank_inf_eq S (ZMod 2 ∙ c)
  rw [inf_span_singleton_eq_bot hc, finrank_bot, add_zero, finrank_span_singleton hc0] at h
  exact h

theorem finrank_le_one_or_add_one_ge [FiniteDimensional (ZMod 2) V]
    {U : Submodule (ZMod 2) V} (S : V → Submodule (ZMod 2) V) {s : ℕ}
    (hmem : ∀ c ∈ U, c ≠ 0 → c ∈ S c) (hle : ∀ c ∈ U, c ≠ 0 → S c ≤ U)
    (hdim : ∀ c ∈ U, c ≠ 0 → finrank (ZMod 2) (S c) = s)
    (hsymm : ∀ c ∈ U, ∀ c' ∈ U, c ≠ 0 → c' ≠ 0 → (c' ∈ S c ↔ c ∈ S c'))
    (hax : ∀ c ∈ U, ∀ c' ∈ U, c ≠ 0 → c' ≠ 0 → c' ∉ S c → S c ≤ S c' ⊔ ZMod 2 ∙ c)
    (hlt : s < finrank (ZMod 2) U) :
    s ≤ 1 ∨ finrank (ZMod 2) U ≤ s + 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h2, hk⟩ := hcon
  have hU0 : U ≠ ⊥ := fun h => by rw [h, finrank_bot] at hlt; omega
  obtain ⟨c, hcU, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hSc_lt : S c < U := lt_of_le_of_ne (hle c hcU hc0) fun h => by
    have := hdim c hcU hc0
    rw [h] at this
    omega
  obtain ⟨c', hc'U, hc'S⟩ := IsConcreteLE.exists_of_lt hSc_lt
  have hc'0 : c' ≠ 0 := fun h => hc'S (h ▸ zero_mem _)
  have hcS' : c ∉ S c' := fun h => hc'S ((hsymm c hcU c' hc'U hc0 hc'0).mpr h)
  set H := S c ⊔ ZMod 2 ∙ c' with hH
  have hS'H : S c' ≤ H := hax c' hc'U c hcU hc'0 hc0 hcS'
  have hHdim : finrank (ZMod 2) H = s + 1 := by
    rw [hH, finrank_sup_span_singleton hc'S, hdim c hcU hc0]
  have hsupH : S c ⊔ S c' = H := by
    refine le_antisymm (sup_le le_sup_left hS'H) (sup_le le_sup_left ?_)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.mem_sup_right (hmem c' hc'U hc'0)
  have hinf : finrank (ZMod 2) (S c ⊓ S c' : Submodule (ZMod 2) V) = s - 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (S c) (S c')
    rw [hsupH, hHdim, hdim c hcU hc0, hdim c' hc'U hc'0] at h
    omega
  have hinf0 : S c ⊓ S c' ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hinf
    omega
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf0
  have hdU : d ∈ U := hle c hcU hc0 hd.1
  have hkey : ∀ e ∈ U, e ∉ H → e ∈ S d := by
    intro e heU heH
    have he0 : e ≠ 0 := fun h => heH (h ▸ zero_mem _)
    have he1 : e ∉ S c := fun h => heH (Submodule.mem_sup_left h)
    have he2 : e ∉ S c' := fun h => heH (hS'H h)
    have h1 := hax e heU c hcU he0 hc0 fun h => he1 ((hsymm e heU c hcU he0 hc0).mp h)
    have h2 := hax e heU c' hc'U he0 hc'0 fun h => he2 ((hsymm e heU c' hc'U he0 hc'0).mp h)
    have h3 : S e ≤ (S c ⊓ S c') ⊔ ZMod 2 ∙ e :=
      (le_inf h1 h2).trans (sup_span_inf_sup_span_le (by rwa [hsupH]))
    have h4 : finrank (ZMod 2) ((S c ⊓ S c') ⊔ ZMod 2 ∙ e : Submodule (ZMod 2) V) ≤ s := by
      have := Submodule.finrank_add_le_finrank_add_finrank (S c ⊓ S c') (ZMod 2 ∙ e)
      have h5 := finrank_span_le_card (R := ZMod 2) ({e} : Set V)
      simp only [Set.toFinset_singleton, Finset.card_singleton] at h5
      omega
    have h5 : S e = (S c ⊓ S c') ⊔ ZMod 2 ∙ e :=
      Submodule.eq_of_le_of_finrank_le h3 (by rw [hdim e heU he0]; exact h4)
    have hde : d ∈ S e := h5 ▸ Submodule.mem_sup_left hd
    exact (hsymm e heU d hdU he0 hd0).mp hde
  have hHU : H < U := by
    refine lt_of_le_of_ne (sup_le (hle c hcU hc0) ?_) fun h => ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hc'U
    · rw [h] at hHdim
      omega
  obtain ⟨e₀, he₀U, he₀H⟩ := IsConcreteLE.exists_of_lt hHU
  have hall : U ≤ S d := by
    intro w hw
    by_cases hwH : w ∈ H
    · have h1 : w + e₀ ∈ S d := hkey _ (add_mem hw he₀U) fun h => he₀H (by
        have := sub_mem h hwH
        rwa [add_sub_cancel_left] at this)
      have h2 : e₀ ∈ S d := hkey e₀ he₀U he₀H
      have := sub_mem h1 h2
      rwa [add_sub_cancel_right] at this
    · exact hkey w hw hwH
  have := Submodule.finrank_mono hall
  rw [hdim d hdU hd0] at this
  omega

end Dichotomy

end CFSG.LargeExtraspecial.DW
