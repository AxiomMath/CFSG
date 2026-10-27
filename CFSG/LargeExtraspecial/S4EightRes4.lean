module

public import CFSG.LargeExtraspecial.S4EightRes3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_mem_trans {A : Submodule (ZMod 2) V} {u v w : V} (h₁ : u + v ∈ A)
    (h₂ : v + w ∈ A) : u + w ∈ A := by
  have := A.add_mem h₁ h₂
  rwa [add_assoc, ← add_assoc v v w, vec_add_self, zero_add] at this

theorem apply_add_mem_span {a : V} {g : V ≃ₗ[ZMod 2] V} (hga : g a = a) {u v : V}
    (h : u + v ∈ (ZMod 2) ∙ a) : g u + g v ∈ (ZMod 2) ∙ a := by
  rw [← map_add]
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
  rw [← hr, map_smul, hga]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)

theorem apply_mem_span_iff {a : V} {g : V ≃ₗ[ZMod 2] V} (hga : g a = a) {v : V} :
    g v ∈ (ZMod 2) ∙ a ↔ v ∈ (ZMod 2) ∙ a := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
    have : v = r • a := by
      apply g.injective
      rw [map_smul, hga, hr]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  · intro h
    have := apply_add_mem_span hga (u := v) (v := 0) (by rwa [add_zero])
    rwa [map_zero, add_zero] at this

variable [FiniteDimensional (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem mem_spPointRadical_of_add_mem (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {a d₁ d₂ : V} (ha : a ≠ 0) (hd₁ : β a d₁ = 0)
    (hd₂ : β a d₂ = 0) (h₁ : d₁ ∉ (ZMod 2) ∙ a) (h₂ : d₂ ∉ (ZMod 2) ∙ a)
    (h₁₂ : d₁ + d₂ ∉ (ZMod 2) ∙ a) {m : V ≃ₗ[ZMod 2] V}
    (hI : m ∈ TauCeti.BilinForm.isometryGroup β) (hma : m a = a)
    (hm₁ : m d₁ + d₁ ∈ (ZMod 2) ∙ a) (hm₂ : m d₂ + d₂ ∈ (ZMod 2) ∙ a) :
    m ∈ spPointRadical β a := by
  have hI' := TauCeti.BilinForm.mem_isometryGroup_iff.mp hI
  have hD : ∀ u v : V, m (u + v) + (u + v) = (m u + u) + (m v + v) := fun u v => by
    rw [map_add, add_add_add_comm]
  have hDA : ∀ w ∈ (ZMod 2) ∙ a, m w + w = 0 := by
    intro w hw
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hma, vec_add_self]
  have hcong : ∀ v c : V, v + c ∈ (ZMod 2) ∙ a → m v + v = m c + c := by
    intro v c h
    have := hD v c
    rw [hDA _ h] at this
    exact (eq_neg_of_add_eq_zero_left this.symm).trans (vec_neg _)
  refine ⟨hI, hma, fun x hx => ?_, fun v => ?_⟩
  · rw [vec_sub]
    rcases perp_cases hβ hnd h4 ha hd₁ hd₂ h₁ h₂ h₁₂ hx with h | h | h | h
    · rw [hDA x h]
      exact Submodule.zero_mem _
    · rw [hcong x d₁ h]
      exact hm₁
    · rw [hcong x d₂ h]
      exact hm₂
    · rw [add_assoc] at h
      rw [hcong x _ h, hD]
      exact Submodule.add_mem _ hm₁ hm₂
  · have := hI' a v
    rw [hma] at this
    rw [map_sub, this, sub_self]

theorem eq_one_of_odd_of_apply_eq (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {a : V} (ha : a ≠ 0) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEU : E ≤ spPointRadical β a) (hidx : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E)
    (hτ : spTransvection β hβ a ∉ E) {d₁ : V} (hd₁ : β a d₁ = 0) (hd₁n : d₁ ∉ (ZMod 2) ∙ a)
    (he₁ : spRho hβ hd₁ 0 ∈ E) {h : V ≃ₗ[ZMod 2] V}
    (hI : h ∈ TauCeti.BilinForm.isometryGroup β) (hha : h a = a)
    (hN : h ∈ normalizer (E : Set (V ≃ₗ[ZMod 2] V))) {n : ℕ} (hn : Odd n) (hhn : h ^ n = 1) :
    h = 1 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  have hI' := TauCeti.BilinForm.mem_isometryGroup_iff.mp hI
  set A := (ZMod 2) ∙ a with hA
  have hperp : ∀ v, β a v = 0 → β a (h v) = 0 := fun v hv => by
    have := hI' a v
    rw [hha] at this
    rw [this, hv]
  have hconj : ∀ {d : V} (hd : β a d = 0) (l : ZMod 2), spRho hβ hd l ∈ E →
      spRho hβ (hperp d hd) l ∈ E := by
    intro d hd l he
    have h1 := conj_spRho hβ hd l hI (by rw [hI', hd] : β (h a) (h d) = 0)
    rw [spRho_congr hβ _ (hperp d hd) hha rfl rfl] at h1
    rw [← h1]
    exact (mem_normalizer_iff.mp hN _).mp he
  set x := h d₁ with hxdef
  set y := h x with hydef
  have hx : β a x = 0 := hperp d₁ hd₁
  have hy : β a y = 0 := hperp x hx
  have hex : spRho hβ hx 0 ∈ E := hconj hd₁ 0 he₁
  have hey : spRho hβ hy 0 ∈ E := hconj hx 0 hex
  have hxn : x ∉ A := fun hm => hd₁n ((apply_mem_span_iff hha).mp hm)
  have hyn : y ∉ A := fun hm => hxn ((apply_mem_span_iff hha).mp hm)
  have step1 : y + d₁ ∈ A := by
    by_contra hne
    have h1x : d₁ + x ∉ A := by
      intro hm
      have := add_mem_trans hm (apply_add_mem_span hha hm)
      exact hne (by rwa [add_comm] at this)
    have hxy : x + y ∉ A := fun hm =>
      h1x ((apply_mem_span_iff hha).mp (by rwa [map_add]))
    have hβ1 : β d₁ x = 1 := beta_eq_one_of_not_mem_span hβ hnd h4 ha hd₁n hxn h1x hd₁ hx
    have h3 : y + d₁ + x ∈ A := by
      rcases perp_cases hβ hnd h4 ha hd₁ hx hd₁n hxn h1x hy with h' | h' | h' | h'
      · exact absurd h' hyn
      · exact absurd h' hne
      · exact absurd (by rwa [add_comm] at h') hxy
      · exact h'
    have hd1x : β a (d₁ + x) = 0 := by rw [map_add, hd₁, hx, add_zero]
    have hdd : β a (d₁ + x + y) = 0 := by rw [map_add, hd1x, hy, add_zero]
    have hm1 := spRho_mul hβ hd₁ hx 0 0 hd1x
    have hm2 := spRho_mul hβ hd1x hy (0 + 0 + β d₁ x) 0 hdd
    have hmem : spRho hβ hdd (0 + 0 + β d₁ x + 0 + β (d₁ + x) y) ∈ E := by
      rw [← hm2, ← hm1]
      exact mul_mem (mul_mem he₁ hex) hey
    have hA3 : d₁ + x + y ∈ A := by
      rw [show d₁ + x + y = y + d₁ + x by abel]
      exact h3
    have hβy : β (d₁ + x) y = 0 := by
      have e : y = (y + d₁ + x) + (d₁ + x) := by
        rw [add_assoc y d₁ x, add_assoc, vec_add_self, add_zero]
      rw [e, map_add, hβ.self_eq_zero, add_zero]
      rcases mem_span_singleton_iff.mp h3 with h0 | h0
      · rw [h0, map_zero]
      · rw [h0, isAlt_symm hβ, hd1x]
    have hl : 0 + 0 + β d₁ x + 0 + β (d₁ + x) y = 1 := by
      rw [hβ1, hβy]
      decide
    rw [spRho_congr hβ hdd hdd rfl rfl hl, spRho_eq_of_mem_span hβ hdd 1 hA3,
      spRho_zero_one] at hmem
    exact hτ hmem
  obtain ⟨hsq, -⟩ := mul_self_and_comm_E hβ hnd ha hEU
  have h4E := four_le_card_E hβ hnd h4 ha hidx
  obtain ⟨e₂, he₂, h2, h12⟩ := exists_ne_one_ne (E := E) (by omega) (spRho hβ hd₁ 0)
  obtain ⟨d₂, hd₂, l₂, rfl⟩ := exists_eq_spRho hβ hnd ha (hEU he₂)
  have hd₂n := not_mem_span_of_spRho_mem hβ hd₂ hτ he₂ h2
  have hd12 : β a (d₁ + d₂) = 0 := by rw [map_add, hd₁, hd₂, add_zero]
  have h12n : d₁ + d₂ ∉ A := by
    have hmul := spRho_mul hβ hd₁ hd₂ 0 l₂ hd12
    refine not_mem_span_of_spRho_mem hβ hd12 hτ (hmul ▸ mul_mem he₁ he₂) ?_
    rw [← hmul]
    intro hp
    exact h12 ((eq_inv_of_mul_eq_one_right hp).trans
      (inv_eq_of_mul_eq_one_right (hsq _ he₁)))
  set k := h * h with hk
  have hkI : k ∈ TauCeti.BilinForm.isometryGroup β := mul_mem hI hI
  have hka : k a = a := by rw [hk, LinearEquiv.mul_apply, hha, hha]
  have hk1 : k d₁ + d₁ ∈ A := step1
  have hkperp : β a (k d₂) = 0 := hperp _ (hperp d₂ hd₂)
  have hkd₂n : k d₂ ∉ A := fun hm => hd₂n ((apply_mem_span_iff hka).mp hm)
  have hka' : k⁻¹ a = a := by
    conv_lhs => rw [← hka]
    exact k.symm_apply_apply a
  have hkd₂d₁ : k d₂ + d₁ ∉ A := by
    intro hm
    have e1 := apply_add_mem_span hka' hm
    rw [show k⁻¹ (k d₂) = d₂ from k.symm_apply_apply d₂] at e1
    have e2 := apply_add_mem_span hka' hk1
    rw [show k⁻¹ (k d₁) = d₁ from k.symm_apply_apply d₁] at e2
    have := add_mem_trans e1 (by rwa [add_comm] at e2)
    exact h12n (by rwa [add_comm] at this)
  have hkk2 : k (k d₂) + d₂ ∈ A := by
    rcases perp_cases hβ hnd h4 ha hd₁ hd₂ hd₁n hd₂n h12n hkperp with h' | h' | h' | h'
    · exact absurd h' hkd₂n
    · exact absurd h' hkd₂d₁
    · exact add_mem_trans (apply_add_mem_span hka h') h'
    · rw [add_assoc] at h'
      have e1 := apply_add_mem_span hka h'
      have iden : (k d₁ + d₁) + (k d₂ + (d₁ + d₂)) = k (d₁ + d₂) + d₂ := by
        rw [map_add, show (k d₁ + d₁) + (k d₂ + (d₁ + d₂)) = k d₁ + k d₂ + d₂ + (d₁ + d₁) by
          abel, vec_add_self, add_zero]
      have e2 : k (d₁ + d₂) + d₂ ∈ A := by
        rw [← iden]
        exact A.add_mem hk1 h'
      exact add_mem_trans e1 e2
  have hkk1 : k (k d₁) + d₁ ∈ A := add_mem_trans (apply_add_mem_span hka hk1) hk1
  have hm := mem_spPointRadical_of_add_mem hβ hnd h4 ha hd₁ hd₂ hd₁n hd₂n h12n
    (mul_mem hkI hkI) (by rw [LinearEquiv.mul_apply, hka, hka]) hkk1 hkk2
  have := isElementaryAbelian_spPointRadical hβ hnd ha
  have h8 : h ^ 8 = 1 := by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := spPointRadical β a) _ hm
    rw [hk] at this
    calc h ^ 8 = (h ^ 2 * h ^ 2) ^ 2 := by rw [← pow_add, ← pow_mul]
      _ = ((h * h) * (h * h)) ^ 2 := by rw [pow_two h]
      _ = 1 := this
  have hdvd8 := orderOf_dvd_of_pow_eq_one h8
  have hcop : Nat.Coprime (orderOf h) n := by
    have h2n : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
    have : Nat.Coprime (2 ^ 3) n := Nat.Coprime.pow_left 3 h2n
    exact Nat.Coprime.coprime_dvd_left hdvd8 this
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hhn))

omit [FiniteDimensional (ZMod 2) V] in
theorem false_of_card_eq_nine [Finite V] (hV : Nat.card V = 16)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : Nat.card P = 9) {a : V} (ha : a ≠ 0)
    (hfree : ∀ f ∈ P, ∀ v : V, v ≠ 0 → f v = v → f = 1) : False := by
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  obtain ⟨y, hy0, hy⟩ : ∃ y : V, y ≠ 0 ∧ ∀ f ∈ P, f a ≠ y := by
    by_contra h
    push Not at h
    let φ : Option P → V := fun o => o.elim 0 fun f => (f : V ≃ₗ[ZMod 2] V) a
    have hφ : Function.Surjective φ := by
      intro v
      by_cases hv : v = 0
      · exact ⟨none, hv.symm⟩
      · obtain ⟨f, hf, hfv⟩ := h v hv
        exact ⟨some ⟨f, hf⟩, hfv⟩
    have := Nat.card_le_card_of_surjective φ hφ
    rw [Finite.card_option, hP, hV] at this
    omega
  have key : ∀ (f f' : P) (v : V), v ≠ 0 →
      (f : V ≃ₗ[ZMod 2] V) v = (f' : V ≃ₗ[ZMod 2] V) v → f = f' := by
    intro f f' v hv h
    have h1 := hfree ((f' : V ≃ₗ[ZMod 2] V)⁻¹ * f) (mul_mem (inv_mem f'.2) f.2) v hv (by
      rw [LinearEquiv.mul_apply, h]
      exact (f' : V ≃ₗ[ZMod 2] V).symm_apply_apply v)
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hne : ∀ f f' : P, (f : V ≃ₗ[ZMod 2] V) a ≠ (f' : V ≃ₗ[ZMod 2] V) y := by
    intro f f' h
    apply hy ((f' : V ≃ₗ[ZMod 2] V)⁻¹ * f) (mul_mem (inv_mem f'.2) f.2)
    rw [LinearEquiv.mul_apply, h]
    exact (f' : V ≃ₗ[ZMod 2] V).symm_apply_apply y
  have hza : ∀ f : P, (f : V ≃ₗ[ZMod 2] V) a ≠ 0 := fun f h0 =>
    ha ((f : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h0)
  have hzy : ∀ f : P, (f : V ≃ₗ[ZMod 2] V) y ≠ 0 := fun f h0 =>
    hy0 ((f : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h0)
  let ψ : Option (P ⊕ P) → V := fun o => o.elim 0 fun s =>
    Sum.elim (fun f : P => (f : V ≃ₗ[ZMod 2] V) a) (fun f : P => (f : V ≃ₗ[ZMod 2] V) y) s
  have hψ : Function.Injective ψ := by
    rintro (_ | (f | f)) (_ | (f' | f')) h <;>
      simp only [ψ, Option.elim_none, Option.elim_some, Sum.elim_inl, Sum.elim_inr] at h
    · rfl
    · exact absurd h.symm (hza f')
    · exact absurd h.symm (hzy f')
    · exact absurd h (hza f)
    · rw [key f f' a ha h]
    · exact absurd h (hne f f')
    · exact absurd h (hzy f)
    · exact absurd h.symm (hne f' f)
    · rw [key f f' y hy0 h]
  have := Nat.card_le_card_of_injective ψ hψ
  rw [Finite.card_option, Nat.card_sum, hP, hV] at this
  omega

end CFSG.LargeExtraspecial.S4
