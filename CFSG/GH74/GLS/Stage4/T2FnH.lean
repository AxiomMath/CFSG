module

public import CFSG.GH74.GLS.Stage4.T2Norm

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

section Y1

variable {G : Type} [Group G] {z u w₁ w₂ : G} {K₁ K₂ H C₁ : Subgroup G}

theorem t2C_Y1 (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z)
    (hzz : z * z = 1) (hzc : ∀ x ∈ C₁, x * z = z * x) (hKC : K₁ ⊔ K₂ ≤ C₁) (huC : u ∈ C₁)
    (hn₁ : ∀ c ∈ C₁, ∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) (hn₂ : ∀ c ∈ C₁, ∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂)
    (hu2 : u * u = 1) (hw₁K : w₁ ∈ K₁) (hw₂K : w₂ ∈ K₂)
    (hw₁u : w₁ * u * w₁⁻¹ = u * z) (hw₂u : w₂ * u * w₂⁻¹ = u * z)
    (hH₁ : ∀ x ∈ K₁, x ∈ H ↔ x * u = u * x) (hH₂ : ∀ x ∈ K₂, x ∈ H ↔ x * u = u * x)
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (huH : u ∈ H) (hHC : H ≤ C₁)
    (hw₀ : ∀ h ∈ H, (w₁ * w₂) * h * (w₁ * w₂)⁻¹ = h⁻¹)
    (hidx : (K₁ ⊔ K₂).relIndex C₁ = 2) {s₀ : G} (hs₀H : s₀ ∈ H) (hs₀K : s₀ ∉ K₁ ⊔ K₂) :
    ∀ y ∈ C₁, y * u = u * y → y ∈ H ∨ ∃ h ∈ H, y = h * (w₁ * w₂) := by
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have huw : ∀ w : G, w * u * w⁻¹ = u * z → u * w * u = z * w := by
    intro w hw
    have h1 : w * u = u * z * w := by
      calc w * u = (w * u * w⁻¹) * w := by group
        _ = u * z * w := by rw [hw]
    calc u * w * u = u * (w * u) := by group
      _ = u * (u * z * w) := by rw [h1]
      _ = (u * u) * z * w := by group
      _ = z * w := by rw [hu2, one_mul]
  have huw₁ := huw w₁ hw₁u
  have huw₂ := huw w₂ hw₂u
  have hcaseK : ∀ y ∈ K₁ ⊔ K₂, y * u = u * y → y ∈ H ∨ ∃ h ∈ H, y = h * (w₁ * w₂) := by
    intro y hy hyu
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm y).1 hy
    have ha' : u * a * u⁻¹ ∈ K₁ := hn₁ u huC a ha
    have hb' : u * b * u⁻¹ ∈ K₂ := hn₂ u huC b hb
    have hab : (u * a * u⁻¹) * (u * b * u⁻¹) = a * b := by
      calc (u * a * u⁻¹) * (u * b * u⁻¹) = u * (a * b) * u⁻¹ := by group
        _ = a * b := by rw [← hyu]; group
    have hmem : a⁻¹ * (u * a * u⁻¹) ∈ K₁ ⊓ K₂ := by
      refine ⟨K₁.mul_mem (K₁.inv_mem ha) ha', ?_⟩
      have h1 : a⁻¹ * (u * a * u⁻¹) = b * (u * b * u⁻¹)⁻¹ := by
        have hc : (u * a * u⁻¹) * (u * b * u⁻¹) = a * b := hab
        calc a⁻¹ * (u * a * u⁻¹) = a⁻¹ * ((u * a * u⁻¹) * (u * b * u⁻¹)) * (u * b * u⁻¹)⁻¹ := by group
          _ = a⁻¹ * (a * b) * (u * b * u⁻¹)⁻¹ := by rw [hc]
          _ = b * (u * b * u⁻¹)⁻¹ := by group
      rw [h1]
      exact K₂.mul_mem hb (K₂.inv_mem hb')
    rcases t2C_zpowers_cases hzz (hinter hmem) with h0 | h1
    ·
      left
      have h0a : u * a * u⁻¹ = a := by
        calc u * a * u⁻¹ = a * (a⁻¹ * (u * a * u⁻¹)) := by group
          _ = a := by rw [h0, mul_one]
      have h0b : u * b * u⁻¹ = b := by
        have : (u * a * u⁻¹) * (u * b * u⁻¹) = a * b := hab
        rw [h0a] at this
        exact mul_left_cancel this
      have haH : a ∈ H := (hH₁ a ha).2 (by
        calc a * u = (u * a * u⁻¹) * u := by rw [h0a]
          _ = u * a := by group)
      have hbH : b ∈ H := (hH₂ b hb).2 (by
        calc b * u = (u * b * u⁻¹) * u := by rw [h0b]
          _ = u * b := by group)
      exact H.mul_mem haH hbH
    · right
      have h1a : u * a * u⁻¹ = a * z := by
        calc u * a * u⁻¹ = a * (a⁻¹ * (u * a * u⁻¹)) := by group
          _ = a * z := by rw [h1]
      have h1b : u * b * u⁻¹ = z * b := by
        have : (u * a * u⁻¹) * (u * b * u⁻¹) = a * b := hab
        rw [h1a] at this
        have hz : z * (u * b * u⁻¹) = b := by
          have h2 : a * (z * (u * b * u⁻¹)) = a * b := by
            calc a * (z * (u * b * u⁻¹)) = a * z * (u * b * u⁻¹) := by group
              _ = a * b := this
          exact mul_left_cancel h2
        calc u * b * u⁻¹ = z⁻¹ * (z * (u * b * u⁻¹)) := by group
          _ = z * b := by rw [hz, hzinv]
      have hzC₁ := hzc
      have hh₁K : w₁⁻¹ * a ∈ K₁ := K₁.mul_mem (K₁.inv_mem hw₁K) ha
      have hh₂K : w₂⁻¹ * b ∈ K₂ := K₂.mul_mem (K₂.inv_mem hw₂K) hb
      have hzcK₁ : ∀ x ∈ K₁, x * z = z * x := fun x hx => hzc x (hKC (Subgroup.mem_sup_left hx))
      have hzcK₂ : ∀ x ∈ K₂, x * z = z * x := fun x hx => hzc x (hKC (Subgroup.mem_sup_right hx))
      have hh₁ : w₁⁻¹ * a ∈ H := by
        refine (hH₁ _ hh₁K).2 ?_
        have hw₁inv : u * w₁⁻¹ * u⁻¹ = w₁⁻¹ * z := by
          have h2 : u * w₁ * u⁻¹ = z * w₁ := by
            calc u * w₁ * u⁻¹ = u * w₁ * u := by rw [hu1]
              _ = z * w₁ := huw₁
          calc u * w₁⁻¹ * u⁻¹ = (u * w₁ * u⁻¹)⁻¹ := by group
            _ = (z * w₁)⁻¹ := by rw [h2]
            _ = w₁⁻¹ * z := by rw [mul_inv_rev, hzinv]
        have h3 : u * (w₁⁻¹ * a) * u⁻¹ = w₁⁻¹ * a := by
          calc u * (w₁⁻¹ * a) * u⁻¹ = (u * w₁⁻¹ * u⁻¹) * (u * a * u⁻¹) := by group
            _ = (w₁⁻¹ * z) * (a * z) := by rw [hw₁inv, h1a]
            _ = w₁⁻¹ * (z * a) * z := by group
            _ = w₁⁻¹ * (a * z) * z := by rw [← hzcK₁ a ha]
            _ = w₁⁻¹ * a * (z * z) := by group
            _ = w₁⁻¹ * a := by rw [hzz, mul_one]
        calc w₁⁻¹ * a * u = (u * (w₁⁻¹ * a) * u⁻¹) * u := by rw [h3]
          _ = u * (w₁⁻¹ * a) := by group
      have hh₂ : w₂⁻¹ * b ∈ H := by
        refine (hH₂ _ hh₂K).2 ?_
        have hw₂inv : u * w₂⁻¹ * u⁻¹ = w₂⁻¹ * z := by
          have h2 : u * w₂ * u⁻¹ = z * w₂ := by
            calc u * w₂ * u⁻¹ = u * w₂ * u := by rw [hu1]
              _ = z * w₂ := huw₂
          calc u * w₂⁻¹ * u⁻¹ = (u * w₂ * u⁻¹)⁻¹ := by group
            _ = (z * w₂)⁻¹ := by rw [h2]
            _ = w₂⁻¹ * z := by rw [mul_inv_rev, hzinv]
        have h3 : u * (w₂⁻¹ * b) * u⁻¹ = w₂⁻¹ * b := by
          calc u * (w₂⁻¹ * b) * u⁻¹ = (u * w₂⁻¹ * u⁻¹) * (u * b * u⁻¹) := by group
            _ = (w₂⁻¹ * z) * (z * b) := by rw [hw₂inv, h1b]
            _ = w₂⁻¹ * (z * z) * b := by group
            _ = w₂⁻¹ * b := by rw [hzz, mul_one]
        calc w₂⁻¹ * b * u = (u * (w₂⁻¹ * b) * u⁻¹) * u := by rw [h3]
          _ = u * (w₂⁻¹ * b) := by group
      refine ⟨(w₁⁻¹ * a * (w₂⁻¹ * b))⁻¹, H.inv_mem (H.mul_mem hh₁ hh₂), ?_⟩
      have hcw : a * w₂ = w₂ * a := hcomm a ha w₂ hw₂K
      have hcb : (w₁⁻¹ * a) * (w₂⁻¹ * b) = (w₂⁻¹ * b) * (w₁⁻¹ * a) :=
        hcomm _ hh₁K _ hh₂K
      have hinvH : (w₁ * w₂) * (w₁⁻¹ * a * (w₂⁻¹ * b)) * (w₁ * w₂)⁻¹ =
          (w₁⁻¹ * a * (w₂⁻¹ * b))⁻¹ := hw₀ _ (H.mul_mem hh₁ hh₂)
      have hab2 : a * b = (w₁ * w₂) * (w₁⁻¹ * a * (w₂⁻¹ * b)) := by
        have hww : w₁ * w₂ = w₂ * w₁ := hcomm w₁ hw₁K w₂ hw₂K
        calc a * b = w₁ * (w₁⁻¹ * a) * (w₂ * (w₂⁻¹ * b)) := by group
          _ = w₁ * ((w₁⁻¹ * a) * w₂) * (w₂⁻¹ * b) := by group
          _ = w₁ * (w₂ * (w₁⁻¹ * a)) * (w₂⁻¹ * b) := by
              rw [show (w₁⁻¹ * a) * w₂ = w₂ * (w₁⁻¹ * a) from hcomm _ hh₁K w₂ hw₂K]
          _ = (w₁ * w₂) * (w₁⁻¹ * a * (w₂⁻¹ * b)) := by group
      calc a * b = (w₁ * w₂) * (w₁⁻¹ * a * (w₂⁻¹ * b)) := hab2
        _ = ((w₁ * w₂) * (w₁⁻¹ * a * (w₂⁻¹ * b)) * (w₁ * w₂)⁻¹) * (w₁ * w₂) := by group
        _ = (w₁⁻¹ * a * (w₂⁻¹ * b))⁻¹ * (w₁ * w₂) := by rw [hinvH]
  intro y hyC hyu
  by_cases hyK : y ∈ K₁ ⊔ K₂
  · exact hcaseK y hyK hyu
  ·
    have hys : y * s₀⁻¹ ∈ K₁ ⊔ K₂ :=
      t2C_outer_coset hidx hyC (hHC hs₀H) hyK hs₀K
    have hs₀u : s₀ * u = u * s₀ := hHc s₀ hs₀H u huH
    have hs₀u' : s₀⁻¹ * u = u * s₀⁻¹ := by
      have : s₀⁻¹ * (s₀ * u) * s₀⁻¹ = s₀⁻¹ * (u * s₀) * s₀⁻¹ := by rw [hs₀u]
      have h2 : u * s₀⁻¹ = s₀⁻¹ * u := by simpa [mul_assoc] using this
      exact h2.symm
    have hyu' : (y * s₀⁻¹) * u = u * (y * s₀⁻¹) := by
      calc (y * s₀⁻¹) * u = y * (s₀⁻¹ * u) := by group
        _ = y * (u * s₀⁻¹) := by rw [hs₀u']
        _ = (y * u) * s₀⁻¹ := by group
        _ = (u * y) * s₀⁻¹ := by rw [hyu]
        _ = u * (y * s₀⁻¹) := by group
    rcases hcaseK _ hys hyu' with h | ⟨h', hh', hh'e⟩
    · left
      have : y = (y * s₀⁻¹) * s₀ := by group
      rw [this]
      exact H.mul_mem h hs₀H
    · right
      refine ⟨h' * s₀⁻¹, H.mul_mem hh' (H.inv_mem hs₀H), ?_⟩
      have hy' : y = (y * s₀⁻¹) * s₀ := by group
      rw [hy', hh'e]
      have h1 := hw₀ s₀ hs₀H
      calc h' * (w₁ * w₂) * s₀ = h' * (((w₁ * w₂) * s₀ * (w₁ * w₂)⁻¹) * (w₁ * w₂)) := by group
        _ = h' * (s₀⁻¹ * (w₁ * w₂)) := by rw [h1]
        _ = h' * s₀⁻¹ * (w₁ * w₂) := by group

end Y1

section NormH

variable {G : Type} [Group G] [Finite G] {u w₀ f : G} {K₁ K₂ H C₁ : Subgroup G}

theorem t2C_normH
    (hY1 : ∀ y ∈ C₁, y * u = u * y → y ∈ H ∨ ∃ h ∈ H, y = h * w₀)
    (hHC : H ≤ C₁) (huH : u ∈ H) (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hH₁ : ∀ x ∈ K₁, x ∈ H ↔ x * u = u * x) (hH₂ : ∀ x ∈ K₂, x ∈ H ↔ x * u = u * x)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hw₀sq : w₀ * w₀ = 1) (hw₀H : w₀ ∉ H)
    (hidx : ((H ⊓ K₁) ⊔ (H ⊓ K₂)).relIndex H = 2)
    (hfC : ∀ x ∈ C₁, f * x * f⁻¹ ∈ C₁) (hfn₁ : ∀ x ∈ K₁, f * x * f⁻¹ ∈ K₁)
    (hfn₂ : ∀ x ∈ K₂, f * x * f⁻¹ ∈ K₂) (hfu : f * u = u * f) (hfw : f * w₀ = w₀ * f)
    (hfodd : Odd (orderOf f)) : ∀ h ∈ H, f * h * f⁻¹ ∈ H := by
  set H₀ : Subgroup G := (H ⊓ K₁) ⊔ (H ⊓ K₂) with hH₀def
  have hH₀H : H₀ ≤ H := sup_le inf_le_left inf_le_left
  have hcomm' : ∀ x ∈ H ⊓ K₁, ∀ y ∈ H ⊓ K₂, x * y = y * x := fun x hx y hy => hcomm x hx.2 y hy.2
  have hfu' : ∀ x, x * u = u * x → (f * x * f⁻¹) * u = u * (f * x * f⁻¹) := by
    intro x hx
    calc (f * x * f⁻¹) * u = f * x * (f⁻¹ * u) := by group
      _ = f * x * (u * f⁻¹) := by
          have : f⁻¹ * u = u * f⁻¹ := by
            have h1 : f⁻¹ * (f * u) * f⁻¹ = f⁻¹ * (u * f) * f⁻¹ := by rw [hfu]
            have h2 : u * f⁻¹ = f⁻¹ * u := by simpa [mul_assoc] using h1
            exact h2.symm
          rw [this]
      _ = f * (x * u) * f⁻¹ := by group
      _ = f * (u * x) * f⁻¹ := by rw [hx]
      _ = u * (f * x * f⁻¹) := by
          calc f * (u * x) * f⁻¹ = (f * u) * x * f⁻¹ := by group
            _ = (u * f) * x * f⁻¹ := by rw [hfu]
            _ = u * (f * x * f⁻¹) := by group
  have hfH₁ : ∀ x ∈ H ⊓ K₁, f * x * f⁻¹ ∈ H ⊓ K₁ := by
    intro x hx
    have hxK := hfn₁ x hx.2
    have hxu : x * u = u * x := (hH₁ x hx.2).1 hx.1
    exact ⟨(hH₁ _ hxK).2 (hfu' x hxu), hxK⟩
  have hfH₂ : ∀ x ∈ H ⊓ K₂, f * x * f⁻¹ ∈ H ⊓ K₂ := by
    intro x hx
    have hxK := hfn₂ x hx.2
    have hxu : x * u = u * x := (hH₂ x hx.2).1 hx.1
    exact ⟨(hH₂ _ hxK).2 (hfu' x hxu), hxK⟩
  have hfH₀ : ∀ x ∈ H₀, f * x * f⁻¹ ∈ H₀ := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm' x).1 hx
    have e : f * (a * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹) := by group
    rw [e]
    exact H₀.mul_mem (Subgroup.mem_sup_left (hfH₁ a ha)) (Subgroup.mem_sup_right (hfH₂ b hb))
  have hfnorm : f ∈ Subgroup.normalizer (H₀ : Set G) := Subgroup.mem_normalizer_fintype hfH₀
  have hfH₀' : ∀ x ∈ H₀, f⁻¹ * x * f ∈ H₀ := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hfnorm) x).1 hx
    simpa using this
  have hfw' : f⁻¹ * w₀ * f = w₀ := by
    calc f⁻¹ * w₀ * f = f⁻¹ * (w₀ * f) := by group
      _ = f⁻¹ * (f * w₀) := by rw [hfw]
      _ = w₀ := by group
  intro h hhH
  by_cases hh₀ : h ∈ H₀
  · exact hH₀H (hfH₀ h hh₀)
  by_contra hg
  have hgC : f * h * f⁻¹ ∈ C₁ := hfC h (hHC hhH)
  have hgu : (f * h * f⁻¹) * u = u * (f * h * f⁻¹) :=
    hfu' h (hHc h hhH u huH)
  rcases hY1 _ hgC hgu with hgH | ⟨h', hh', hgeq⟩
  · exact hg hgH
  ·
    have hrel : ∀ x ∈ H, x ∉ H₀ → ∀ y ∈ H, y ∉ H₀ → x * y⁻¹ ∈ H₀ :=
      fun x hx hx0 y hy hy0 => t2C_outer_coset hidx hx hy hx0 hy0
    by_cases hh'₀ : h' ∈ H₀
    ·
      apply hw₀H
      have h1 : h = (f⁻¹ * h' * f) * w₀ := by
        calc h = f⁻¹ * (f * h * f⁻¹) * f := by group
          _ = f⁻¹ * (h' * w₀) * f := by rw [hgeq]
          _ = (f⁻¹ * h' * f) * (f⁻¹ * w₀ * f) := by group
          _ = (f⁻¹ * h' * f) * w₀ := by rw [hfw']
      have h2 : w₀ = (f⁻¹ * h' * f)⁻¹ * h := by rw [h1]; group
      rw [h2]
      exact H.mul_mem (H.inv_mem (hH₀H (hfH₀' _ hh'₀))) hhH
    ·
      have hk : h' * h⁻¹ ∈ H₀ := hrel h' hh' hh'₀ h hhH hh₀
      set k : G := h' * h⁻¹ with hkdef
      have hh'e : h' = k * h := by rw [hkdef]; group
      have hfw₀ : f * w₀ * f⁻¹ = w₀ := by
        calc f * w₀ * f⁻¹ = (w₀ * f) * f⁻¹ := by rw [hfw]
          _ = w₀ := by group
      have hfh : f * h * f⁻¹ = k * h * w₀ := by rw [hgeq, hh'e]
      have hstep : ∀ m ∈ H₀, ∃ m' ∈ H₀, f * (f * (h * m) * f⁻¹) * f⁻¹ = h * m' := by
        intro m hm
        have hm₁ := hfH₀ m hm
        have hk₁ := hfH₀ k hk
        have hm₂ := hfH₀ _ hm₁
        refine ⟨(f * k * f⁻¹) * k * (f * (f * m * f⁻¹) * f⁻¹),
          H₀.mul_mem (H₀.mul_mem hk₁ hk) hm₂, ?_⟩
        have e1 : f * (h * m) * f⁻¹ = (k * h * w₀) * (f * m * f⁻¹) := by
          calc f * (h * m) * f⁻¹ = (f * h * f⁻¹) * (f * m * f⁻¹) := by group
            _ = (k * h * w₀) * (f * m * f⁻¹) := by rw [hfh]
        have e2 : f * ((k * h * w₀) * (f * m * f⁻¹)) * f⁻¹ =
            (f * k * f⁻¹) * (f * h * f⁻¹) * (f * w₀ * f⁻¹) * (f * (f * m * f⁻¹) * f⁻¹) := by group
        rw [e1, e2, hfh, hfw₀]
        have hkH : k ∈ H := hH₀H hk
        have h1H : f * k * f⁻¹ ∈ H := hH₀H hk₁
        have h2H : f * (f * m * f⁻¹) * f⁻¹ ∈ H := hH₀H hm₂
        calc (f * k * f⁻¹) * (k * h * w₀) * w₀ * (f * (f * m * f⁻¹) * f⁻¹)
            = (f * k * f⁻¹) * (k * h) * (w₀ * w₀) * (f * (f * m * f⁻¹) * f⁻¹) := by group
          _ = (f * k * f⁻¹) * (k * h) * (f * (f * m * f⁻¹) * f⁻¹) := by rw [hw₀sq, mul_one]
          _ = h * ((f * k * f⁻¹) * k * (f * (f * m * f⁻¹) * f⁻¹)) := by
              have c1 : h * (f * k * f⁻¹) = (f * k * f⁻¹) * h := (hHc _ h1H h hhH).symm
              have c2 : h * k = k * h := (hHc _ hkH h hhH).symm
              calc (f * k * f⁻¹) * (k * h) * (f * (f * m * f⁻¹) * f⁻¹)
                  = (f * k * f⁻¹) * (h * k) * (f * (f * m * f⁻¹) * f⁻¹) := by rw [← c2]
                _ = ((f * k * f⁻¹) * h) * k * (f * (f * m * f⁻¹) * f⁻¹) := by group
                _ = (h * (f * k * f⁻¹)) * k * (f * (f * m * f⁻¹) * f⁻¹) := by rw [c1]
                _ = h * ((f * k * f⁻¹) * k * (f * (f * m * f⁻¹) * f⁻¹)) := by group
      have hiter : ∀ j : ℕ, ∃ m ∈ H₀, (f * f) ^ j * h * ((f * f) ^ j)⁻¹ = h * m := by
        intro j
        induction j with
        | zero => exact ⟨1, H₀.one_mem, by simp⟩
        | succ j ih =>
          obtain ⟨m, hm, hme⟩ := ih
          obtain ⟨m', hm', hme'⟩ := hstep m hm
          refine ⟨m', hm', ?_⟩
          have e : (f * f) ^ (j + 1) * h * ((f * f) ^ (j + 1))⁻¹ =
              f * (f * ((f * f) ^ j * h * ((f * f) ^ j)⁻¹) * f⁻¹) * f⁻¹ := by
            rw [pow_succ']; generalize (f * f) ^ j = w; group
          rw [e, hme, hme']
      obtain ⟨j, hj⟩ := hfodd
      have hfpow : (f * f) ^ (j + 1) = f := by
        have h1 : f ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one f
        calc (f * f) ^ (j + 1) = f ^ (2 * j + 1) * f := by
              rw [← pow_two, ← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ]
          _ = f := by rw [h1, one_mul]
      obtain ⟨m, hm, hme⟩ := hiter (j + 1)
      rw [hfpow] at hme
      apply hg
      rw [hme]
      exact H.mul_mem hhH (hH₀H hm)

omit [Finite G] in
theorem t2C_w0_not_mem {K H : Subgroup G} {w₀ : G} (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hw₀ : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹) (hcyc : IsCyclic ↥(H ⊓ K))
    (hcard : 3 ≤ Nat.card ↥(H ⊓ K)) : w₀ ∉ H := by
  intro hw
  have hsq : ∀ x : ↥(H ⊓ K), x * x = 1 := by
    intro x
    have h1 : w₀ * (x : G) * w₀⁻¹ = (x : G) := by
      rw [hHc w₀ hw (x : G) x.2.1]; group
    have h2 := hw₀ (x : G) x.2.1
    have h3 : (x : G) = (x : G)⁻¹ := h1.symm.trans h2
    apply Subtype.ext
    show (x : G) * (x : G) = 1
    calc (x : G) * (x : G) = (x : G) * (x : G)⁻¹ := by rw [← h3]
      _ = 1 := by group
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcardeq : orderOf g = Nat.card ↥(H ⊓ K) := orderOf_eq_card_of_forall_mem_zpowers hg
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact hsq g
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  omega

end NormH


end CFSG.GH74.GLS.Stage4.Rest
