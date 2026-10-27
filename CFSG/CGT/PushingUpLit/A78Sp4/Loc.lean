module

public import CFSG.CGT.PushingUpLit.A78Sp4.Data
public import CFSG.CGT.PushingUpLit.A78Sp4.Act

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_coords {F : Type} [Field F] [CharP F 2] {J : Subgroup G} (r s t w : G → F)
    (hmul : ∀ x ∈ J, ∀ y ∈ J, r (x * y) = r x + r y ∧ s (x * y) = s x + s y ∧
      t (x * y) = t x + t y + r x * s y ∧ w (x * y) = w x + w y + r x ^ 2 * s y)
    {x y : G} (hx : x ∈ J) (hy : y ∈ J) :
    r ⁅x, y⁆ = 0 ∧ s ⁅x, y⁆ = 0 ∧ t ⁅x, y⁆ = r x * s y + r y * s x ∧
      w ⁅x, y⁆ = r x ^ 2 * s y + r y ^ 2 * s x := by
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have hcJ : ⁅x, y⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)
  have hyx : y * x ∈ J := J.mul_mem hy hx
  have e : ⁅x, y⁆ * (y * x) = x * y := by
    simp only [commutatorElement_def]; group
  obtain ⟨hr1, hs1, ht1, hw1⟩ := hmul _ hcJ _ hyx
  obtain ⟨hr2, hs2, ht2, hw2⟩ := hmul x hx y hy
  obtain ⟨hr3, hs3, ht3, hw3⟩ := hmul y hy x hx
  rw [e] at hr1 hs1 ht1 hw1
  have hrc : r ⁅x, y⁆ = 0 := by linear_combination hr2 - hr3 - hr1
  have hsc : s ⁅x, y⁆ = 0 := by linear_combination hs2 - hs3 - hs1
  refine ⟨hrc, hsc, ?_, ?_⟩
  · linear_combination ht2 - ht3 - ht1 - s (y * x) * hrc - (r y * s x) * h2
  · linear_combination hw2 - hw3 - hw1 - (r ⁅x, y⁆ * s (y * x)) * hrc - (r y ^ 2 * s x) * h2

theorem exists_cls2 {F : Type} [Field F] [CharP F 2] {J V V₂ Z Z₂ : Subgroup G}
    (h : Sp4Coords G J V V₂ Z Z₂ F) :
    ∃ c : Cls2Coord F J,
      (∀ x ∈ J, (x ∈ V ↔ (c.π x).2 = 0)) ∧ (∀ x ∈ J, (x ∈ V₂ ↔ (c.π x).1 = 0)) ∧
      (∀ x ∈ J, (x ∈ Z ↔ c.π x = 0 ∧ (c.ζ x).1 = 0)) ∧
      (∀ x ∈ J, (x ∈ Z₂ ↔ c.π x = 0 ∧ (c.ζ x).2 = 0)) := by
  obtain ⟨r, s, t, w, hmul, hinj, hsurj, hV, hV₂, hZ, hZ₂⟩ := h.ex
  refine ⟨⟨fun x => (r x, s x), fun x => (t x, w x), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨h1, h2, _, _⟩ := hmul x hx y hy
    simp [h1, h2]
  · rintro ⟨a, b⟩
    obtain ⟨x, hx, ha, hb, _, _⟩ := hsurj a b 0 0
    exact ⟨x, hx, by simp [ha, hb]⟩
  · intro x hx hx0 y hy hy0
    obtain ⟨_, _, h3, h4⟩ := hmul x hx y hy
    have hrx : r x = 0 := (Prod.ext_iff.1 hx0).1
    simp [h3, h4, hrx]
  · intro x hx hx0 y hy hy0 hζ
    have hrx : r x = 0 := (Prod.ext_iff.1 hx0).1
    have hsx : s x = 0 := (Prod.ext_iff.1 hx0).2
    have hry : r y = 0 := (Prod.ext_iff.1 hy0).1
    have hsy : s y = 0 := (Prod.ext_iff.1 hy0).2
    exact hinj x hx y hy (by rw [hrx, hry]) (by rw [hsx, hsy]) (Prod.ext_iff.1 hζ).1
      (Prod.ext_iff.1 hζ).2
  · rintro ⟨c, d⟩
    obtain ⟨x, hx, ha, hb, hc, hd⟩ := hsurj 0 0 c d
    exact ⟨x, hx, by simp [ha, hb], by simp [hc, hd]⟩
  · intro x hx y hy
    obtain ⟨h1, h2, h3, h4⟩ := comm_coords r s t w hmul hx hy
    exact ⟨by simp [h1, h2], by simp [beta, h3, h4]⟩
  · intro x hx; simpa using hV x hx
  · intro x hx; simpa using hV₂ x hx
  · intro x hx
    rw [hZ x hx]
    simp only [Prod.mk_eq_zero]
    tauto
  · intro x hx
    rw [hZ₂ x hx]
    simp only [Prod.mk_eq_zero]
    tauto

variable {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem Sp4Base.J_le_S (h : Sp4Base G V V₂ J T S M M₂ e) : J ≤ S := h.J_le.trans h.T_le

theorem Sp4Base.conj_J (h : Sp4Base G V V₂ J T S M M₂ e) {s : G} (hs : s ∈ S) {x : G}
    (hx : x ∈ J) : s * x * s⁻¹ ∈ J := by
  have hxS : x ∈ S := h.J_le_S hx
  have := h.normal_J.conj_mem ⟨x, hxS⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨s, hs⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem Sp4Base.faithful (h : Sp4Base G V V₂ J T S M M₂ e) {F : Type} [Field F]
    (c : Cls2Coord F J) (hV : ∀ x ∈ J, (x ∈ V ↔ (c.π x).2 = 0))
    (hV₂ : ∀ x ∈ J, (x ∈ V₂ ↔ (c.π x).1 = 0)) {s : G} (hs : s ∈ S) (hsJ : s ∉ J) :
    ∃ y ∈ J, c.π ⁅s, y⁆ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hsJ
  refine h.cent_S s hs fun j hj => ?_
  have hcJ : ⁅s, j⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem (h.conj_J hs hj) (J.inv_mem hj)
  have h0 := hcon j hj
  refine ⟨(hV _ hcJ).2 (by rw [h0]; rfl), (hV₂ _ hcJ).2 (by rw [h0]; rfl)⟩

theorem mul_mem_cj' (g : G) {H : Subgroup G} {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ cj g H :=
  Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem Sp4Base.wdiag (h : Sp4Base G V V₂ J T S M M₂ e) {F : Type} [Field F] (c : Cls2Coord F J)
    (hV : ∀ x ∈ J, (x ∈ V ↔ (c.π x).2 = 0)) (hV₂ : ∀ x ∈ J, (x ∈ V₂ ↔ (c.π x).1 = 0))
    {s : G} (hsT : s ∈ T) : WDiag c s := by
  have hs : s ∈ S := h.T_le hsT
  obtain ⟨h1, h2⟩ := h.T_norm s hsT
  intro x hx
  have hxJ := h.conj_J hs hx
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have : s * x * s⁻¹ ∈ V := h1 ▸ mul_mem_cj' s ((hV x hx).2 h0)
    exact (hV _ hxJ).1 this
  · have : s * x * s⁻¹ ∈ V₂ := h2 ▸ mul_mem_cj' s ((hV₂ x hx).2 h0)
    exact (hV₂ _ hxJ).1 this

theorem Sp4Base.wswap (h : Sp4Base G V V₂ J T S M M₂ e) {F : Type} [Field F] (c : Cls2Coord F J)
    (hV : ∀ x ∈ J, (x ∈ V ↔ (c.π x).2 = 0)) (hV₂ : ∀ x ∈ J, (x ∈ V₂ ↔ (c.π x).1 = 0))
    {s : G} (hs : s ∈ S) (hsT : s ∉ T) : WSwap c s := by
  obtain ⟨h1, h2⟩ := h.swap s hs hsT
  intro x hx
  have hxJ := h.conj_J hs hx
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have : s * x * s⁻¹ ∈ V₂ := h1 ▸ mul_mem_cj' s ((hV x hx).2 h0)
    exact (hV₂ _ hxJ).1 this
  · have : s * x * s⁻¹ ∈ V := h2 ▸ mul_mem_cj' s ((hV₂ x hx).2 h0)
    exact (hV _ hxJ).1 this

end CFSG.CGT.PushingUpLit.A78Sp4
