module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseWr
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseCnt

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

variable {D : Type*} [Group D]

@[expose] def wrY (X : Set D) : Set (D ≀ᵣ Z2) :=
  {y | (∃ a ∈ X, ∃ b ∈ X, y = wr a b 1) ∨ ∃ h : D, y = wr h h⁻¹ z2}

theorem wrY_natCard_param {S α : Type*} (F : S → α) (hF : Function.Injective F)
    (p : α → Prop) (h : ∀ a, p a ↔ ∃ s, F s = a) : Nat.card {a // p a} = Nat.card S :=
  Nat.card_congr ((Equiv.subtypeEquivRight fun a => (h a).trans Set.mem_range.symm).trans
    (Equiv.ofInjective F hF).symm)

omit [Group D] in
theorem wrY_card_pairs (X : Set D) (c c' : D → D → D) (h1 : ∀ h k, c' h (c h k) = k)
    (h2 : ∀ h x, c h (c' h x) = x) :
    Nat.card {hk : D × D // c hk.1 hk.2 ∈ X} = Nat.card D * Nat.card X := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun hk => (hk.1.1, ⟨c hk.1.1 hk.1.2, hk.2⟩)
      invFun := fun p => ⟨(p.1, c' p.1 p.2.1), by simp [h2]⟩
      left_inv := fun hk => by simp [h1]
      right_inv := fun p => by simp [h2] }

section Key

variable {X : Set D} {g : D}

theorem wrY_mem_swap_A (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ d : D, d * x * d⁻¹ ∈ X)
    (hg2 : g * g = 1) (hgc : ∀ d : D, d * g = g * d) {h k : D} (hx : g * (k * h⁻¹) ∈ X) :
    g * (k⁻¹ * h) ∈ X := by
  have hy := hXc _ hx h⁻¹
  have e1 : h⁻¹ * (g * (k * h⁻¹)) * h⁻¹⁻¹ = g * (h⁻¹ * k) := by
    rw [inv_inv]
    calc h⁻¹ * (g * (k * h⁻¹)) * h = (h⁻¹ * g) * (k * h⁻¹) * h := by group
      _ = (g * h⁻¹) * (k * h⁻¹) * h := by rw [hgc]
      _ = g * (h⁻¹ * k) := by group
  rw [e1] at hy
  have hy2 := hX2 _ hy
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have e2 : g * (k⁻¹ * h) = (g * (h⁻¹ * k))⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, hginv, ← mul_assoc, hgc, mul_assoc]
  rw [e2, inv_eq_of_mul_eq_one_right hy2]
  exact hy

theorem wrY_mem_swap_B (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ d : D, d * x * d⁻¹ ∈ X)
    (hg2 : g * g = 1) (hgc : ∀ d : D, d * g = g * d) {h k : D} (hx : g * (h⁻¹ * k) ∈ X) :
    g * (h * k⁻¹) ∈ X := by
  simpa using wrY_mem_swap_A hX2 hXc hg2 hgc (h := k⁻¹) (k := h⁻¹) (by simpa using hx)

end Key

section Param

variable (X : Set D) (g : D)

abbrev WrYTriX : Type _ :=
  {t : D × D × D // t.1 ∈ X ∧ t.2.1 ∈ X ∧ t.2.2 ∈ X ∧ t.1 * t.2.1 * t.2.2 = g}

abbrev WrYPrA : Type _ := {hk : D × D // g * (hk.2 * hk.1⁻¹) ∈ X}

abbrev WrYPrB : Type _ := {hk : D × D // g * (hk.1⁻¹ * hk.2) ∈ X}

def wrYParam : (WrYTriX X g × WrYTriX X g) ⊕ (WrYPrA X g ⊕ (WrYPrB X g ⊕ WrYPrA X g)) →
    (D ≀ᵣ Z2) × (D ≀ᵣ Z2) × (D ≀ᵣ Z2)
  | .inl (⟨(a₀, a₁, a₂), _⟩, ⟨(b₀, b₁, b₂), _⟩) => (wr a₀ b₀ 1, wr a₁ b₁ 1, wr a₂ b₂ 1)
  | .inr (.inl ⟨(h, k), _⟩) =>
      (wr (g * (k * h⁻¹)) (g * (k⁻¹ * h)) 1, wr h h⁻¹ z2, wr k k⁻¹ z2)
  | .inr (.inr (.inl ⟨(h, k), _⟩)) =>
      (wr h h⁻¹ z2, wr (g * (h * k⁻¹)) (g * (h⁻¹ * k)) 1, wr k k⁻¹ z2)
  | .inr (.inr (.inr ⟨(h, k), _⟩)) =>
      (wr h h⁻¹ z2, wr k k⁻¹ z2, wr (g * (k * h⁻¹)) (g * (k⁻¹ * h)) 1)

variable {X g}

theorem wrYParam_prop (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ d : D, d * x * d⁻¹ ∈ X)
    (hg2 : g * g = 1) (hgc : ∀ d : D, d * g = g * d)
    (s : (WrYTriX X g × WrYTriX X g) ⊕ (WrYPrA X g ⊕ (WrYPrB X g ⊕ WrYPrA X g))) :
    (wrYParam X g s).1 ∈ wrY X ∧ (wrYParam X g s).2.1 ∈ wrY X ∧ (wrYParam X g s).2.2 ∈ wrY X ∧
      (wrYParam X g s).1 * (wrYParam X g s).2.1 * (wrYParam X g s).2.2 = diag g := by
  rcases s with ⟨⟨⟨a₀, a₁, a₂⟩, ha₀, ha₁, ha₂, ha⟩, ⟨⟨b₀, b₁, b₂⟩, hb₀, hb₁, hb₂, hb⟩⟩ |
    ⟨⟨h, k⟩, hx⟩ | ⟨⟨h, k⟩, hx⟩ | ⟨⟨h, k⟩, hx⟩
  · refine ⟨Or.inl ⟨a₀, ha₀, b₀, hb₀, rfl⟩, Or.inl ⟨a₁, ha₁, b₁, hb₁, rfl⟩,
      Or.inl ⟨a₂, ha₂, b₂, hb₂, rfl⟩, ?_⟩
    simp only [wrYParam, wr_mul_one, diag_eq_wr] at ha hb ⊢
    rw [ha, hb]
  · have hv := wrY_mem_swap_A hX2 hXc hg2 hgc hx
    refine ⟨Or.inl ⟨_, hx, _, hv, rfl⟩, Or.inr ⟨h, rfl⟩, Or.inr ⟨k, rfl⟩, ?_⟩
    simp only [wrYParam, wr_mul_one, wr_mul_z2, z2_mul_self, diag_eq_wr, wr_inj, and_true]
    exact ⟨by group, by group⟩
  · have hu := wrY_mem_swap_B hX2 hXc hg2 hgc hx
    have hcen : ∀ d y : D, d * (g * y) = g * (d * y) := fun d y => by
      rw [← mul_assoc, hgc, mul_assoc]
    refine ⟨Or.inr ⟨h, rfl⟩, Or.inl ⟨_, hu, _, hx, rfl⟩, Or.inr ⟨k, rfl⟩, ?_⟩
    simp only [wrYParam, wr_mul_z2, mul_one, z2_mul_self, diag_eq_wr, wr_inj, and_true]
    exact ⟨by rw [hcen]; group, by rw [hcen]; group⟩
  · have hv := wrY_mem_swap_A hX2 hXc hg2 hgc hx
    have hcen : ∀ d y : D, d * (g * y) = g * (d * y) := fun d y => by
      rw [← mul_assoc, hgc, mul_assoc]
    refine ⟨Or.inr ⟨h, rfl⟩, Or.inr ⟨k, rfl⟩, Or.inl ⟨_, hx, _, hv, rfl⟩, ?_⟩
    simp only [wrYParam, wr_mul_one, wr_mul_z2, z2_mul_self, diag_eq_wr, wr_inj, and_true]
    exact ⟨by simp only [mul_assoc, hcen]; group, by simp only [mul_assoc, hcen]; group⟩

theorem wrYParam_surj (hgc : ∀ d : D, d * g = g * d)
    (t : (D ≀ᵣ Z2) × (D ≀ᵣ Z2) × (D ≀ᵣ Z2)) (h0 : t.1 ∈ wrY X) (h1 : t.2.1 ∈ wrY X)
    (h2 : t.2.2 ∈ wrY X) (hp : t.1 * t.2.1 * t.2.2 = diag g) : ∃ s, wrYParam X g s = t := by
  obtain ⟨t₀, t₁, t₂⟩ := t
  simp only at h0 h1 h2 hp
  rw [diag_eq_wr] at hp
  rcases h0 with ⟨a₀, ha₀, b₀, hb₀, rfl⟩ | ⟨h₀, rfl⟩ <;>
  rcases h1 with ⟨a₁, ha₁, b₁, hb₁, rfl⟩ | ⟨h₁, rfl⟩ <;>
  rcases h2 with ⟨a₂, ha₂, b₂, hb₂, rfl⟩ | ⟨h₂, rfl⟩
  · simp only [wr_mul_one, wr_inj, and_true] at hp
    exact ⟨.inl (⟨(a₀, a₁, a₂), ha₀, ha₁, ha₂, hp.1⟩, ⟨(b₀, b₁, b₂), hb₀, hb₁, hb₂, hp.2⟩),
      rfl⟩
  · simp only [wr_mul_one, wr_inj] at hp
    exact absurd hp.2.2 z2_ne_one
  · simp only [wr_mul_one, wr_mul_z2, mul_one, wr_inj] at hp
    exact absurd hp.2.2 z2_ne_one
  · simp only [wr_mul_one, wr_mul_z2, z2_mul_self, wr_inj, and_true] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have ea : a₀ = g * (h₂ * h₁⁻¹) := by
      calc a₀ = a₀ * h₁ * h₂⁻¹ * (h₂ * h₁⁻¹) := by group
        _ = g * (h₂ * h₁⁻¹) := by rw [hp1]
    have eb : b₀ = g * (h₂⁻¹ * h₁) := by
      calc b₀ = b₀ * h₁⁻¹ * h₂ * (h₂⁻¹ * h₁) := by group
        _ = g * (h₂⁻¹ * h₁) := by rw [hp2]
    subst ea eb
    exact ⟨.inr (.inl ⟨(h₁, h₂), ha₀⟩), rfl⟩
  · simp only [wr_mul_z2, mul_one, wr_inj] at hp
    exact absurd hp.2.2 z2_ne_one
  · simp only [wr_mul_z2, mul_one, z2_mul_self, wr_inj, and_true] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have eb : b₁ = g * (h₀⁻¹ * h₂) := by
      calc b₁ = h₀⁻¹ * (h₀ * b₁ * h₂⁻¹) * h₂ := by group
        _ = h₀⁻¹ * g * h₂ := by rw [hp1]
        _ = g * (h₀⁻¹ * h₂) := by rw [hgc h₀⁻¹, mul_assoc]
    have ea : a₁ = g * (h₀ * h₂⁻¹) := by
      calc a₁ = h₀ * (h₀⁻¹ * a₁ * h₂) * h₂⁻¹ := by group
        _ = h₀ * g * h₂⁻¹ := by rw [hp2]
        _ = g * (h₀ * h₂⁻¹) := by rw [hgc h₀, mul_assoc]
    subst ea eb
    exact ⟨.inr (.inr (.inl ⟨(h₀, h₂), hb₁⟩)), rfl⟩
  · simp only [wr_mul_one, wr_mul_z2, z2_mul_self, wr_inj, and_true] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have ea : a₂ = g * (h₁ * h₀⁻¹) := by
      calc a₂ = h₁ * h₀⁻¹ * (h₀ * h₁⁻¹ * a₂) := by group
        _ = h₁ * h₀⁻¹ * g := by rw [hp1]
        _ = g * (h₁ * h₀⁻¹) := hgc _
    have eb : b₂ = g * (h₁⁻¹ * h₀) := by
      calc b₂ = h₁⁻¹ * h₀ * (h₀⁻¹ * h₁ * b₂) := by group
        _ = h₁⁻¹ * h₀ * g := by rw [hp2]
        _ = g * (h₁⁻¹ * h₀) := hgc _
    subst ea eb
    exact ⟨.inr (.inr (.inr ⟨(h₀, h₁), ha₂⟩)), rfl⟩
  · simp only [wr_mul_one, wr_mul_z2, z2_mul_self, wr_inj] at hp
    exact absurd hp.2.2 z2_ne_one

theorem wrYParam_injective : Function.Injective (wrYParam X g) := by
  rintro (⟨⟨⟨a₀, a₁, a₂⟩, ha⟩, ⟨⟨b₀, b₁, b₂⟩, hb⟩⟩ | ⟨⟨h, k⟩, hx⟩ | ⟨⟨h, k⟩, hx⟩ |
    ⟨⟨h, k⟩, hx⟩) (⟨⟨⟨a₀', a₁', a₂'⟩, ha'⟩, ⟨⟨b₀', b₁', b₂'⟩, hb'⟩⟩ | ⟨⟨h', k'⟩, hx'⟩ |
    ⟨⟨h', k'⟩, hx'⟩ | ⟨⟨h', k'⟩, hx'⟩) heq <;>
  simp [wrYParam, wr_inj, z2_ne_one, z2_ne_one.symm] at heq
  · obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩ := heq
    rfl
  · obtain ⟨-, rfl, rfl⟩ := heq
    rfl
  · obtain ⟨rfl, -, rfl⟩ := heq
    rfl
  · obtain ⟨rfl, rfl, -⟩ := heq
    rfl

theorem card_wrYPrA : Nat.card (WrYPrA X g) = Nat.card D * Nat.card X :=
  wrY_card_pairs X (fun h k => g * (k * h⁻¹)) (fun h x => g⁻¹ * x * h)
    (fun h k => by group) (fun h x => by group)

theorem card_wrYPrB : Nat.card (WrYPrB X g) = Nat.card D * Nat.card X :=
  wrY_card_pairs X (fun h k => g * (h⁻¹ * k)) (fun h x => h * (g⁻¹ * x))
    (fun h k => by group) (fun h x => by group)

end Param

theorem prodCnt_wrY [Finite D] (X : Set D) (hX2 : ∀ x ∈ X, x * x = 1)
    (hXc : ∀ x ∈ X, ∀ d : D, d * x * d⁻¹ ∈ X) (g : D) (hg2 : g * g = 1)
    (hgc : ∀ d : D, d * g = g * d) :
    prodCnt (wrY X) (diag g) = prodCnt X g ^ 2 + 3 * (Nat.card D * Nat.card X) := by
  have h1 : prodCnt (wrY X) (diag g) =
      Nat.card ((WrYTriX X g × WrYTriX X g) ⊕ (WrYPrA X g ⊕ (WrYPrB X g ⊕ WrYPrA X g))) :=
    wrY_natCard_param (wrYParam X g) wrYParam_injective _ fun t =>
      ⟨fun ⟨h0, h1, h2, hp⟩ => wrYParam_surj hgc t h0 h1 h2 hp,
        fun ⟨s, hs⟩ => hs ▸ wrYParam_prop hX2 hXc hg2 hgc s⟩
  have h2 : prodCnt X g = Nat.card (WrYTriX X g) := rfl
  rw [h1, h2, Nat.card_sum, Nat.card_prod, Nat.card_sum, Nat.card_sum, card_wrYPrA, card_wrYPrB]
  ring

end CFSG.OddStandard.AltStdSec.SylowSn
