module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourLin

public section

namespace CFSG.CGT.PushingUpLit.CGT6

section Frame

variable {K V : Type*} [Group K] [Group V]

structure NatQ (θ : K →* MulAut V) (Y : Subgroup K) (m : ℕ) : Prop where
  triv : ∀ e ∈ Subgroup.centralizer (Y : Set K), Nat.Coprime (orderOf e) m →
    ∀ v : V, θ e v * v⁻¹ ∈ fixQ θ Y
  fpf : ∀ e ∈ Subgroup.centralizer (Y : Set K), ∀ y ∈ Y, y ≠ 1 → Odd (orderOf y) →
    Nat.Coprime (orderOf y) m → ∀ v : V, θ (e * y) v * v⁻¹ ∈ fixQ θ Y → v ∈ fixQ θ Y

theorem exists_mul_mem_of_fpf [Finite V] (hc : ∀ a b : V, a * b = b * a) (σ : MulAut V)
    (C : Subgroup V) (h : ∀ v : V, σ v * v⁻¹ ∈ C → v ∈ C) :
    ∀ v : V, ∃ w : V, (σ w * w⁻¹)⁻¹ * v ∈ C := by
  classical
  have hN : C.Normal := ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
  let κ : V →* V ⧸ C := (QuotientGroup.mk' C).comp (autPhi hc σ)
  have hker : κ.ker ≤ C := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv
    exact h v ((QuotientGroup.eq_one_iff _).mp hv)
  have h1 : Nat.card (V ⧸ κ.ker) = Nat.card κ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange κ).toEquiv
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup κ.ker
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have h4 : Nat.card κ.ker ≤ Nat.card C := Subgroup.card_le_of_le hker
  have h5 : Nat.card (V ⧸ C) ≤ Nat.card (V ⧸ κ.ker) := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < Nat.card κ.ker := Nat.card_pos
    have hpos' : 0 < Nat.card C := Nat.card_pos
    have : Nat.card (V ⧸ κ.ker) * Nat.card κ.ker < Nat.card (V ⧸ C) * Nat.card C :=
      calc Nat.card (V ⧸ κ.ker) * Nat.card κ.ker < Nat.card (V ⧸ C) * Nat.card κ.ker :=
            Nat.mul_lt_mul_of_pos_right hlt hpos
        _ ≤ Nat.card (V ⧸ C) * Nat.card C := Nat.mul_le_mul_left _ h4
    omega
  have h6 : Nat.card κ.range ≤ Nat.card (V ⧸ C) := Nat.card_le_card_of_injective _ Subtype.val_injective
  have hrange : κ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    omega
  intro v
  have hv : QuotientGroup.mk v ∈ κ.range := hrange ▸ Subgroup.mem_top _
  obtain ⟨w, hw⟩ := hv
  refine ⟨w, ?_⟩
  exact QuotientGroup.eq.mp hw

theorem frame_false [Finite V] (hc : ∀ a b : V, a * b = b * a) {θ : K →* MulAut V}
    (hθ : Function.Injective θ) {m : ℕ} {Y₁ Y₃ : Subgroup K} (h₁ : NatQ θ Y₁ m)
    (h₃ : NatQ θ Y₃ m) {d y y₃ : K} (hd : d ∈ Subgroup.centralizer (Y₃ : Set K))
    (hdo : Nat.Coprime (orderOf d) m) (hy : y ∈ Y₁) (hy1 : y ≠ 1) (hyo : Odd (orderOf y))
    (hyc : Nat.Coprime (orderOf y) m) (hdy : d * y⁻¹ ∈ Subgroup.centralizer (Y₁ : Set K))
    (hy₃ : y₃ ∈ Y₃) (hy₃1 : y₃ ≠ 1) (hy₃o : Odd (orderOf y₃))
    (hy₃c : Nat.Coprime (orderOf y₃) m)
    (hyy₃ : y * y₃⁻¹ ∈ Subgroup.centralizer (Y₃ : Set K)) : False := by
  have hA : ∀ v : V, θ d v * v⁻¹ ∈ fixQ θ Y₃ := h₃.triv d hd hdo
  have hB : ∀ v : V, θ d v * v⁻¹ ∈ fixQ θ Y₁ → v ∈ fixQ θ Y₁ := by
    have := h₁.fpf (d * y⁻¹) hdy y hy hy1 hyo hyc
    rwa [inv_mul_cancel_right] at this
  have hC : ∀ v : V, ∃ c₁ ∈ fixQ θ Y₁, ∃ c₃ ∈ fixQ θ Y₃, v = c₁ * c₃ := by
    intro v
    obtain ⟨w, hw⟩ := exists_mul_mem_of_fpf hc (θ d) (fixQ θ Y₁) hB v
    refine ⟨(θ d w * w⁻¹)⁻¹ * v, hw, θ d w * w⁻¹, hA w, ?_⟩
    rw [mul_assoc, hc v, ← mul_assoc, inv_mul_cancel, one_mul]
  have hynorm : ∀ g ∈ Y₃, y⁻¹ * g * y ∈ Y₃ := by
    intro g hg
    have he := Subgroup.mem_centralizer_iff.mp hyy₃ g hg
    have hu : (y * y₃⁻¹)⁻¹ * g * (y * y₃⁻¹) = g := by
      rw [mul_assoc, he, ← mul_assoc, inv_mul_cancel, one_mul]
    have hy' : y⁻¹ * g * y = y₃⁻¹ * ((y * y₃⁻¹)⁻¹ * g * (y * y₃⁻¹)) * y₃ := by group
    rw [hy', hu]
    exact Y₃.mul_mem (Y₃.mul_mem (Y₃.inv_mem hy₃) hg) hy₃
  have hyC₃ : ∀ c ∈ fixQ θ Y₃, θ y c ∈ fixQ θ Y₃ := by
    intro c hc₃
    rw [mem_fixQ] at hc₃ ⊢
    intro g hg
    have h1 : θ (y⁻¹ * g * y) c = c := hc₃ _ (hynorm g hg)
    have e1 : g * y = y * (y⁻¹ * g * y) := by group
    calc θ g (θ y c) = θ (g * y) c := by rw [map_mul, MulAut.mul_apply]
      _ = θ (y * (y⁻¹ * g * y)) c := by rw [e1]
      _ = θ y (θ (y⁻¹ * g * y) c) := by rw [map_mul, MulAut.mul_apply]
      _ = θ y c := by rw [h1]
  have hE : ∀ v : V, θ y v * v⁻¹ ∈ fixQ θ Y₃ := by
    intro v
    obtain ⟨c₁, hc₁, c₃, hc₃, rfl⟩ := hC v
    have hfix : θ y c₁ = c₁ := mem_fixQ.mp hc₁ y hy
    rw [map_mul, hfix]
    let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
    have : c₁ * θ y c₃ * (c₁ * c₃)⁻¹ = θ y c₃ * c₃⁻¹ := by
      rw [mul_inv_rev]
      calc c₁ * θ y c₃ * (c₃⁻¹ * c₁⁻¹) = (c₁ * c₁⁻¹) * (θ y c₃ * c₃⁻¹) := by ac_rfl
        _ = θ y c₃ * c₃⁻¹ := by rw [mul_inv_cancel, one_mul]
    rw [this]
    exact (fixQ θ Y₃).mul_mem (hyC₃ c₃ hc₃) ((fixQ θ Y₃).inv_mem hc₃)
  have hF : ∀ v : V, v ∈ fixQ θ Y₃ := by
    intro v
    have := h₃.fpf (y * y₃⁻¹) hyy₃ y₃ hy₃ hy₃1 hy₃o hy₃c v
    rw [inv_mul_cancel_right] at this
    exact this (hE v)
  apply hy₃1
  apply hθ
  ext v
  rw [map_one, MulAut.one_apply]
  exact mem_fixQ.mp (hF v) y₃ hy₃

end Frame

end CFSG.CGT.PushingUpLit.CGT6
