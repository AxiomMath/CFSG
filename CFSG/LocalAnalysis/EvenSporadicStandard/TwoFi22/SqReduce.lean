module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.SqSylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

variable {G : Type*} [Group G]

@[expose] def SqStatement (S : Set G) (δ : G) : Prop :=
  (∀ w : G, w * w ≠ δ) ∧
    ∀ x : G, x * δ = δ * x → x * x = 1 → x ≠ 1 → x ≠ δ → x ∉ S → δ * x ∉ S →
      ∃ w : G, w * δ = δ * w ∧ w * w = x

theorem SqStatement.of_conj {S : Set G} (hS : ∀ c x : G, c * x * c⁻¹ ∈ S ↔ x ∈ S) {δ : G}
    (g : G) (h : SqStatement S (g * δ * g⁻¹)) : SqStatement S δ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun w hw => h1 (g * w * g⁻¹) ?_, fun x hxδ hx2 hx1 hxδ' hxS hδxS => ?_⟩
  · calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = g * δ * g⁻¹ := by rw [hw]
  · have hc1 : g * x * g⁻¹ * (g * δ * g⁻¹) = g * δ * g⁻¹ * (g * x * g⁻¹) := by
      calc g * x * g⁻¹ * (g * δ * g⁻¹) = g * (x * δ) * g⁻¹ := by group
        _ = g * (δ * x) * g⁻¹ := by rw [hxδ]
        _ = g * δ * g⁻¹ * (g * x * g⁻¹) := by group
    have hc2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
      calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have hc3 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (conj_eq_one_iff.1 h)
    have hc4 : g * x * g⁻¹ ≠ g * δ * g⁻¹ := fun h =>
      hxδ' (mul_left_cancel (mul_right_cancel h))
    have hc5 : g * x * g⁻¹ ∉ S := fun h => hxS ((hS g x).1 h)
    have hc6 : g * δ * g⁻¹ * (g * x * g⁻¹) ∉ S := by
      intro h
      apply hδxS
      refine (hS g (δ * x)).1 ?_
      rw [show g * (δ * x) * g⁻¹ = g * δ * g⁻¹ * (g * x * g⁻¹) by group]
      exact h
    obtain ⟨w, hw1, hw2⟩ := h2 (g * x * g⁻¹) hc1 hc2 hc3 hc4 hc5 hc6
    refine ⟨g⁻¹ * w * g, ?_, ?_⟩
    · calc g⁻¹ * w * g * δ = g⁻¹ * (w * (g * δ * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * δ * g⁻¹) * w) * g := by rw [hw1]
        _ = δ * (g⁻¹ * w * g) := by group
    · calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hw2]
        _ = x := by group

theorem sqStatement_of_sylow [Finite G] {S : Set G} (hS : ∀ c x : G, c * x * c⁻¹ ∈ S ↔ x ∈ S)
    {δ : G} (hδ : δ * δ = 1) {T : Subgroup G} (hTδ : ∀ g ∈ T, g * δ = δ * g) {e m : ℕ}
    (hT : Nat.card T = 2 ^ e) (hN : Nat.card (Subgroup.centralizer {δ}) = 2 ^ e * m)
    (hm : ¬ 2 ∣ m) (hC : ∀ g ∈ T, g * g ≠ δ)
    (hD : ∀ g ∈ T, g * g = 1 → g ≠ 1 → g ≠ δ → g ∉ S → δ * g ∉ S →
      ∃ w : G, w * δ = δ * w ∧ w * w = g) : SqStatement S δ := by
  have hTN : T ≤ Subgroup.centralizer {δ} := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hTδ g hg)
  refine ⟨fun w hw => ?_, fun x hxδ hx2 hx1 hxδ' hxS hδxS => ?_⟩
  · have hwN : w ∈ Subgroup.centralizer {δ} :=
      Subgroup.mem_centralizer_singleton_iff.2 (by rw [← hw]; exact (mul_assoc w w w).symm)
    have h4 : w ^ 2 ^ 2 = 1 := by
      calc w ^ 2 ^ 2 = (w * w) * (w * w) := by
            rw [show (2 : ℕ) ^ 2 = 4 from rfl]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = δ * δ := by rw [hw]
        _ = 1 := hδ
    obtain ⟨c, hcN, hcT⟩ := exists_conj_mem_of_card hTN hT hN hm hwN ⟨2, h4⟩
    have hcδ : c * δ * c⁻¹ = δ := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hcN, mul_inv_cancel_right]
    refine hC _ hcT ?_
    calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = δ := by rw [hw, hcδ]
  · have hxN : x ∈ Subgroup.centralizer {δ} := Subgroup.mem_centralizer_singleton_iff.2 hxδ
    have hx1' : x ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hx2
    obtain ⟨c, hcN, hcT⟩ := exists_conj_mem_of_card hTN hT hN hm hxN ⟨1, hx1'⟩
    have hcδ : c * δ = δ * c := Subgroup.mem_centralizer_singleton_iff.1 hcN
    have hcδ' : c * δ * c⁻¹ = δ := by rw [hcδ, mul_inv_cancel_right]
    have hcδ2 : c⁻¹ * δ = δ * c⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.1 (inv_mem hcN)
    have hd1 : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
      calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have hd2 : c * x * c⁻¹ ≠ 1 := fun h => hx1 (conj_eq_one_iff.1 h)
    have hd3 : c * x * c⁻¹ ≠ δ := by
      intro h
      rw [← hcδ'] at h
      exact hxδ' (mul_left_cancel (mul_right_cancel h))
    have hd4 : c * x * c⁻¹ ∉ S := fun h => hxS ((hS c x).1 h)
    have hd5 : δ * (c * x * c⁻¹) ∉ S := by
      intro h
      apply hδxS
      refine (hS c (δ * x)).1 ?_
      rw [show c * (δ * x) * c⁻¹ = c * δ * c⁻¹ * (c * x * c⁻¹) by group, hcδ']
      exact h
    obtain ⟨w0, hw01, hw02⟩ := hD (c * x * c⁻¹) hcT hd1 hd2 hd3 hd4 hd5
    refine ⟨c⁻¹ * w0 * c, ?_, ?_⟩
    · calc c⁻¹ * w0 * c * δ = c⁻¹ * w0 * (c * δ) := by rw [mul_assoc]
        _ = c⁻¹ * w0 * (δ * c) := by rw [hcδ]
        _ = c⁻¹ * (w0 * δ) * c := by group
        _ = c⁻¹ * (δ * w0) * c := by rw [hw01]
        _ = (c⁻¹ * δ) * w0 * c := by group
        _ = (δ * c⁻¹) * w0 * c := by rw [hcδ2]
        _ = δ * (c⁻¹ * w0 * c) := by group
    · calc c⁻¹ * w0 * c * (c⁻¹ * w0 * c) = c⁻¹ * (w0 * w0) * c := by group
        _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [hw02]
        _ = x := by group

end CFSG.EvenSporadicStandard.TwoFi22
