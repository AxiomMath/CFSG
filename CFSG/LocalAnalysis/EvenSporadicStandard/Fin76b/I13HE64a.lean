module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Aut

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

namespace I13HE64

variable {Γ : Type*} [Group Γ]

theorem card_sup_zpowers_le [Finite Γ] (H : Subgroup Γ) (g : Γ) (hn : ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hsq : g * g ∈ H) : Nat.card ↥(H ⊔ zpowers g) ≤ 2 * Nat.card H := by
  have hK : H ⊔ zpowers g = closure ((H : Set Γ) ∪ {g}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
  have hpred : ∀ b ∈ H ⊔ zpowers g, b ∈ H ∨ b * g⁻¹ ∈ H := by
    intro b hb
    rw [hK] at hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact Or.inl hx
      · rw [Set.mem_singleton_iff.1 hx, mul_inv_cancel]
        exact Or.inr H.one_mem
    | one => exact Or.inl H.one_mem
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (mul_mem hx hy)
      · rw [mul_assoc]; exact Or.inr (mul_mem hx hy)
      · refine Or.inr ?_
        have e : x * y * g⁻¹ = (x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [e]; exact mul_mem hx (hn y hy)
      · refine Or.inl ?_
        have e : x * y = (x * g⁻¹) * (g * (y * g⁻¹) * g⁻¹) * (g * g) := by group
        rw [e]; exact mul_mem (mul_mem hx (hn _ hy)) hsq
    | inv x _ hx =>
      rcases hx with hx | hx
      · exact Or.inl (inv_mem hx)
      · refine Or.inr ?_
        have e : x⁻¹ * g⁻¹ = ((g * (x * g⁻¹) * g⁻¹) * (g * g))⁻¹ := by group
        rw [e]; exact inv_mem (mul_mem (hn _ hx) hsq)
  have hdvd : H.relIndex (H ⊔ zpowers g) ∣ 2 := by
    refine Subgroup.relIndex_dvd_two_iff.2 ⟨g⁻¹, inv_mem (mem_sup_right (mem_zpowers g)),
      fun b hb => ?_⟩
    exact (hpred b hb).symm
  have hle : H.relIndex (H ⊔ zpowers g) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := H ⊔ zpowers g)
  rw [inf_eq_left.2 le_sup_left] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ hle

theorem card_zpowers_le [Finite Γ] {a : Γ} (ha : a * a = 1) : Nat.card ↥(zpowers a) ≤ 2 := by
  rw [Nat.card_zpowers]
  by_cases h1 : a = 1
  · rw [h1, orderOf_one]; norm_num
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [orderOf_eq_prime (by rw [pow_two]; exact ha) h1]

theorem card_closure_le_of_list [Finite Γ] (W : Subgroup Γ) {a : Γ} (haW : a ∈ W)
    (ha2 : a * a = 1) (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ zpowers a)
    (hsq : ∀ x ∈ W, x * x ∈ zpowers a) :
    ∀ l : List Γ, (∀ x ∈ l, x ∈ W) →
      Nat.card ↥(closure ({a} ∪ {x | x ∈ l})) ≤ 2 * 2 ^ l.length := by
  intro l
  induction l with
  | nil =>
    intro _
    have : closure ({a} ∪ {x | x ∈ ([] : List Γ)}) = zpowers a := by
      simp [zpowers_eq_closure]
    rw [this]
    simpa using card_zpowers_le ha2
  | cons x l ih =>
    intro hl
    have hxW : x ∈ W := hl x (by simp)
    have hlW : ∀ y ∈ l, y ∈ W := fun y hy => hl y (by simp [hy])
    set H : Subgroup Γ := closure ({a} ∪ {y | y ∈ l}) with hH
    have hHW : H ≤ W := by
      rw [hH, closure_le]
      rintro y (hy | hy)
      · rw [Set.mem_singleton_iff.1 hy]; exact haW
      · exact hlW y hy
    have haH : zpowers a ≤ H := by
      rw [zpowers_le]
      exact subset_closure (Or.inl rfl)
    have hsplit : closure ({a} ∪ {y | y ∈ x :: l}) = H ⊔ zpowers x := by
      have : ({a} ∪ {y | y ∈ x :: l} : Set Γ) = ({a} ∪ {y | y ∈ l}) ∪ {x} := by
        ext y
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons]
        tauto
      rw [this, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
    rw [hsplit]
    have h1 := card_sup_zpowers_le H x (fun h hh => by
      have e : x * h * x⁻¹ = (x * h * x⁻¹ * h⁻¹) * h := by group
      rw [e]
      exact mul_mem (haH (hcomm x hxW h (hHW hh))) hh) (haH (hsq x hxW))
    calc Nat.card ↥(H ⊔ zpowers x) ≤ 2 * Nat.card H := h1
      _ ≤ 2 * (2 * 2 ^ l.length) := Nat.mul_le_mul_left _ (ih hlW)
      _ = 2 * 2 ^ (x :: l).length := by rw [List.length_cons, pow_succ]; ring

theorem conj_mem_closure {S : Set Γ} (b : Γ) (hS : ∀ s ∈ S, b * s * b⁻¹ ∈ closure S) :
    ∀ p ∈ closure S, b * p * b⁻¹ ∈ closure S := by
  intro p hp
  induction hp using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
    rw [e]; exact mul_mem hx hy
  | inv x _ hx =>
    have e : b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hx

theorem sq_eq_one_of_mem_sup {H K : Subgroup Γ} (hHK : K ≤ centralizer (H : Set Γ))
    (hH : ∀ h ∈ H, h * h = 1) (hK : ∀ k ∈ K, k * k = 1) : ∀ x ∈ H ⊔ K, x * x = 1 := by
  intro x hx
  obtain ⟨h, hh, k, hk, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hHK hx
  have hc : k * h = h * k := (mem_centralizer_iff.1 (hHK hk) h hh).symm
  calc h * k * (h * k) = h * (k * h) * k := by group
    _ = h * (h * k) * k := by rw [hc]
    _ = (h * h) * (k * k) := by group
    _ = 1 := by rw [hH h hh, hK k hk, one_mul]

end I13HE64

end CFSG.EvenSporadicStandard.Fin76b
