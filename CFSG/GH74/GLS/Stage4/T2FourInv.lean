module

public import CFSG.GH74.GLS.Stage4.T2FourQ
public import CFSG.GH74.GLS.Stage4.T2FourW

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section Fix

variable {G : Type} [Group G]

theorem t2_card_fixed_eq {Q S : Subgroup G} (hSQ : S ≤ Q) {y : G}
    (hiff : ∀ q ∈ Q, (y * q * y⁻¹ = q ↔ q ∈ S)) :
    Nat.card {q : ↥Q // y * (q : G) * y⁻¹ = (q : G)} = Nat.card ↥S := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun q : {q : ↥Q // y * (q : G) * y⁻¹ = (q : G)} =>
      (⟨(q.1 : G), (hiff _ q.1.2).1 q.2⟩ : ↥S)) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩ hab
    have : a = b := congrArg Subtype.val hab
    subst this
    rfl
  · rintro ⟨s, hs⟩
    exact ⟨⟨⟨s, hSQ hs⟩, (hiff _ (hSQ hs)).2 hs⟩, rfl⟩

theorem t2_card_fixed_conj {Q S : Subgroup G} (hSQ : S ≤ Q) {y c : G}
    (hc : ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hc' : ∀ q ∈ Q, c⁻¹ * q * c ∈ Q)
    (hiff : ∀ q ∈ Q, (y * q * y⁻¹ = q ↔ q ∈ S)) :
    Nat.card {q : ↥Q // (c * y * c⁻¹) * (q : G) * (c * y * c⁻¹)⁻¹ = (q : G)} = Nat.card ↥S := by
  let S' : Subgroup G := S.map (MulAut.conj c).toMonoidHom
  have hS'Q : S' ≤ Q := by
    rintro _ ⟨s, hs, rfl⟩
    exact hc s (hSQ hs)
  have hmem : ∀ q : G, q ∈ S' ↔ c⁻¹ * q * c ∈ S := by
    intro q
    constructor
    · rintro ⟨s, hs, rfl⟩
      have : c⁻¹ * ((MulAut.conj c).toMonoidHom s) * c = s := by
        simp [MulAut.conj_apply]; group
      rw [this]; exact hs
    · intro hq
      refine ⟨c⁻¹ * q * c, hq, ?_⟩
      simp [MulAut.conj_apply]; group
  have h1 : Nat.card {q : ↥Q // (c * y * c⁻¹) * (q : G) * (c * y * c⁻¹)⁻¹ = (q : G)} =
      Nat.card ↥S' := by
    apply t2_card_fixed_eq hS'Q
    intro q hq
    rw [hmem]
    have key : (c * y * c⁻¹) * q * (c * y * c⁻¹)⁻¹ = c * (y * (c⁻¹ * q * c) * y⁻¹) * c⁻¹ := by
      group
    constructor
    · intro h1
      rw [key] at h1
      have h2 : y * (c⁻¹ * q * c) * y⁻¹ = c⁻¹ * q * c := by
        have h3 : c⁻¹ * (c * (y * (c⁻¹ * q * c) * y⁻¹) * c⁻¹) * c = c⁻¹ * q * c := by rw [h1]
        calc y * (c⁻¹ * q * c) * y⁻¹ = c⁻¹ * (c * (y * (c⁻¹ * q * c) * y⁻¹) * c⁻¹) * c := by group
          _ = c⁻¹ * q * c := h3
      exact (hiff _ (hc' q hq)).1 h2
    · intro h1
      have h2 := (hiff _ (hc' q hq)).2 h1
      rw [key, h2]; group
  rw [h1]
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

end Fix

section W₁

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H Q₁ Q₂ : Subgroup G} {w₁ w₂ : G} {k : ℕ}

theorem T2Four.w₁_inv_H₁ (h : T2Four z u K₁ K₂ H w₁ w₂) {x : G} (hx : x ∈ H) (hxK : x ∈ K₁) :
    w₁ * x * w₁⁻¹ = x⁻¹ := by
  have h1 := h.w₀_inv x hx
  have hc : w₂ * x = x * w₂ := (h.K_comm x hxK w₂ h.w₂_mem).symm
  calc w₁ * x * w₁⁻¹ = w₁ * (w₂ * x * w₂⁻¹) * w₁⁻¹ := by rw [hc]; group
    _ = (w₁ * w₂) * x * (w₁ * w₂)⁻¹ := by group
    _ = x⁻¹ := h1

theorem t2Q_w₁_fix (h : T2Four z u K₁ K₂ H w₁ w₂) (hQ₁H : Q₁ ≤ H ⊓ K₁) (hQ₂H : Q₂ ≤ H ⊓ K₂)
    (hk : Odd k) (hQ₁e : ∀ x ∈ Q₁, x ^ k = 1) (hQ₂e : ∀ x ∈ Q₂, x ^ k = 1)
    (hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) :
    (∀ q ∈ Q₁ ⊔ Q₂, (w₁ * q * w₁⁻¹ = q ↔ q ∈ Q₂)) ∧
      (∀ q ∈ Q₁ ⊔ Q₂, (w₁ * q * w₁⁻¹ = q⁻¹ ↔ q ∈ Q₁)) := by
  have hone : ∀ a ∈ Q₁, ∀ b ∈ Q₂, w₁ * (a * b) * w₁⁻¹ = a⁻¹ * b := by
    intro a ha b hb
    have hw₁b : w₁ * b = b * w₁ := h.K_comm w₁ h.w₁_mem b (hQ₂H hb).2
    calc w₁ * (a * b) * w₁⁻¹ = (w₁ * a * w₁⁻¹) * (w₁ * b * w₁⁻¹) := by group
      _ = a⁻¹ * b := by
          rw [h.w₁_inv_H₁ (hQ₁H ha).1 (hQ₁H ha).2, hw₁b]; group
  constructor
  · intro q hq
    constructor
    · intro h1
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcommQ q).1 hq
      rw [hone a ha b hb] at h1
      have h2 : a⁻¹ = a := mul_right_cancel h1
      have h3 : a * a = 1 := by
        have h5 : a * a⁻¹ = 1 := by group
        rwa [h2] at h5
      have ha1 : a = 1 := t2_pow_odd_trivial hk (hQ₁e a ha) h3
      rw [ha1, one_mul]
      exact hb
    · intro hq2
      have hc : w₁ * q = q * w₁ := h.K_comm w₁ h.w₁_mem q (hQ₂H hq2).2
      calc w₁ * q * w₁⁻¹ = q * w₁ * w₁⁻¹ := by rw [hc]
        _ = q := by group
  · intro q hq
    constructor
    · intro h1
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcommQ q).1 hq
      rw [hone a ha b hb] at h1
      have hab : Commute a b := hcommQ a ha b hb
      have h2 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
        rw [mul_inv_rev]; exact hab.inv_inv.eq.symm
      rw [h2] at h1
      have h3 : b = b⁻¹ := mul_left_cancel h1
      have h4 : b * b = 1 := by
        calc b * b = b * b⁻¹ := by rw [← h3]
          _ = 1 := by group
      have hb1 : b = 1 := t2_pow_odd_trivial hk (hQ₂e b hb) h4
      rw [hb1, mul_one]
      exact ha
    · intro hq1
      exact h.w₁_inv_H₁ (hQ₁H hq1).1 (hQ₁H hq1).2

end W₁

section Card

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H Q₁ Q₂ : Subgroup G} {w₁ w₂ a : G} {k : ℕ}

theorem T2Weyl.inv_fix_card (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) {v : G} (hv : v ∈ t2U z u)
    (hy2 : (w₁ * v) * (w₁ * v) = 1) (hya : (w₁ * v) * a * (w₁ * v)⁻¹ = a⁻¹)
    (hQ₁H : Q₁ ≤ H ⊓ K₁) (hQ₂H : Q₂ ≤ H ⊓ K₂) (hk : Odd k)
    (hQ₁c : Nat.card ↥Q₁ = k) (hQ₂c : Nat.card ↥Q₂ = k)
    (hQ₁e : ∀ x ∈ Q₁, x ^ k = 1) (hQ₂e : ∀ x ∈ Q₂, x ^ k = 1)
    (hdec : ∀ x ∈ H, ∃ c ∈ t2U z u, ∃ b ∈ Q₁ ⊔ Q₂, x = c * b)
    {y' : G} (hy' : y' ∈ Subgroup.closure ({a, w₁ * v, w₁ * w₂} : Set G)) (hord : orderOf y' = 2)
    (hne : y' ≠ w₁ * w₂) :
    Nat.card {q : ↥(Q₁ ⊔ Q₂) // y' * (q : G) * y'⁻¹ = (q : G)} = k := by
  have hF := h.four
  have hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
    hF.K_comm x (hQ₁H hx).2 y (hQ₂H hy).2
  have hQH : Q₁ ⊔ Q₂ ≤ H := sup_le (fun x hx => (hQ₁H hx).1) (fun x hx => (hQ₂H hx).1)
  have hUH : t2U z u ≤ H := t2U_le_of_mem hF.zz hF.uu hF.zu_comm hF.z_mem_H hF.u_mem_H
  have hQe := t2Q_exp hcommQ hQ₁e hQ₂e
  have hfix := t2Q_w₁_fix hF hQ₁H hQ₂H hk hQ₁e hQ₂e hcommQ
  obtain ⟨m, l, hl, rfl⟩ := h.involutions hv hy2 hya hy' hord hne
  have hamN : a ^ m ∈ normalizer (H : Set G) := Subgroup.pow_mem _ h.a_normH m
  have hamN' : (a ^ m)⁻¹ ∈ normalizer (H : Set G) := Subgroup.inv_mem _ hamN
  have hc : ∀ q ∈ Q₁ ⊔ Q₂, a ^ m * q * (a ^ m)⁻¹ ∈ Q₁ ⊔ Q₂ := fun q hq =>
    t2Q_normalized hF.zz hF.uu hF.zu_comm hk hF.H_comm hQH hUH hQe hdec
      (fun x hx => (Subgroup.mem_normalizer_iff.1 hamN x).1 hx) q hq
  have hc' : ∀ q ∈ Q₁ ⊔ Q₂, (a ^ m)⁻¹ * q * a ^ m ∈ Q₁ ⊔ Q₂ := by
    intro q hq
    have := t2Q_normalized hF.zz hF.uu hF.zu_comm hk hF.H_comm hQH hUH hQe hdec
      (fun x hx => (Subgroup.mem_normalizer_iff.1 hamN' x).1 hx) q hq
    rwa [inv_inv] at this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with rfl | rfl
  ·
    refine (t2_card_fixed_conj (S := Q₂) (fun x hx => Subgroup.mem_sup_right hx) hc hc' ?_).trans hQ₂c
    intro q hq
    have hvq : v * q = q * v := hF.H_comm v (hUH hv) q (hQH hq)
    have e : ((w₁ * v) * (w₁ * w₂) ^ 0) * q * ((w₁ * v) * (w₁ * w₂) ^ 0)⁻¹ = w₁ * q * w₁⁻¹ := by
      rw [pow_zero, mul_one]
      calc (w₁ * v) * q * (w₁ * v)⁻¹ = w₁ * (v * q * v⁻¹) * w₁⁻¹ := by group
        _ = w₁ * q * w₁⁻¹ := by rw [hvq]; group
    rw [e]
    exact hfix.1 q hq
  ·
    refine (t2_card_fixed_conj (S := Q₁) (fun x hx => Subgroup.mem_sup_left hx) hc hc' ?_).trans hQ₁c
    intro q hq
    have h0 := hF.w₀_inv q (hQH hq)
    have hvq' : v * q⁻¹ = q⁻¹ * v := hF.H_comm v (hUH hv) q⁻¹ (H.inv_mem (hQH hq))
    have e : ((w₁ * v) * (w₁ * w₂) ^ 1) * q * ((w₁ * v) * (w₁ * w₂) ^ 1)⁻¹ =
        (w₁ * q * w₁⁻¹)⁻¹ := by
      rw [pow_one]
      calc ((w₁ * v) * (w₁ * w₂)) * q * ((w₁ * v) * (w₁ * w₂))⁻¹
          = w₁ * v * ((w₁ * w₂) * q * (w₁ * w₂)⁻¹) * v⁻¹ * w₁⁻¹ := by group
        _ = w₁ * v * q⁻¹ * v⁻¹ * w₁⁻¹ := by rw [h0]
        _ = w₁ * (v * q⁻¹ * v⁻¹) * w₁⁻¹ := by group
        _ = w₁ * q⁻¹ * w₁⁻¹ := by rw [hvq']; group
        _ = (w₁ * q * w₁⁻¹)⁻¹ := by group
    rw [e, inv_eq_iff_eq_inv]
    exact hfix.2 q hq

end Card

end CFSG.GH74.GLS.Stage4.Rest
