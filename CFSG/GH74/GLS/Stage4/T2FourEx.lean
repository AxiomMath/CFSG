module

public import CFSG.GH74.GLS.Stage4.T2Four

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section Parity

variable {G : Type} [Group G]

@[expose] noncomputable def t2Par (M : Subgroup G) (g : G) : ZMod 2 := by
  classical exact if g ∈ M then 0 else 1

theorem t2Par_eq_zero_iff {M : Subgroup G} {g : G} : t2Par M g = 0 ↔ g ∈ M := by
  classical
  unfold t2Par
  by_cases hg : g ∈ M <;> simp [hg]

theorem t2Par_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) : t2Par M g = 0 :=
  t2Par_eq_zero_iff.2 hg

theorem t2Par_mul {M C : Subgroup G} (hidx : M.relIndex C = 2) {x y : G} (hx : x ∈ C)
    (hy : y ∈ C) : t2Par M (x * y) = t2Par M x + t2Par M y := by
  classical
  have h2 : (M.subgroupOf C).index = 2 := hidx
  have key := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  simp only [Subgroup.mem_subgroupOf] at key
  change x * y ∈ M ↔ (x ∈ M ↔ y ∈ M) at key
  unfold t2Par
  by_cases hxM : x ∈ M <;> by_cases hyM : y ∈ M <;> simp [hxM, hyM] at key ⊢ <;> simp [key]
  all_goals decide

theorem t2Par_inv {M : Subgroup G} (g : G) : t2Par M g⁻¹ = t2Par M g := by
  classical
  unfold t2Par
  simp

theorem t2Par_conj {M C : Subgroup G} (hidx : M.relIndex C = 2) {c y : G} (hc : c ∈ C)
    (hy : y ∈ C) : t2Par M (c * y * c⁻¹) = t2Par M y := by
  rw [t2Par_mul hidx (C.mul_mem hc hy) (C.inv_mem hc), t2Par_mul hidx hc hy, t2Par_inv]
  generalize t2Par M c = p
  generalize t2Par M y = q
  revert p q
  decide

end Parity

section Fixed

theorem t2_exists_fixed_conj {G : Type} [Group G] [Finite G] {a : G} (ha3 : a ^ 3 = 1) (X : Set G)
    (hX : ∀ y ∈ X, a * y * a⁻¹ ∈ X) (hX' : ∀ y ∈ X, a⁻¹ * y * a ∈ X)
    (hcard : ¬ 3 ∣ Nat.card X) : ∃ y ∈ X, a * y * a⁻¹ = y := by
  classical
  have : Fintype X := Fintype.ofFinite X
  let σ : Equiv.Perm X :=
    { toFun := fun y => ⟨a * y * a⁻¹, hX y y.2⟩
      invFun := fun y => ⟨a⁻¹ * y * a, hX' y y.2⟩
      left_inv := fun y => by apply Subtype.ext; simp [mul_assoc]
      right_inv := fun y => by apply Subtype.ext; simp [mul_assoc] }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext y
    apply congrArg Subtype.val
    show (σ ^ 3) y = y
    have : ((σ ^ 3) y : G) = a ^ 3 * y * (a ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.coe_mul, Function.comp_apply]
      show a * (a * (a * (y : G) * a⁻¹) * a⁻¹) * a⁻¹ = _
      group
    apply Subtype.ext
    rw [this, ha3]
    simp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (by rwa [← Nat.card_eq_fintype_card]) hσ
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end Fixed

section Re

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

theorem T2Four.rechoose (h : T2Four z u K₁ K₂ H w₁ w₂) {x₁ x₂ : G} (hx₁ : x₁ ∈ H) (hx₁K : x₁ ∈ K₁)
    (hx₂ : x₂ ∈ H) (hx₂K : x₂ ∈ K₂) : T2Four z u K₁ K₂ H (x₁ * w₁) (x₂ * w₂) := by
  have hw₁x : w₁ * x₁ * w₁⁻¹ = x₁⁻¹ := by
    have h1 := h.w₀_inv x₁ hx₁
    have hc : w₂ * x₁ = x₁ * w₂ := (h.K_comm x₁ hx₁K w₂ h.w₂_mem).symm
    calc w₁ * x₁ * w₁⁻¹ = w₁ * (w₂ * x₁ * w₂⁻¹) * w₁⁻¹ := by rw [hc]; group
      _ = (w₁ * w₂) * x₁ * (w₁ * w₂)⁻¹ := by group
      _ = x₁⁻¹ := h1
  have hw₂x : w₂ * x₂ * w₂⁻¹ = x₂⁻¹ := by
    have h1 := h.w₀_inv x₂ hx₂
    have hc : w₁ * (w₂ * x₂ * w₂⁻¹) = (w₂ * x₂ * w₂⁻¹) * w₁ :=
      h.K_comm w₁ h.w₁_mem _ (K₂.mul_mem (K₂.mul_mem h.w₂_mem hx₂K) (K₂.inv_mem h.w₂_mem))
    calc w₂ * x₂ * w₂⁻¹ = w₁ * (w₂ * x₂ * w₂⁻¹) * w₁⁻¹ := by rw [hc]; group
      _ = (w₁ * w₂) * x₂ * (w₁ * w₂)⁻¹ := by group
      _ = x₂⁻¹ := h1
  have hw₁xc : w₁ * x₂ = x₂ * w₁ := h.K_comm w₁ h.w₁_mem x₂ hx₂K
  have hww : (x₁ * w₁) * (x₂ * w₂) = (x₁ * x₂) * (w₁ * w₂) := by
    calc (x₁ * w₁) * (x₂ * w₂) = x₁ * (w₁ * x₂) * w₂ := by group
      _ = x₁ * (x₂ * w₁) * w₂ := by rw [hw₁xc]
      _ = (x₁ * x₂) * (w₁ * w₂) := by group
  have hx₁₂ : x₁ * x₂ ∈ H := H.mul_mem hx₁ hx₂
  refine
    { zz := h.zz, z_ne := h.z_ne, uu := h.uu, u_ne := h.u_ne, zu_ne := h.zu_ne,
      zu_comm := h.zu_comm, K_comm := h.K_comm, K_inter := h.K_inter, K_le_C := h.K_le_C,
      C_norm₁ := h.C_norm₁, C_norm₂ := h.C_norm₂, C_idx := h.C_idx, H_comm := h.H_comm,
      z_mem_H := h.z_mem_H, u_mem_H := h.u_mem_H, H_le_C := h.H_le_C,
      H_not_le_K := h.H_not_le_K, H₁_iff := h.H₁_iff, H₂_iff := h.H₂_iff,
      w₁_mem := K₁.mul_mem hx₁K h.w₁_mem, w₂_mem := K₂.mul_mem hx₂K h.w₂_mem,
      w₁_sq := ?_, w₂_sq := ?_, w₁_u := ?_, w₂_u := ?_, w₁_normH := ?_, w₂_normH := ?_,
      w₀_inv := ?_, w₀_not_mem := ?_ }
  · calc (x₁ * w₁) * (x₁ * w₁) = x₁ * (w₁ * x₁ * w₁⁻¹) * (w₁ * w₁) := by group
      _ = z := by rw [hw₁x, h.w₁_sq]; group
  · calc (x₂ * w₂) * (x₂ * w₂) = x₂ * (w₂ * x₂ * w₂⁻¹) * (w₂ * w₂) := by group
      _ = z := by rw [hw₂x, h.w₂_sq]; group
  · have hzuH : u * z ∈ H := H.mul_mem h.u_mem_H h.z_mem_H
    have hc := h.H_comm x₁ hx₁ (u * z) hzuH
    calc (x₁ * w₁) * u * (x₁ * w₁)⁻¹ = x₁ * (w₁ * u * w₁⁻¹) * x₁⁻¹ := by group
      _ = x₁ * (u * z) * x₁⁻¹ := by rw [h.w₁_u]
      _ = (u * z) * x₁ * x₁⁻¹ := by rw [hc]
      _ = u * z := by group
  · have hzuH : u * z ∈ H := H.mul_mem h.u_mem_H h.z_mem_H
    have hc := h.H_comm x₂ hx₂ (u * z) hzuH
    calc (x₂ * w₂) * u * (x₂ * w₂)⁻¹ = x₂ * (w₂ * u * w₂⁻¹) * x₂⁻¹ := by group
      _ = x₂ * (u * z) * x₂⁻¹ := by rw [h.w₂_u]
      _ = (u * z) * x₂ * x₂⁻¹ := by rw [hc]
      _ = u * z := by group
  · intro y hy
    have : (x₁ * w₁) * y * (x₁ * w₁)⁻¹ = x₁ * (w₁ * y * w₁⁻¹) * x₁⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem hx₁ (h.w₁_normH y hy)) (H.inv_mem hx₁)
  · intro y hy
    have : (x₂ * w₂) * y * (x₂ * w₂)⁻¹ = x₂ * (w₂ * y * w₂⁻¹) * x₂⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem hx₂ (h.w₂_normH y hy)) (H.inv_mem hx₂)
  · intro y hy
    rw [hww]
    have e : ((x₁ * x₂) * (w₁ * w₂)) * y * ((x₁ * x₂) * (w₁ * w₂))⁻¹ =
        (x₁ * x₂) * ((w₁ * w₂) * y * (w₁ * w₂)⁻¹) * (x₁ * x₂)⁻¹ := by group
    rw [e, h.w₀_inv y hy]
    have hc := h.H_comm (x₁ * x₂) hx₁₂ y⁻¹ (H.inv_mem hy)
    calc (x₁ * x₂) * y⁻¹ * (x₁ * x₂)⁻¹ = y⁻¹ * (x₁ * x₂) * (x₁ * x₂)⁻¹ := by rw [hc]
      _ = y⁻¹ := by group
  · intro hmem
    rw [hww] at hmem
    apply h.w₀_not_mem
    have : w₁ * w₂ = (x₁ * x₂)⁻¹ * ((x₁ * x₂) * (w₁ * w₂)) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem hx₁₂) hmem

theorem T2Four.u_w₁ (h : T2Four z u K₁ K₂ H w₁ w₂) : u * w₁ * u⁻¹ = z * w₁ := by
  have h1 : w₁ * u = u * z * w₁ := by
    calc w₁ * u = (w₁ * u * w₁⁻¹) * w₁ := by group
      _ = u * z * w₁ := by rw [h.w₁_u]
  rw [h.u_inv]
  calc u * w₁ * u = u * (w₁ * u) := by group
    _ = u * (u * z * w₁) := by rw [h1]
    _ = (u * u) * z * w₁ := by group
    _ = z * w₁ := by rw [h.uu, one_mul]

theorem T2Four.u_w₂ (h : T2Four z u K₁ K₂ H w₁ w₂) : u * w₂ * u⁻¹ = z * w₂ := by
  have h1 : w₂ * u = u * z * w₂ := by
    calc w₂ * u = (w₂ * u * w₂⁻¹) * w₂ := by group
      _ = u * z * w₂ := by rw [h.w₂_u]
  rw [h.u_inv]
  calc u * w₂ * u = u * (w₂ * u) := by group
    _ = u * (u * z * w₂) := by rw [h1]
    _ = (u * u) * z * w₂ := by group
    _ = z * w₂ := by rw [h.uu, one_mul]

theorem T2Four.H_inf_K (h : T2Four z u K₁ K₂ H w₁ w₂) {x : G} (hx : x ∈ H)
    (hxK : x ∈ K₁ ⊔ K₂) :
    ∃ x₁ ∈ H, x₁ ∈ K₁ ∧ ∃ x₂ ∈ H, x₂ ∈ K₂ ∧ x = x₁ * x₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm h.K_comm x).1 hxK
  have huC := h.u_mem_C
  have hxu : (a * b) * u = u * (a * b) := h.H_comm _ hx u h.u_mem_H
  have ha' : u * a * u⁻¹ ∈ K₁ := h.C_norm₁ u huC a ha
  have hb' : u * b * u⁻¹ ∈ K₂ := h.C_norm₂ u huC b hb
  have hab : (u * a * u⁻¹) * (u * b * u⁻¹) = a * b := by
    calc (u * a * u⁻¹) * (u * b * u⁻¹) = u * (a * b) * u⁻¹ := by group
      _ = a * b := by rw [← hxu]; group
  have hmem : a⁻¹ * (u * a * u⁻¹) ∈ K₁ ⊓ K₂ := by
    refine ⟨K₁.mul_mem (K₁.inv_mem ha) ha', ?_⟩
    have h1 : a⁻¹ * (u * a * u⁻¹) = b * (u * b * u⁻¹)⁻¹ := by
      calc a⁻¹ * (u * a * u⁻¹) = a⁻¹ * ((u * a * u⁻¹) * (u * b * u⁻¹)) * (u * b * u⁻¹)⁻¹ := by
            group
        _ = a⁻¹ * (a * b) * (u * b * u⁻¹)⁻¹ := by rw [hab]
        _ = b * (u * b * u⁻¹)⁻¹ := by group
    rw [h1]
    exact K₂.mul_mem hb (K₂.inv_mem hb')
  rcases t2C_zpowers_cases h.zz (h.K_inter hmem) with h1 | h1
  ·
    have h2 : u * a * u⁻¹ = a := by
      have := congrArg (a * ·) h1
      simpa using this
    have hau : a * u = u * a := by
      calc a * u = (u * a * u⁻¹) * u := by rw [h2]
        _ = u * a := by group
    have h3 : u * b * u⁻¹ = b := by
      rw [h2] at hab
      exact mul_left_cancel hab
    have hbu : b * u = u * b := by
      calc b * u = (u * b * u⁻¹) * u := by rw [h3]
        _ = u * b := by group
    exact ⟨a, (h.H₁_iff a ha).2 hau, ha, b, (h.H₂_iff b hb).2 hbu, hb, rfl⟩
  ·
    exfalso
    have h2 : u * a * u⁻¹ = a * z := by
      have := congrArg (a * ·) h1
      simpa using this
    have h3 : u * b * u⁻¹ = z * b := by
      rw [h2] at hab
      have h4 : a * (z * (u * b * u⁻¹)) = a * b := by rw [← hab]; group
      have h5 := mul_left_cancel h4
      calc u * b * u⁻¹ = z⁻¹ * (z * (u * b * u⁻¹)) := by group
        _ = z⁻¹ * b := by rw [h5]
        _ = z * b := by rw [h.z_inv]
    have hw₁z : w₁⁻¹ * z = z * w₁⁻¹ := by
      calc w₁⁻¹ * z = w₁⁻¹ * z * w₁ * w₁⁻¹ := by group
        _ = w₁⁻¹ * (z * w₁) * w₁⁻¹ := by group
        _ = w₁⁻¹ * (w₁ * z) * w₁⁻¹ := by rw [h.w₁_z]
        _ = z * w₁⁻¹ := by group
    have hw₂z : w₂⁻¹ * z = z * w₂⁻¹ := by
      calc w₂⁻¹ * z = w₂⁻¹ * (z * w₂) * w₂⁻¹ := by group
        _ = w₂⁻¹ * (w₂ * z) * w₂⁻¹ := by rw [h.w₂_z]
        _ = z * w₂⁻¹ := by group
    have ha1 : a * w₁⁻¹ ∈ H := by
      refine (h.H₁_iff _ (K₁.mul_mem ha (K₁.inv_mem h.w₁_mem))).2 ?_
      have e : u * (a * w₁⁻¹) * u⁻¹ = a * w₁⁻¹ := by
        have e1 : u * w₁⁻¹ * u⁻¹ = w₁⁻¹ * z := by
          have := congrArg (·⁻¹) h.u_w₁
          simpa [mul_assoc, h.z_inv] using this
        calc u * (a * w₁⁻¹) * u⁻¹ = (u * a * u⁻¹) * (u * w₁⁻¹ * u⁻¹) := by group
          _ = (a * z) * (w₁⁻¹ * z) := by rw [h2, e1]
          _ = a * (z * w₁⁻¹) * z := by group
          _ = a * (w₁⁻¹ * z) * z := by rw [hw₁z]
          _ = a * w₁⁻¹ * (z * z) := by group
          _ = a * w₁⁻¹ := by rw [h.zz, mul_one]
      calc a * w₁⁻¹ * u = (u * (a * w₁⁻¹) * u⁻¹) * u := by rw [e]
        _ = u * (a * w₁⁻¹) := by group
    have hbz : b * z = z * b :=
      (Subgroup.mem_centralizer_singleton_iff.1 (h.K_le_C (Subgroup.mem_sup_right hb)))
    have hzbz : z * b * z = b * (z * z) := by
      calc z * b * z = z * (b * z) := by group
        _ = z * (z * b) := by rw [hbz]
        _ = (z * z) * b := by group
        _ = b * (z * z) := by rw [h.zz]; group
    have hb1 : b * w₂⁻¹ ∈ H := by
      refine (h.H₂_iff _ (K₂.mul_mem hb (K₂.inv_mem h.w₂_mem))).2 ?_
      have e : u * (b * w₂⁻¹) * u⁻¹ = b * w₂⁻¹ := by
        have e1 : u * w₂⁻¹ * u⁻¹ = w₂⁻¹ * z := by
          have := congrArg (·⁻¹) h.u_w₂
          simpa [mul_assoc, h.z_inv] using this
        calc u * (b * w₂⁻¹) * u⁻¹ = (u * b * u⁻¹) * (u * w₂⁻¹ * u⁻¹) := by group
          _ = (z * b) * (w₂⁻¹ * z) := by rw [h3, e1]
          _ = z * b * (w₂⁻¹ * z) := by group
          _ = z * b * (z * w₂⁻¹) := by rw [hw₂z]
          _ = (z * b * z) * w₂⁻¹ := by group
          _ = b * (z * z) * w₂⁻¹ := by rw [hzbz]
          _ = b * w₂⁻¹ := by rw [h.zz, mul_one]
      calc b * w₂⁻¹ * u = (u * (b * w₂⁻¹) * u⁻¹) * u := by rw [e]
        _ = u * (b * w₂⁻¹) := by group
    apply h.w₀_not_mem
    have hc : w₁ * (b * w₂⁻¹) = (b * w₂⁻¹) * w₁ :=
      h.K_comm w₁ h.w₁_mem _ (K₂.mul_mem hb (K₂.inv_mem h.w₂_mem))
    have hxx : a * b = ((a * w₁⁻¹) * (b * w₂⁻¹)) * (w₁ * w₂) := by
      calc a * b = (a * w₁⁻¹) * (w₁ * (b * w₂⁻¹)) * w₂ := by group
        _ = (a * w₁⁻¹) * ((b * w₂⁻¹) * w₁) * w₂ := by rw [hc]
        _ = ((a * w₁⁻¹) * (b * w₂⁻¹)) * (w₁ * w₂) := by group
    have : w₁ * w₂ = ((a * w₁⁻¹) * (b * w₂⁻¹))⁻¹ * (a * b) := by rw [hxx]; group
    rw [this]
    exact H.mul_mem (H.inv_mem (H.mul_mem ha1 hb1)) hx

end Re

end CFSG.GH74.GLS.Stage4.Rest
