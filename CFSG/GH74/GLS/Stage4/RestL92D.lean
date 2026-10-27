module

public import CFSG.GH74.GLS.Stage4.RestL92C
public import CFSG.GH74.GLS.Stage4.RestPre

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest.L92

variable {G : Type} [Group G] {D : Ch6Notation G}

structure Ch6Notation.ShapeStd (D : Ch6Notation G) : Prop where
  a_cycle : D.a⁻¹ * D.u * D.a = D.z * D.u
  cent_z : centralizer ({D.z} : Set G) ⊓ D.P = D.X₁ ⊔ D.X₂
  cent_u : centralizer ({D.u} : Set G) ⊓ D.P = conjBy D.a (D.X₁' ⊔ D.X₂')
  cent_zu : centralizer ({D.z * D.u} : Set G) ⊓ D.P = conjBy (D.a ^ 2) (D.X₁ ⊔ D.X₂')

theorem Ch6Basics.irr_X₁ (h : Ch6Basics D) : Irr D.H D.X₁ := by
  have hP := (SL2Pair.toSL2Phi (fun x hx y hy => ?_) (fun x hx y hy => ?_) h.sl2₁ : _)
  · have hodd : Odd (Nat.card ↥(D.root 1)) := by
      rw [root_p1, h.card_X₁]
      exact h.q₁_odd
    have := SL2Phi.irred hP hodd
    rwa [root_p1] at this
  · rw [root_p1] at hy ⊢
    exact h.H_norm_X₁ x hx y hy
  · rw [root_m1] at hy ⊢
    exact h.H_norm_X₁' x hx y hy

theorem Ch6Basics.irr_X₁' (h : Ch6Basics D) : Irr D.H D.X₁' := by
  have := irr_conjBy h.irr_X₁ (g := D.w₁⁻¹) (Subgroup.inv_mem _ h.w₁_normH)
  rwa [DodecA.conjBy_w₁_X₁ h] at this

theorem Ch6Basics.irr_X₂' (h : Ch6Basics D) : Irr D.H D.X₂' := by
  have hP := (SL2Pair.toSL2Phi (fun x hx y hy => ?_) (fun x hx y hy => ?_) h.sl2₆ : _)
  · have hodd : Odd (Nat.card ↥(D.root 6)) := by
      rw [root_p6, DodecA.card_conjBy, h.card_X₂']
      exact h.q₂_odd
    have h6 := SL2Phi.irred hP hodd
    have := irr_conjBy h6 (g := D.a⁻¹) (Subgroup.inv_mem _ h.a_normH)
    rwa [root_p6, ← BNPair.conjBy_mul, mul_inv_cancel, BNPair.conjBy_one] at this
  · exact h.invariant 6 ⟨by norm_num, by norm_num⟩ x hx y hy
  · exact h.invariant (-6) ⟨by norm_num, by norm_num⟩ x hx y hy

theorem Ch6Basics.irr_X₂ (h : Ch6Basics D) : Irr D.H D.X₂ := by
  have := irr_conjBy h.irr_X₂' (g := D.w₂⁻¹) (Subgroup.inv_mem _ h.w₂_normH)
  rwa [DodecA.conjBy_w₂_X₂' h] at this

theorem Ch6Basics.root_irr (h : Ch6Basics D) : ∀ i : ℤ, IsRoot 6 i → Irr D.H (D.root i) := fun _ hi =>
  DodecA.root_rec D (Irr D.H) h.irr_X₁ h.irr_X₁' h.irr_X₂ h.irr_X₂'
    (fun _ hB => irr_conjBy hB h.a_normH) (fun _ hB => irr_conjBy hB (pow_mem h.a_normH 2)) hi

theorem Ch6Core.root_neg_not_le (h : Ch6Core D) {k : ℤ} (hk1 : 1 ≤ k) (hk6 : k ≤ 6) :
    ¬ D.root (-k) ≤ D.P := by
  intro hle
  have hrot := actsAs_rot (actsAs_r₁ h.toCh6Basics.act₁) (actsAs_r₂ h.toCh6Basics.act₂) 3
  have hpos : Rt 6 (k - 1) = k := by
    rw [Rt6_of_lt (by omega) (by omega)]
    ring
  have hneg : Rt 6 (k - 1 + 2 * ((3 : ℕ) : ℤ)) = -k := by
    rw [Rt6_of_ge (by push_cast; omega) (by push_cast; omega)]
    push_cast
    ring
  apply h.toCh6Basics.root_ne_bot (-k) ⟨by omega, by omega⟩
  rw [eq_bot_iff]
  intro y hy
  have hxroot : (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3) ∈ D.root k := by
    have e : (D.w₁ * D.r₂) ^ 3 * (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3) *
        ((D.w₁ * D.r₂) ^ 3)⁻¹ = y := by group
    have := (hrot (k - 1) (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3)).2 (by
      show (D.w₁ * D.r₂) ^ 3 * (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3) *
        ((D.w₁ * D.r₂) ^ 3)⁻¹ ∈ D.root (Rt 6 (k - 1 + 2 * ((3 : ℕ) : ℤ)))
      rw [e, hneg]
      exact hy)
    rwa [hpos] at this
  have hxP : (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3) ∈ D.P := h.root_le_P hk1 hk6 hxroot
  have hxc : (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3) ∈ conjBy ((D.w₁ * D.r₂) ^ 3) D.P := by
    rw [mem_conjBy_iff]
    have e : (D.w₁ * D.r₂) ^ 3 * (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3) *
        ((D.w₁ * D.r₂) ^ 3)⁻¹ = y := by group
    rw [e]
    exact hle hy
  have h1 : (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3) ∈ D.P ⊓ conjBy ((D.w₁ * D.r₂) ^ 3) D.P :=
    ⟨hxP, hxc⟩
  rw [h.opp'] at h1
  have h2 : ((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3 = 1 := h1
  have : y = 1 := by
    have e : y = (D.w₁ * D.r₂) ^ 3 * (((D.w₁ * D.r₂) ^ 3)⁻¹ * y * (D.w₁ * D.r₂) ^ 3) *
        ((D.w₁ * D.r₂) ^ 3)⁻¹ := by group
    rw [e, h2]
    group
  simp [this]

theorem comm_conjBy₂ {A B : Subgroup G} (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (m : G) :
    ∀ x ∈ conjBy m A, ∀ y ∈ conjBy m B, x * y = y * x := by
  intro x hx y hy
  rw [mem_conjBy_iff] at hx hy
  have h := hAB _ hx _ hy
  have e1 : x * y = m⁻¹ * ((m * x * m⁻¹) * (m * y * m⁻¹)) * m := by group
  have e2 : y * x = m⁻¹ * ((m * y * m⁻¹) * (m * x * m⁻¹)) * m := by group
  rw [e1, e2, h]

theorem Ch6Core.l92Data (h : Ch6Core D) (hs : D.ShapeStd) :
    L92Data D.p D.H D.P D.z D.u D.root where
  prime := h.prime
  p_ne_two := h.p_ne_two
  P_pGroup := h.P_pGroup
  zz := by
    have := pow_orderOf_eq_one D.z
    rwa [h.z_ord, pow_two] at this
  uu := by
    have hzz : D.z * D.z = 1 := by
      have := pow_orderOf_eq_one D.z
      rwa [h.z_ord, pow_two] at this
    have e : D.u * D.u = D.a⁻¹ * (D.z * D.z) * D.a := by
      simp only [Ch6Notation.u]
      group
    rw [e, hzz]
    group
  zu_comm := by
    have hu : D.u ∈ D.H := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h.a_normH) D.z).1 h.z_mem_H
      simpa [Ch6Notation.u] using this
    exact h.H_comm D.z h.z_mem_H D.u hu
  z_ne := by
    intro h1
    have := h.z_ord
    rw [h1, orderOf_one] at this
    omega
  u_ne := by
    intro h1
    have hz1 : D.z = 1 := by
      have e : D.z = D.a * D.u * D.a⁻¹ := by simp only [Ch6Notation.u]; group
      rw [e, h1]
      group
    have := h.z_ord
    rw [hz1, orderOf_one] at this
    omega
  zu_ne := by
    intro hzu
    have hdef : D.u = D.a⁻¹ * D.z * D.a := rfl
    have h1 := hs.a_cycle
    have h2 : D.a⁻¹ * D.u * D.a = D.u := by
      calc D.a⁻¹ * D.u * D.a = D.a⁻¹ * D.z * D.a := by rw [← hzu]
        _ = D.u := hdef.symm
    have h3 : D.z * D.u = D.u := h1.symm.trans h2
    have hz1 : D.z = 1 := mul_right_cancel (h3.trans (one_mul D.u).symm)
    have := h.z_ord
    rw [hz1, orderOf_one] at this
    omega
  z_mem := h.z_mem_H
  u_mem := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h.a_normH) D.z).1 h.z_mem_H
    simpa [Ch6Notation.u] using this
  inv := fun i h1 h6 => h.invariant i ⟨by omega, by omega⟩
  ne_bot := fun i h1 h6 => h.root_ne_bot i ⟨by omega, by omega⟩
  irr := fun i h1 h6 => h.root_irr i ⟨by omega, by omega⟩
  inequiv := fun i j h1 h6 h1' h6' hij => h.inequiv i j h1 h6 h1' h6' hij
  comm₁ := by
    intro x hx y hy
    rw [root_p1] at hx
    rw [root_p4] at hy
    have hxK : x ∈ D.K₁ := by rw [h.K₁_eq]; exact Subgroup.mem_sup_left hx
    have hyK : y ∈ D.K₂ := by rw [h.K₂_eq]; exact Subgroup.mem_sup_left hy
    exact h.K_comm x hxK y hyK
  comm₂ := by
    rw [root_p3, root_p6]
    refine comm_conjBy₂ (fun x hx y hy => ?_) D.a
    have hxK : x ∈ D.K₁ := by rw [h.K₁_eq]; exact Subgroup.mem_sup_right hx
    have hyK : y ∈ D.K₂ := by rw [h.K₂_eq]; exact Subgroup.mem_sup_right hy
    exact h.K_comm x hxK y hyK
  comm₃ := by
    rw [root_p5, root_p2]
    refine comm_conjBy₂ (fun x hx y hy => ?_) (D.a ^ 2)
    have hxK : x ∈ D.K₁ := by rw [h.K₁_eq]; exact Subgroup.mem_sup_left hx
    have hyK : y ∈ D.K₂ := by rw [h.K₂_eq]; exact Subgroup.mem_sup_right hy
    exact h.K_comm x hxK y hyK
  cent_z := by
    rw [root_p1, root_p4, inf_comm]
    exact hs.cent_z
  cent_u := by
    rw [root_p3, root_p6, ← conjBy_sup', inf_comm]
    exact hs.cent_u
  cent_zu := by
    rw [root_p5, root_p2, ← conjBy_sup', inf_comm]
    exact hs.cent_zu

theorem Ch6Core.l92_of_shapeStd [Finite G] (h : Ch6Core D) (hs : D.ShapeStd) : D.L92 := by
  have hd := h.l92Data hs
  intro Z hZP hZ l hl hlmem
  have hlpos : ∀ i, i ∈ l ↔ 1 ≤ i ∧ i ≤ 6 ∧ D.root i ≤ Z := by
    intro i
    rw [hlmem i]
    constructor
    · rintro ⟨hi, hle⟩
      have hi1 : 1 ≤ i := by
        by_contra hneg
        have hlt : i < 0 := by
          have := hi.1
          omega
        have h6 : -i ≤ 6 := by
          have := hi.2
          omega
        have := h.root_neg_not_le (k := -i) (by omega) h6
        exact this (by rw [neg_neg]; exact hle.trans hZP)
      have hi6 : i ≤ 6 := by
        have := hi.2
        omega
      exact ⟨hi1, hi6, hle⟩
    · rintro ⟨h1, h6, hle⟩
      exact ⟨⟨by omega, by omega⟩, hle⟩
  exact hd.eq_chainProd hZP hZ l hl hlpos

theorem Ch6Pre.shapeStd_of (h : Ch6Pre D)
    (hc : centralizer ({D.z} : Set G) ⊓ D.P = D.X₁ ⊔ D.X₂ ∧
      centralizer ({D.u} : Set G) ⊓ D.P = conjBy D.a (D.A true ⊔ D.B true) ∧
      centralizer ({D.z * D.u} : Set G) ⊓ D.P = conjBy (D.a ^ 2) (D.A false ⊔ D.B true)) :
    D.ShapeStd where
  a_cycle := h.pre.a_cycle
  cent_z := hc.1
  cent_u := by simpa [Ch6Notation.A, Ch6Notation.B] using hc.2.1
  cent_zu := by simpa [Ch6Notation.A, Ch6Notation.B] using hc.2.2

end CFSG.GH74.GLS.Stage4.Rest
