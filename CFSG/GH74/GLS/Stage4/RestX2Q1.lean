module

public import CFSG.GH74.GLS.Stage4.T2Defs
public import CFSG.GH74.GLS.Stage4.RestDodecA
public import CFSG.GH74.GLS.Stage4.T2Coord
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

@[expose] def T2N3.swap (N : T2N3 G) : T2N3 G where
  q₁ := N.q₂
  q₂ := N.q₁
  z := N.z
  S := N.S
  K₁ := N.K₂
  K₂ := N.K₁
  H := N.H
  X₁ := N.X₂
  X₁' := N.X₂'
  X₂ := N.X₁
  X₂' := N.X₁'
  w₁ := N.w₂
  w₂ := N.w₁
  F := N.F
  a := N.a

theorem Ch6Loc5.swap {N : T2N3 G} {u : G} (h : Ch6Loc5 N.toT2N2.toT2N1 u) (hq : N.q₁ = N.q₂) :
    Ch6Loc5 N.swap.toT2N2.toT2N1 u where
  q₁_odd := h.q₂_odd
  q₂_odd := h.q₁_odd
  q₂_le := hq.le
  q₁_ge := by have := h.q₁_ge; show 5 ≤ N.q₂; omega
  q₂_ge := by have := h.q₁_ge; show 3 ≤ N.q₁; omega
  q₁_pp := h.q₂_pp
  q₂_pp := h.q₁_pp
  z_ord := h.z_ord
  one_class := h.one_class
  O2prime := h.O2prime
  K_comm := fun x hx y hy => (h.K_comm y hy x hx).symm
  iso₁ := h.iso₂
  iso₂ := h.iso₁
  z_mem_K₁ := h.z_mem_K₂
  z_mem_K₂ := h.z_mem_K₁
  K_inter := by
    show N.K₂ ⊓ N.K₁ ≤ _
    rw [inf_comm]; exact h.K_inter
  u_ord := h.u_ord
  u_ne := h.u_ne
  u_comm := h.u_comm
  S_pGroup := h.S_pGroup
  S_sylow := h.S_sylow
  z_mem_S := h.z_mem_S
  z_cent_S := h.z_cent_S
  u_mem_S := h.u_mem_S
  S_idx := by
    show (N.S ⊓ (N.K₂ ⊔ N.K₁)).relIndex N.S = 2
    rw [sup_comm]; exact h.S_idx
  w₁_memS := h.w₂_memS
  w₂_memS := h.w₁_memS
  K₁_eq := h.K₂_eq
  K₂_eq := h.K₁_eq
  card_X₁ := h.card_X₂
  card_X₁' := h.card_X₂'
  card_X₂ := h.card_X₁
  card_X₂' := h.card_X₁'
  X₁_comm := h.X₂_comm
  X₁'_comm := h.X₂'_comm
  X₂_comm := h.X₁_comm
  X₂'_comm := h.X₁'_comm
  X₁_exp := h.X₂_exp
  X₁'_exp := h.X₂'_exp
  X₂_exp := h.X₁_exp
  X₂'_exp := h.X₁'_exp
  X₁_ne := h.X₂_ne
  X₂_ne := h.X₁_ne
  H_comm := h.H_comm
  z_mem_H := h.z_mem_H
  u_mem_H := h.u_mem_H
  H₁_eq := h.H₂_eq
  H₂_eq := h.H₁_eq
  H₁_cyc := h.H₂_cyc
  H₂_cyc := h.H₁_cyc
  card_H_K₁ := h.card_H_K₂
  card_H_K₂ := h.card_H_K₁
  H_idx := by
    show ((N.H ⊓ N.K₂) ⊔ (N.H ⊓ N.K₁)).relIndex N.H = 2
    rw [sup_comm]; exact h.H_idx
  H_le := by
    show N.H ≤ N.K₂ ⊔ N.K₁ ⊔ N.S
    rw [sup_comm N.K₂ N.K₁]; exact h.H_le
  H_not_le_K := by
    show ¬ N.H ≤ N.K₂ ⊔ N.K₁
    rw [sup_comm]; exact h.H_not_le_K
  H_norm_X₁ := h.H_norm_X₂
  H_norm_X₁' := h.H_norm_X₂'
  H_norm_X₂ := h.H_norm_X₁
  H_norm_X₂' := h.H_norm_X₁'
  H_fpf₁ := h.H_fpf₂
  H_fpf₁' := h.H_fpf₂'
  H_fpf₂ := h.H_fpf₁
  H_fpf₂' := h.H_fpf₁'
  w₁_mem := h.w₂_mem
  w₂_mem := h.w₁_mem
  w₁_sq := h.w₂_sq
  w₂_sq := h.w₁_sq
  w₁_swap := h.w₂_swap
  w₁_swap' := h.w₂_swap'
  w₂_swap := h.w₁_swap
  w₂_swap' := h.w₁_swap'
  w₁_inv := h.w₂_inv
  w₂_inv := h.w₁_inv
  w₁_u := h.w₂_u
  w₂_u := h.w₁_u
  w₁_normH := h.w₂_normH
  w₂_normH := h.w₁_normH
  w₀_inv := by
    intro x hx
    have hc : N.w₁ * N.w₂ = N.w₂ * N.w₁ := h.K_comm _ h.w₁_mem _ h.w₂_mem
    show (N.w₂ * N.w₁) * x * (N.w₂ * N.w₁)⁻¹ = x⁻¹
    rw [← hc]; exact h.w₀_inv x hx
  w₀_cent := by
    have hc : N.w₁ * N.w₂ = N.w₂ * N.w₁ := h.K_comm _ h.w₁_mem _ h.w₂_mem
    show (N.w₂ * N.w₁) * u = u * (N.w₂ * N.w₁)
    rw [← hc]; exact h.w₀_cent
  u_inv_X₁ := h.u_inv_X₂
  u_inv_X₁' := h.u_inv_X₂'
  u_inv_X₂ := h.u_inv_X₁
  u_inv_X₂' := h.u_inv_X₁'

theorem Ch6F5.swap {N : T2N3 G} (h : Ch6F5 N.toT2N2) : Ch6F5 N.swap.toT2N2 where
  F_def := h.F_def
  F_odd := h.F_odd
  F_comm := h.F_comm
  F_inter_K := by
    show N.F ⊓ (N.K₂ ⊔ N.K₁) = ⊥
    rw [sup_comm]; exact h.F_inter_K
  C_le := by
    show centralizer ({N.z} : Set G) ≤ N.K₂ ⊔ N.K₁ ⊔ N.S ⊔ N.F
    rw [sup_comm N.K₂ N.K₁]; exact h.C_le
  centS := h.centS
  F_normH := h.F_normH
  F_normX₁ := h.F_normX₂
  F_normX₁' := h.F_normX₂'
  F_normX₂ := h.F_normX₁
  F_normX₂' := h.F_normX₁'

theorem Ch6Coord.swap {N : T2N3 G} (h : Ch6Coord N.toT2N2.toT2N1) : Ch6Coord N.swap.toT2N2.toT2N1 :=
  ⟨h.coord₂, h.coord₁⟩

namespace DodecA

theorem dodec_sq2 {Q : Type*} [Group Q] {A W₁ W₂ : Q} (hA : A ^ 3 = 1)
    (h1 : W₁ * A * W₁⁻¹ = A⁻¹) (h2 : W₂ * A * W₂⁻¹ = A⁻¹) (hs1 : W₁ * W₁ = 1) (hs2 : W₂ * W₂ = 1)
    (hc : W₁ * W₂ = W₂ * W₁) : (W₁ * (A⁻¹ * W₂ * A)) ^ 2 = A := by
  have f1 : W₁ * A⁻¹ = A * W₁ := by
    calc W₁ * A⁻¹ = (W₁ * A * W₁⁻¹)⁻¹ * W₁ := by group
      _ = A * W₁ := by rw [h1, inv_inv]
  have f2 : W₂ * A = A⁻¹ * W₂ := by
    calc W₂ * A = (W₂ * A * W₂⁻¹) * W₂ := by group
      _ = A⁻¹ * W₂ := by rw [h2]
  have f3 : (W₁ * W₂) * A = A * (W₁ * W₂) := by
    calc (W₁ * W₂) * A = W₁ * (W₂ * A) := by group
      _ = W₁ * (A⁻¹ * W₂) := by rw [f2]
      _ = (W₁ * A⁻¹) * W₂ := by group
      _ = (A * W₁) * W₂ := by rw [f1]
      _ = A * (W₁ * W₂) := by group
  have f4 : W₁ * (A⁻¹ * W₂ * A) = A ^ 2 * (W₁ * W₂) := by
    calc W₁ * (A⁻¹ * W₂ * A) = (W₁ * A⁻¹) * W₂ * A := by group
      _ = (A * W₁) * W₂ * A := by rw [f1]
      _ = A * ((W₁ * W₂) * A) := by group
      _ = A * (A * (W₁ * W₂)) := by rw [f3]
      _ = A ^ 2 * (W₁ * W₂) := by rw [pow_two, mul_assoc]
  have f5 : (W₁ * W₂) ^ 2 = 1 := by
    calc (W₁ * W₂) ^ 2 = W₁ * (W₂ * W₁) * W₂ := by rw [pow_two]; simp only [mul_assoc]
      _ = W₁ * (W₁ * W₂) * W₂ := by rw [hc]
      _ = (W₁ * W₁) * (W₂ * W₂) := by group
      _ = 1 := by rw [hs1, hs2, mul_one]
  have hcomm : Commute (A ^ 2) (W₁ * W₂) := (show Commute A (W₁ * W₂) from f3.symm).pow_left 2
  rw [f4, hcomm.mul_pow, f5, mul_one, ← pow_mul]
  calc A ^ (2 * 2) = A ^ 3 * A := by rw [← pow_succ]
    _ = A := by rw [hA, one_mul]

theorem sq_of_rel {H : Subgroup G} {a w₁ w₂ : G} (hw₁ : w₁ ∈ normalizer (H : Set G))
    (hw₂ : w₂ ∈ normalizer (H : Set G)) (ha : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 ∈ H)
    (hs₁ : w₁ * w₁ ∈ H) (hs₂ : w₂ * w₂ ∈ H) (hc : w₁ * w₂ = w₂ * w₁)
    (hr₁ : ∃ h ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * h) (hr₂ : ∃ h ∈ H, w₂ * a * w₂⁻¹ = a⁻¹ * h) :
    ((w₁ * (a⁻¹ * w₂ * a)) ^ 2)⁻¹ * a ∈ H := by
  have : (H.subgroupOf (normalizer (H : Set G))).Normal := Subgroup.normal_in_normalizer
  let π : ↥(normalizer (H : Set G)) →* ↥(normalizer (H : Set G)) ⧸
      H.subgroupOf (normalizer (H : Set G)) := QuotientGroup.mk' _
  let w₁' : ↥(normalizer (H : Set G)) := ⟨w₁, hw₁⟩
  let w₂' : ↥(normalizer (H : Set G)) := ⟨w₂, hw₂⟩
  let a' : ↥(normalizer (H : Set G)) := ⟨a, ha⟩
  have hπ : ∀ x y : ↥(normalizer (H : Set G)), π x = π y ↔ (x : G)⁻¹ * (y : G) ∈ H :=
    fun x y => by
      show (QuotientGroup.mk x : _ ⧸ _) = QuotientGroup.mk y ↔ _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
  have hπ1 : ∀ x : ↥(normalizer (H : Set G)), π x = 1 ↔ (x : G) ∈ H := fun x => by
    show (QuotientGroup.mk x : _ ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hA : π a' ^ 3 = 1 := by
    rw [← map_pow π a' 3, hπ1]
    exact ha3
  have hrel : ∀ (w : ↥(normalizer (H : Set G))) (h₁ : G), h₁ ∈ H →
      (w : G) * a * (w : G)⁻¹ = a⁻¹ * h₁ → π w * π a' * (π w)⁻¹ = (π a')⁻¹ := by
    intro w h₁ hh₁ hr
    have e : π (w * a' * w⁻¹) = π a'⁻¹ := by
      rw [hπ]
      show ((w : G) * a * (w : G)⁻¹)⁻¹ * a⁻¹ ∈ H
      rw [hr]
      have : (a⁻¹ * h₁)⁻¹ * a⁻¹ = h₁⁻¹ := by group
      rw [this]
      exact H.inv_mem hh₁
    simpa only [map_mul, map_inv] using e
  obtain ⟨h₁, hh₁, hr₁'⟩ := hr₁
  obtain ⟨h₂, hh₂, hr₂'⟩ := hr₂
  have hsq : ∀ (w : ↥(normalizer (H : Set G))), (w : G) * (w : G) ∈ H → π w * π w = 1 := by
    intro w hw
    rw [← map_mul, hπ1]
    exact hw
  have hc' : π w₁' * π w₂' = π w₂' * π w₁' := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  have k2 := dodec_sq2 hA (hrel w₁' h₁ hh₁ hr₁') (hrel w₂' h₂ hh₂ hr₂') (hsq w₁' hs₁) (hsq w₂' hs₂) hc'
  have e2 : π ((w₁' * (a'⁻¹ * w₂' * a')) ^ 2) = π a' := by
    simpa only [map_mul, map_inv, map_pow] using k2
  have := (hπ _ _).1 e2
  simpa using this

end DodecA

theorem Ch6Weyl.a_mem_swap {N : T2N3 G} {u : G} (hL : Ch6Loc5 N.toT2N2.toT2N1 u) (hW : Ch6Weyl N) :
    N.a ∈ N.swap.Nsub := by
  have hs₁ : N.w₁ * N.w₁ ∈ N.H := by rw [hL.w₁_sq]; exact hL.z_mem_H
  have hs₂ : N.w₂ * N.w₂ ∈ N.H := by rw [hL.w₂_sq]; exact hL.z_mem_H
  have hc : N.w₂ * N.w₁ = N.w₁ * N.w₂ := (hL.K_comm _ hL.w₁_mem _ hL.w₂_mem).symm
  have hsq := DodecA.sq_of_rel (H := N.H) (a := N.a) hL.w₂_normH hL.w₁_normH hW.a_normH hW.a_cube hs₂
    hs₁ hc hW.w₂_a hW.w₁_a
  have hgen₁ : N.w₂ ∈ N.swap.Nsub := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hgen₂ : N.a⁻¹ * N.w₁ * N.a ∈ N.swap.Nsub := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hmem : (N.w₂ * (N.a⁻¹ * N.w₁ * N.a)) ^ 2 ∈ N.swap.Nsub :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ hgen₁ hgen₂) 2
  have hH : (((N.w₂ * (N.a⁻¹ * N.w₁ * N.a)) ^ 2)⁻¹ * N.a)⁻¹ ∈ N.swap.Nsub := by
    refine Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl ?_))
    exact hsq
  have e : N.a = (N.w₂ * (N.a⁻¹ * N.w₁ * N.a)) ^ 2 *
      ((((N.w₂ * (N.a⁻¹ * N.w₁ * N.a)) ^ 2)⁻¹ * N.a)⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hH)

theorem T2N3.swap_Nsub {N : T2N3 G} {u : G} (hL : Ch6Loc5 N.toT2N2.toT2N1 u) (hW : Ch6Weyl N) :
    N.swap.Nsub = N.Nsub := by
  apply le_antisymm
  ·
    refine (Subgroup.closure_le _).2 ?_
    rintro x (hx | rfl | rfl)
    · exact Subgroup.subset_closure (Or.inl hx)
    ·
      have h1 : N.a ∈ N.Nsub := hW.a_mem_N
      have h2 : N.a⁻¹ * N.w₂ * N.a ∈ N.Nsub := Subgroup.subset_closure (Or.inr (Or.inr rfl))
      have : N.w₂ = N.a * (N.a⁻¹ * N.w₂ * N.a) * N.a⁻¹ := by group
      show N.w₂ ∈ N.Nsub
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)
    · have h1 : N.a ∈ N.Nsub := hW.a_mem_N
      have h2 : N.w₁ ∈ N.Nsub := Subgroup.subset_closure (Or.inr (Or.inl rfl))
      show N.a⁻¹ * N.w₁ * N.a ∈ N.Nsub
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2) h1
  ·
    refine (Subgroup.closure_le _).2 ?_
    have h1 : N.a ∈ N.swap.Nsub := Ch6Weyl.a_mem_swap hL hW
    rintro x (hx | rfl | rfl)
    · exact Subgroup.subset_closure (Or.inl hx)
    · have h2 : N.a⁻¹ * N.w₁ * N.a ∈ N.swap.Nsub := Subgroup.subset_closure (Or.inr (Or.inr rfl))
      have : N.w₁ = N.a * (N.a⁻¹ * N.w₁ * N.a) * N.a⁻¹ := by group
      show N.w₁ ∈ N.swap.Nsub
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)
    · have h2 : N.w₂ ∈ N.swap.Nsub := Subgroup.subset_closure (Or.inr (Or.inl rfl))
      show N.a⁻¹ * N.w₂ * N.a ∈ N.swap.Nsub
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2) h1

theorem Ch6Weyl.swap {N : T2N3 G} {u : G} (hL : Ch6Loc5 N.toT2N2.toT2N1 u) (hW : Ch6Weyl N) :
    Ch6Weyl N.swap where
  a_normH := hW.a_normH
  a_cube := hW.a_cube
  w₁_a := hW.w₂_a
  w₂_a := hW.w₁_a
  a_mem_N := Ch6Weyl.a_mem_swap hL hW
  a_cycle := hW.a_cycle
  F_normN := by rw [T2N3.swap_Nsub hL hW]; exact hW.F_normN

theorem Ch6Sec5.swap {N : T2N3 G} {u : G} (h : Ch6Sec5 N u) (hq : N.q₁ = N.q₂) : Ch6Sec5 N.swap u where
  loc := h.loc.swap hq
  F5 := h.F5.swap
  weyl := Ch6Weyl.swap h.loc h.weyl
  u_eq := h.u_eq

end CFSG.GH74.GLS.Stage4.Rest
