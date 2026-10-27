module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace Perp23

namespace Three

section Frame

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W K K' : Subgroup Y} {t : Y}
  (D : Two.TwoFrame Ω W K K' t)

include D

theorem t_ne_one : t ≠ 1 := D.hzK.ne_one

theorem j_ne_one : D.F.j ≠ 1 := D.F.hj.ne_one

theorem ce_mul_self (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.ce * D.ce = 1 := by
  have hm := D.x₁_mem_W
  have e2 : D.ce * D.ce =
      (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ ((2 * D.m : ℕ) : ℤ) := by
    rw [zpow_natCast, Two.TwoFrame.ce, ← pow_add, two_mul]
  rw [e2]
  rw [A3Mod.pow_triple (hc _ D.x₁_mem_W _ D.x₂_mem_W) (hc _ D.x₁_mem_W _ D.x₃_mem_W)
    (hc _ D.x₂_mem_W _ D.x₃_mem_W)]
  have h1 : D.x₁ ^ ((2 * D.m : ℕ) : ℤ) = t := by rw [zpow_natCast]; exact D.z₁
  have h2 : D.x₂ ^ (-((2 * D.m : ℕ) : ℤ)) = t := by
    rw [zpow_neg, zpow_natCast, D.z₂]
    exact inv_eq_of_mul_eq_one_right D.hzK.sq
  have h3 : D.x₃ ^ (2 * ((2 * D.m : ℕ) : ℤ)) = 1 := by
    have : (2 * ((2 * D.m : ℕ) : ℤ)) = ((4 * D.m : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, ← D.o₃]
    exact pow_orderOf_eq_one _
  rw [h1, h2, h3, mul_one]
  exact D.hzK.sq

theorem u_mul_self (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.u * D.u = 1 := by
  have h := D.u_mul_e hc
  have hej : D.F.j * D.ce = D.u := by
    have hce := ce_mul_self D hc
    calc D.F.j * D.ce = (D.u * D.ce) * D.ce := by rw [h]
      _ = D.u * (D.ce * D.ce) := by group
      _ = D.u := by rw [hce, mul_one]
  have hjc : D.F.j * D.ce = D.ce * D.F.j := hc _ D.j_mem_W _ D.e_mem_W
  calc D.u * D.u = (D.F.j * D.ce) * (D.F.j * D.ce) := by rw [hej]
    _ = (D.F.j * D.F.j) * (D.ce * D.ce) := by
        calc (D.F.j * D.ce) * (D.F.j * D.ce) = D.F.j * (D.ce * D.F.j) * D.ce := by group
          _ = D.F.j * (D.F.j * D.ce) * D.ce := by rw [← hjc]
          _ = (D.F.j * D.F.j) * (D.ce * D.ce) := by group
    _ = 1 := by rw [D.j_sq, ce_mul_self D hc, mul_one]

theorem e_mul_j (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.ce * D.F.j = D.u := by
  have h := D.u_mul_e hc
  have hce := ce_mul_self D hc
  calc D.ce * D.F.j = D.ce * (D.u * D.ce) := by rw [h]
    _ = (D.ce * D.ce) * D.u := by
        have := hc _ D.u_mem_W _ D.e_mem_W
        calc D.ce * (D.u * D.ce) = D.ce * (D.ce * D.u) := by rw [← this]
          _ = (D.ce * D.ce) * D.u := by group
    _ = D.u := by rw [hce, one_mul]

theorem j_comm_t (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.F.j * t = t * D.F.j :=
  hc _ D.j_mem_W _ D.t_mem_W

theorem t_ne_j (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : t ≠ D.F.j := by
  intro h
  have h1 := D.s_t hc
  have h2 := D.s_j
  rw [← h] at h2
  rw [h2] at h1
  have h3 : t * 1 = t * D.F.j := by rw [mul_one]; exact h1
  exact j_ne_one D (mul_left_cancel h3).symm

theorem ce_ne_t (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.ce ≠ t := by
  intro h
  have h1 := D.s_t hc
  have h2 := D.s_e hc
  rw [h] at h2
  rw [h2] at h1
  have h3 : t * 1 = t * D.F.j := by rw [mul_one]; exact h1
  exact j_ne_one D (mul_left_cancel h3).symm

theorem ce_ne_j (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.ce ≠ D.F.j := by
  intro h
  have h1 := D.r_j hc
  have h2 := D.r_e hc
  rw [h] at h2
  rw [h2] at h1
  have h3 : D.F.j * 1 = D.F.j * t := by rw [mul_one]; exact h1
  exact t_ne_one D (mul_left_cancel h3).symm

theorem ce_ne_t_mul_j (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.ce ≠ t * D.F.j := by
  intro h
  have h2 := D.r_e hc
  have hrt : D.F.ρ.r * t * D.F.ρ.r⁻¹ = t := by rw [D.r_t]; group
  have hrj := D.r_j hc
  have h3 : D.F.ρ.r * (t * D.F.j) * D.F.ρ.r⁻¹ = D.F.j := by
    calc D.F.ρ.r * (t * D.F.j) * D.F.ρ.r⁻¹
        = (D.F.ρ.r * t * D.F.ρ.r⁻¹) * (D.F.ρ.r * D.F.j * D.F.ρ.r⁻¹) := by group
      _ = t * (D.F.j * t) := by rw [hrt, hrj]
      _ = (t * t) * D.F.j := by
          have := j_comm_t D hc
          rw [this]; group
      _ = D.F.j := by rw [D.hzK.sq, one_mul]
  rw [h] at h2
  rw [h2] at h3
  have h4 : t * D.F.j = 1 * D.F.j := by rw [one_mul]; exact h3
  exact t_ne_one D (mul_right_cancel h4)

@[expose] def bGrp : Subgroup Y := Subgroup.closure ({t, D.F.j, D.ce} : Set Y)

theorem t_mem_bGrp : t ∈ bGrp D := Subgroup.subset_closure (by simp)

theorem j_mem_bGrp : D.F.j ∈ bGrp D := Subgroup.subset_closure (by simp)

theorem e_mem_bGrp : D.ce ∈ bGrp D := Subgroup.subset_closure (by simp)

theorem u_mem_bGrp (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.u ∈ bGrp D := by
  rw [← e_mul_j D hc]
  exact (bGrp D).mul_mem (e_mem_bGrp D) (j_mem_bGrp D)

theorem bGrp_comm (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    ∀ x ∈ bGrp D, ∀ y ∈ bGrp D, x * y = y * x := by
  refine T7A.commutes_closure ?_
  intro a ha b hb
  have hmem : ∀ x ∈ ({t, D.F.j, D.ce} : Set Y), x ∈ W := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact D.t_mem_W
    · exact D.j_mem_W
    · exact D.e_mem_W
  exact hc a (hmem a ha) b (hmem b hb)

theorem bGrp_sq (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : ∀ x ∈ bGrp D, x * x = 1 := by
  refine T7A.sq_closure ?_ (bGrp_comm D hc |> fun h a ha b hb => h a (Subgroup.subset_closure ha) b
    (Subgroup.subset_closure hb))
  intro a ha
  rcases ha with rfl | rfl | rfl
  · exact D.hzK.sq
  · exact D.j_sq
  · exact ce_mul_self D hc

theorem isElemAbelian_bGrp (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    IsElemAbelian 2 (bGrp D) :=
  ⟨⟨⟨fun a b => Subtype.ext (bGrp_comm D hc _ a.2 _ b.2)⟩⟩, fun x hx => by
    rw [pow_two]; exact bGrp_sq D hc x hx⟩

theorem card_bGrp (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (he1 : D.ce ≠ 1) :
    Nat.card (bGrp D) = 8 := by
  have hnot : D.ce ∉ Subgroup.closure ({t, D.F.j} : Set Y) := by
    intro hx
    rcases T7B.mem_closure_pair D.hzK.sq D.j_sq D.hzK.ne_one (j_ne_one D)
      (j_comm_t D hc).symm hx with h | h | h | h
    · exact he1 h
    · exact ce_ne_t D hc h
    · exact ce_ne_j D hc h
    · exact ce_ne_t_mul_j D hc h
  exact T7B.natCard_closure_three_eq_eight D.hzK.sq D.j_sq (ce_mul_self D hc) (t_ne_one D)
    (j_ne_one D) (t_ne_j D hc) he1 (j_comm_t D hc).symm (hc _ D.t_mem_W _ D.e_mem_W)
    (hc _ D.j_mem_W _ D.e_mem_W) hnot

omit D in
theorem mem_normalizer_of_conjSub_le {B : Subgroup Y} {g : Y} (h : conjSub g B ≤ B) :
    g ∈ Subgroup.normalizer (B : Set Y) := by
  have hcard : Nat.card B ≤ Nat.card (conjSub g B) := by
    unfold conjSub
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge h hcard)

theorem mgrp_le_normalizer_bGrp (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (c : Q3CL.Thompson.Ctx Ω W) :
    MGrp Ω W ≤ Subgroup.normalizer (bGrp D : Set Y) := by
  intro g hg
  apply mem_normalizer_of_conjSub_le
  have hN := D.mgrp_le_normalizer hΩ hW c hg
  have hE : Subgroup.closure ({t, D.F.j} : Set Y) ≤ bGrp D := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact t_mem_bGrp D
    · exact j_mem_bGrp D
  have hfix := D.mgrp_fix_e hΩ hW c g hg
  have hmap : conjSub g (bGrp D) =
      Subgroup.closure ((MulAut.conj g).toMonoidHom '' ({t, D.F.j, D.ce} : Set Y)) :=
    MonoidHom.map_closure _ _
  rw [hmap, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with rfl | rfl | rfl
  · exact hE ((Subgroup.mem_normalizer_iff.mp hN _).mp (Subgroup.subset_closure (by simp)))
  · exact hE ((Subgroup.mem_normalizer_iff.mp hN _).mp (Subgroup.subset_closure (by simp)))
  · show g * D.ce * g⁻¹ ∈ bGrp D
    rw [hfix]
    simpa using e_mem_bGrp D

theorem g0_t (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    (D.F.ρ.r * D.F.ρ₃.r) * t * (D.F.ρ.r * D.F.ρ₃.r)⁻¹ = D.F.j := by
  have h1 := D.s_t hc
  have hrt : D.F.ρ.r * t * D.F.ρ.r⁻¹ = t := by rw [D.r_t]; group
  have hrj := D.r_j hc
  calc (D.F.ρ.r * D.F.ρ₃.r) * t * (D.F.ρ.r * D.F.ρ₃.r)⁻¹
      = D.F.ρ.r * (D.F.ρ₃.r * t * D.F.ρ₃.r⁻¹) * D.F.ρ.r⁻¹ := by group
    _ = D.F.ρ.r * (t * D.F.j) * D.F.ρ.r⁻¹ := by rw [h1]
    _ = (D.F.ρ.r * t * D.F.ρ.r⁻¹) * (D.F.ρ.r * D.F.j * D.F.ρ.r⁻¹) := by group
    _ = t * (D.F.j * t) := by rw [hrt, hrj]
    _ = D.F.j := by
        rw [j_comm_t D hc]
        calc t * (t * D.F.j) = (t * t) * D.F.j := by group
          _ = D.F.j := by rw [D.hzK.sq, one_mul]

theorem g0_e (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    (D.F.ρ.r * D.F.ρ₃.r) * D.ce * (D.F.ρ.r * D.F.ρ₃.r)⁻¹ = D.ce := by
  have h1 := D.s_e hc
  have h2 := D.r_e hc
  calc (D.F.ρ.r * D.F.ρ₃.r) * D.ce * (D.F.ρ.r * D.F.ρ₃.r)⁻¹
      = D.F.ρ.r * (D.F.ρ₃.r * D.ce * D.F.ρ₃.r⁻¹) * D.F.ρ.r⁻¹ := by group
    _ = D.ce := by rw [h1, h2]

theorem t_mul_e_eq (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    t * D.ce = (D.F.ρ.r * D.F.ρ₃.r)⁻¹ * D.u * ((D.F.ρ.r * D.F.ρ₃.r)⁻¹)⁻¹ := by
  set g : Y := D.F.ρ.r * D.F.ρ₃.r with hg
  have h1 : g * (t * D.ce) * g⁻¹ = D.u := by
    calc g * (t * D.ce) * g⁻¹ = (g * t * g⁻¹) * (g * D.ce * g⁻¹) := by group
      _ = D.F.j * D.ce := by rw [g0_t D hc, g0_e D hc]
      _ = D.u := by
          rw [hc _ D.j_mem_W _ D.e_mem_W]
          exact e_mul_j D hc
  rw [← h1]
  group

theorem exists_normalizer_conj_of_mem_bGrp (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (c : Q3CL.Thompson.Ctx Ω W) {x : Y} (hx : x ∈ bGrp D) (hx1 : x ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (bGrp D : Set Y),
      x = g * t * g⁻¹ ∨ x = g * D.u * g⁻¹ ∨ x = g * D.ce * g⁻¹ := by
  have hc := WTool.comm_of_mem_wSet hΩ hW
  have hMN := mgrp_le_normalizer_bGrp D hΩ hW c
  have hrN : D.F.ρ.r ∈ Subgroup.normalizer (bGrp D : Set Y) := hMN D.r_mem_mgrp
  have hsN : D.F.ρ₃.r ∈ Subgroup.normalizer (bGrp D : Set Y) := hMN D.s_mem_mgrp
  have hg0 : (D.F.ρ.r * D.F.ρ₃.r) ∈ Subgroup.normalizer (bGrp D : Set Y) :=
    Subgroup.mul_mem _ hrN hsN
  have h1N : (1 : Y) ∈ Subgroup.normalizer (bGrp D : Set Y) := Subgroup.one_mem _
  have hej : D.F.j * D.ce = D.u := by
    rw [hc _ D.j_mem_W _ D.e_mem_W]; exact e_mul_j D hc
  rcases T8T.mem_closure_three_involutions D.hzK.sq D.j_sq (ce_mul_self D hc)
    (j_comm_t D hc).symm (hc _ D.t_mem_W _ D.e_mem_W) (hc _ D.j_mem_W _ D.e_mem_W) hx with
    h | h | h | h | h | h | h | h
  · exact absurd h hx1
  · exact ⟨1, h1N, Or.inl (by rw [h]; group)⟩
  · exact ⟨D.F.ρ.r * D.F.ρ₃.r, hg0, Or.inl (by rw [h, g0_t D hc])⟩
  · exact ⟨1, h1N, Or.inr (Or.inr (by rw [h]; group))⟩
  · exact ⟨D.F.ρ₃.r, hsN, Or.inl (by rw [h, D.s_t hc])⟩
  · exact ⟨(D.F.ρ.r * D.F.ρ₃.r)⁻¹, Subgroup.inv_mem _ hg0, Or.inr (Or.inl (by
      rw [h, t_mul_e_eq D hc]))⟩
  · exact ⟨1, h1N, Or.inr (Or.inl (by rw [h, hej]; group))⟩
  · refine ⟨D.F.ρ.r, hrN, Or.inr (Or.inl ?_)⟩
    rw [h, D.r_u hc, ← hej]
    group

theorem ce_ne_one_of_wCentral (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (c : Q3CL.Thompson.Ctx Ω W) (hwc : TwinPerp.WCentralNontrivial W) : D.ce ≠ 1 := by
  obtain ⟨w, hwW, hw1, hwcen⟩ := hwc
  have hc := WTool.comm_of_mem_wSet hΩ hW
  have hfix : ∀ g ∈ MGrp Ω W, g * w * g⁻¹ = w := fun g hg => by
    have := hwcen g (Thompson.MGrp_le_normalizer Ω W hg)
    rw [this]; group
  have hcl : W ≤ Subgroup.closure ({D.x₁, D.x₂, D.x₃} : Set Y) :=
    D.F.W_le_closure c D.he D.hab D.hcomm D.hac D.h₁ D.h₂ D.h₃ D.r₂ D.r₃ D.t₃
  have hfix1 := A3Mod.fixed_eq_one_or (m := D.m) (hc _ D.x₁_mem_W _ D.x₂_mem_W)
    (hc _ D.x₁_mem_W _ D.x₃_mem_W) (hc _ D.x₂_mem_W _ D.x₃_mem_W) D.o₁ D.o₂ D.o₃
    (D.z₁.trans D.z₂.symm) D.r₁ D.r₂ D.r₃ D.t₁ D.t₂ D.t₃ D.s₁ D.s₂ D.s₃ (hcl hwW)
    (hfix _ D.r_mem_mgrp) (hfix _ D.r'_mem_mgrp) (hfix _ D.s_mem_mgrp)
  rcases hfix1 with h | h
  · exact absurd h hw1
  · intro he1
    apply hw1
    rw [h]
    exact he1

end Frame

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
