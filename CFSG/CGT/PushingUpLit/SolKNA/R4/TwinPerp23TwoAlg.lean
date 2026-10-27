module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoFrame
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinWToolBasic
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngA

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace Perp23

namespace Two

section Alg

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W K K' : Subgroup Y} {t : Y}

namespace TwoFrame

variable (D : TwoFrame Ω W K K' t)

include D

@[expose] def b : Y := D.x₁ ^ D.m

@[expose] def b' : Y := D.x₂ ^ D.m

@[expose] def b₃ : Y := D.x₃ ^ D.m

@[expose] def u : Y := D.b * D.b'⁻¹

theorem x₁_mem_R : D.x₁ ∈ D.F.ρ.R := (D.h₁ ▸ Subgroup.mem_zpowers D.x₁ : D.x₁ ∈ D.F.ρ.R ⊓ W).1

theorem x₁_mem_W : D.x₁ ∈ W := (D.h₁ ▸ Subgroup.mem_zpowers D.x₁ : D.x₁ ∈ D.F.ρ.R ⊓ W).2

theorem x₂_mem_R : D.x₂ ∈ D.F.ρ'.R := (D.h₂ ▸ Subgroup.mem_zpowers D.x₂ : D.x₂ ∈ D.F.ρ'.R ⊓ W).1

theorem x₂_mem_W : D.x₂ ∈ W := (D.h₂ ▸ Subgroup.mem_zpowers D.x₂ : D.x₂ ∈ D.F.ρ'.R ⊓ W).2

theorem x₃_mem_W : D.x₃ ∈ W := (D.h₃ ▸ Subgroup.mem_zpowers D.x₃ : D.x₃ ∈ D.F.ρ₃.R ⊓ W).2

theorem b_mem_R : D.b ∈ D.F.ρ.R := D.F.ρ.R.pow_mem D.x₁_mem_R _

theorem b_mem_W : D.b ∈ W := W.pow_mem D.x₁_mem_W _

theorem b'_mem_R : D.b' ∈ D.F.ρ'.R := D.F.ρ'.R.pow_mem D.x₂_mem_R _

theorem b'_mem_W : D.b' ∈ W := W.pow_mem D.x₂_mem_W _

theorem u_mem_W : D.u ∈ W := W.mul_mem D.b_mem_W (W.inv_mem D.b'_mem_W)

theorem t_mem_W : t ∈ W := D.z₁ ▸ W.pow_mem D.x₁_mem_W _

theorem hzK : IsUniqueInvolution K t := by
  have := D.F.hz
  rw [D.hρK, D.hzt] at this
  exact this

theorem hzK' : IsUniqueInvolution K' t := by
  have := D.F.hz'
  rw [D.hρ'K, D.hzt] at this
  exact this

theorem b_sq : D.b * D.b = t := by
  rw [b, ← pow_add, ← two_mul, D.z₁]

theorem b'_sq : D.b' * D.b' = t := by
  rw [b', ← pow_add, ← two_mul, D.z₂]

theorem b_order : orderOf D.b = 4 := by
  have h := orderOf_pow_of_dvd (x := D.x₁) (n := D.m) (by have := D.hm; omega)
    (by rw [D.o₁]; exact dvd_mul_left D.m 4)
  rwa [D.o₁, Nat.mul_div_cancel _ D.hm] at h

theorem b'_order : orderOf D.b' = 4 := by
  have h := orderOf_pow_of_dvd (x := D.x₂) (n := D.m) (by have := D.hm; omega)
    (by rw [D.o₂]; exact dvd_mul_left D.m 4)
  rwa [D.o₂, Nat.mul_div_cancel _ D.hm] at h

theorem b_inv (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.b⁻¹ = t * D.b := by
  have h := hc t D.t_mem_W D.b D.b_mem_W
  have h2 : D.b * (t * D.b) = 1 := by
    calc D.b * (t * D.b) = D.b * (D.b * t) := by rw [h]
      _ = (D.b * D.b) * t := by group
      _ = t * t := by rw [D.b_sq]
      _ = 1 := (TwoFrame.hzK D).sq
  exact inv_eq_of_mul_eq_one_right h2

theorem b'_inv (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.b'⁻¹ = t * D.b' := by
  have h := hc t D.t_mem_W D.b' D.b'_mem_W
  have h2 : D.b' * (t * D.b') = 1 := by
    calc D.b' * (t * D.b') = D.b' * (D.b' * t) := by rw [h]
      _ = (D.b' * D.b') * t := by group
      _ = t * t := by rw [D.b'_sq]
      _ = 1 := (TwoFrame.hzK D).sq
  exact inv_eq_of_mul_eq_one_right h2

theorem u_eq (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.u = t * (D.b * D.b') := by
  rw [u, D.b'_inv hc]
  have h := hc t D.t_mem_W D.b D.b_mem_W
  calc D.b * (t * D.b') = (D.b * t) * D.b' := by group
    _ = (t * D.b) * D.b' := by rw [h]
    _ = t * (D.b * D.b') := by group

theorem tu_eq (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : t * D.u = D.b * D.b' := by
  rw [D.u_eq hc, ← mul_assoc, (TwoFrame.hzK D).sq, one_mul]

theorem r_b : D.F.ρ.r * D.b * D.F.ρ.r⁻¹ = D.b⁻¹ := by
  rw [b, ← conj_pow, D.r₁, inv_pow]

theorem r_b' : D.F.ρ.r * D.b' * D.F.ρ.r⁻¹ = D.b' := by
  rw [b', ← conj_pow, D.r₂]

theorem s_b (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    D.F.ρ₃.r * D.b * D.F.ρ₃.r⁻¹ = D.b * D.b₃ := by
  rw [b, b₃, ← conj_pow, D.s₁]
  exact Commute.mul_pow (hc _ D.x₁_mem_W _ D.x₃_mem_W) _

theorem s_b' (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    D.F.ρ₃.r * D.b' * D.F.ρ₃.r⁻¹ = D.b' * D.b₃ := by
  rw [b', b₃, ← conj_pow, D.s₂]
  exact Commute.mul_pow (hc _ D.x₂_mem_W _ D.x₃_mem_W) _

theorem s_u (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    D.F.ρ₃.r * D.u * D.F.ρ₃.r⁻¹ = D.u := by
  have e1 : D.F.ρ₃.r * D.u * D.F.ρ₃.r⁻¹ =
      (D.F.ρ₃.r * D.b * D.F.ρ₃.r⁻¹) * (D.F.ρ₃.r * D.b' * D.F.ρ₃.r⁻¹)⁻¹ := by
    rw [u]; group
  rw [e1, D.s_b hc, D.s_b' hc, u]
  group

theorem r_u (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    D.F.ρ.r * D.u * D.F.ρ.r⁻¹ = t * D.u := by
  have e1 : D.F.ρ.r * D.u * D.F.ρ.r⁻¹ =
      (D.F.ρ.r * D.b * D.F.ρ.r⁻¹) * (D.F.ρ.r * D.b' * D.F.ρ.r⁻¹)⁻¹ := by
    rw [u]; group
  rw [e1, D.r_b, D.r_b', D.tu_eq hc, D.b_inv hc, D.b'_inv hc]
  have h := hc t D.t_mem_W D.b D.b_mem_W
  calc (t * D.b) * (t * D.b') = t * (D.b * t) * D.b' := by group
    _ = t * (t * D.b) * D.b' := by rw [← h]
    _ = (t * t) * (D.b * D.b') := by group
    _ = D.b * D.b' := by rw [(TwoFrame.hzK D).sq, one_mul]

theorem r_mem_K : D.F.ρ.r ∈ K := by
  have := D.F.ρ.hRK.1 D.F.ρ.hr
  rwa [D.hρK] at this

theorem r_t : D.F.ρ.r * t = t * D.F.ρ.r := ((TwoFrame.hzK D).commute_of_mem D.r_mem_K).symm

theorem r'_mem_K' : D.F.ρ'.r ∈ K' := by
  have := D.F.ρ'.hRK.1 D.F.ρ'.hr
  rwa [D.hρ'K] at this

theorem inv_cases (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (hK : K ∈ Ω) (hK'tw : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) {a : Y} (haK : a ∈ K ⊔ K') (haW : a ∈ W) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hat : a ≠ t) : a = D.u ∨ a = t * D.u := by
  have hc := WTool.comm_of_mem_wSet hΩ hW
  have hR : IsSylow2In D.F.ρ.R K := by
    have := D.F.ρ.hRK
    rwa [D.hρK] at this
  have hR' : IsSylow2In D.F.ρ'.R K' := by
    have := D.F.ρ'.hRK
    rwa [D.hρ'K] at this
  rcases CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.involution_cases_of hΩ hK hK'tw hne
      (TwoFrame.hzK D) hR hR' D.hρS D.hρ'S D.b_mem_R D.b'_mem_R D.b_order D.b'_order haK
      (D.hWS haW) ha2 ha1 hat (hc _ haW _ D.b_mem_W) (hc _ haW _ D.b'_mem_W) with h | h
  · right
    rw [h, D.tu_eq hc]
  · left
    rw [h, D.u_eq hc]

end TwoFrame

end Alg

end Two

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
