module

public import CFSG.LargeExtraspecial.AS62Y

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup AS62.Sem

namespace AS62

variable {G : Type} [Group G] [Finite G]

namespace YCon

variable {S : Setting G} {H : Subgroup G} {F : Frame G}

omit [Finite G] in
theorem conj_tet {t e y : G} (he2 : e * e = 1)
    (hy₁ : MulAut.conj y (t * e * t * e) = S.z * e) (hy₂ : MulAut.conj y e = t * e * t) :
    MulAut.conj y (t * e * t) = S.z * e * (t * e * t) := by
  have h : t * e * t = t * e * t * e * e := by rw [mul_assoc (t * e * t), he2, mul_one]
  calc MulAut.conj y (t * e * t) = MulAut.conj y (t * e * t * e * e) := by rw [← h]
    _ = S.z * e * (t * e * t) := by rw [map_mul, hy₁, hy₂]

theorem exists_y_cube (hF : IsFrameOf S H F) (hc : ConfHyp S H)
    (hMbar : Nat.card S.Mbar = 18 ∨ Nat.card S.Mbar = 36)
    {t e x : G} (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) :
    ∃ y ∈ S.M, y * x = x * y ∧ y * (t * e * t * e) * y⁻¹ = S.z * e ∧
      y * e * y⁻¹ = t * e * t ∧ y * y * y = 1 := by
  obtain ⟨y₀, hy₀M, hy₀x, hy₁, hy₂⟩ := exists_conj_alpha0 hF hc hMbar ht he hx
  have hz := hF.rep_z
  have hbQ := b1_mem_QG hF hc ht he
  have heQ := hF.mem_QG_of_rep_eD hc he
  have hy₀z : y₀ * S.z = S.z * y₀ := S.mem_M_iff.mp hy₀M
  have c1 : MulAut.conj y₀ (t * e * t * e) = S.z * e := hy₁
  have c2 : MulAut.conj y₀ e = t * e * t := hy₂
  have c3 : MulAut.conj y₀ S.z = S.z := by
    rw [MulAut.conj_apply, hy₀z, mul_inv_cancel_right]
  have c4 := conj_tet (mul_self_of_rep_eD he) c1 c2
  have c5 : MulAut.conj y₀ (S.z * e) = S.z * (t * e * t) := by rw [map_mul, c3, c2]
  have c6 : MulAut.conj y₀ (S.z * (t * e * t)) = S.z * (S.z * e * (t * e * t)) := by
    rw [map_mul, c3, c4]
  have c7 : MulAut.conj y₀ (S.z * e * (t * e * t)) =
      S.z * (t * e * t) * (S.z * e * (t * e * t)) := by
    rw [map_mul, c5, c4]
  have k1 : MulAut.conj (y₀ ^ 3) (t * e * t * e) = t * e * t * e := by
    rw [map_pow, pow_three, MulAut.mul_apply, MulAut.mul_apply, c1, c5, c6,
      ← mul_assoc S.z (S.z * e) (t * e * t)]
    exact F.I1 hz ht he
  have k2 : MulAut.conj (y₀ ^ 3) e = e := by
    rw [map_pow, pow_three, MulAut.mul_apply, MulAut.mul_apply, c2, c4, c7,
      ← mul_assoc (S.z * (t * e * t)) (S.z * e) (t * e * t)]
    exact F.I2 hz ht he
  rw [MulAut.conj_apply] at k1 k2
  rcases eq_one_or_z_of_commute_gens hF hc ht he hx (pow_mem hy₀M 3)
      (mul_inv_eq_iff_eq_mul.mp k1) (mul_inv_eq_iff_eq_mul.mp k2)
      (Commute.pow_left (show Commute y₀ x from hy₀x) 3).eq with h3 | h3
  · exact ⟨y₀, hy₀M, hy₀x, hy₁, hy₂, by rw [← pow_three', h3]⟩
  · have hxz : x * S.z = S.z * x := S.mem_M_iff.mp (hF.mem_M_of_rep_xD hx)
    refine ⟨y₀ * S.z, mul_mem hy₀M S.z_mem_M, ?_, ?_, ?_, ?_⟩
    · calc y₀ * S.z * x = y₀ * (x * S.z) := by rw [mul_assoc, hxz]
        _ = x * (y₀ * S.z) := by rw [← mul_assoc, hy₀x, mul_assoc]
    · calc y₀ * S.z * (t * e * t * e) * (y₀ * S.z)⁻¹ =
            y₀ * (S.z * (t * e * t * e)) * S.z⁻¹ * y₀⁻¹ := by group
        _ = y₀ * (t * e * t * e * S.z) * S.z⁻¹ * y₀⁻¹ := by rw [S.z_comm_QG hbQ]
        _ = y₀ * (t * e * t * e) * y₀⁻¹ := by group
        _ = S.z * e := hy₁
    · calc y₀ * S.z * e * (y₀ * S.z)⁻¹ = y₀ * (S.z * e) * S.z⁻¹ * y₀⁻¹ := by group
        _ = y₀ * (e * S.z) * S.z⁻¹ * y₀⁻¹ := by rw [S.z_comm_QG heQ]
        _ = y₀ * e * y₀⁻¹ := by group
        _ = t * e * t := hy₂
    · calc y₀ * S.z * (y₀ * S.z) * (y₀ * S.z) = (y₀ * S.z) ^ 3 := (pow_three' _).symm
        _ = y₀ ^ 3 * S.z ^ 3 := (show Commute y₀ S.z from hy₀z).mul_pow 3
        _ = S.z * S.z * (S.z * S.z) := by
            rw [h3, pow_three']
            simp only [mul_assoc]
        _ = 1 := by rw [S.z_mul_z, one_mul]

theorem t_mul_y_sq (hF : IsFrameOf S H F) (hc : ConfHyp S H) {t e x y : G} (ht : F.Rep t tD)
    (he : F.Rep e eD) (hx : F.Rep x xD) (hyM : y ∈ S.M) (hyx : y * x = x * y)
    (hy₁ : y * (t * e * t * e) * y⁻¹ = S.z * e) (hy₂ : y * e * y⁻¹ = t * e * t)
    (hy3 : y * y * y = 1) : t * y * t * y = 1 := by
  have hz := hF.rep_z
  have ht2 := mul_self_of_rep_tD ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htz : t * S.z = S.z * t := commute_of_rep ht hz (by decide +kernel)
  have htM : t ∈ S.M := S.mem_M_iff.mpr htz
  have hxt : x * t = t * x := commute_of_rep hx ht (by decide +kernel)
  have cy1 : MulAut.conj y (t * e * t * e) = S.z * e := hy₁
  have cy2 : MulAut.conj y e = t * e * t := hy₂
  have cy3 : MulAut.conj y S.z = S.z := by
    rw [MulAut.conj_apply, S.mem_M_iff.mp hyM, mul_inv_cancel_right]
  have cy4 := conj_tet (mul_self_of_rep_eD he) cy1 cy2
  have ct1 : MulAut.conj t (t * e * t * e) = t * e * t * e := by
    rw [MulAut.conj_apply, htinv]
    exact t_mul_b1_mul_t ht he
  have ct2 : MulAut.conj t e = t * e * t := by rw [MulAut.conj_apply, htinv]
  have ct3 : MulAut.conj t (S.z * e) = S.z * (t * e * t) := by
    rw [MulAut.conj_apply, htinv]
    exact F.I3 hz ht he
  have ct4 : MulAut.conj t (S.z * e * (t * e * t)) = S.z * e * (t * e * t) := by
    rw [MulAut.conj_apply, htinv]
    exact F.I4 hz ht he
  have hw : MulAut.conj (t * y * t) = MulAut.conj t * MulAut.conj y * MulAut.conj t := by
    rw [map_mul, map_mul]
  have hyy : MulAut.conj (y * y) = MulAut.conj y * MulAut.conj y := map_mul _ _ _
  have k1 : t * y * t * (t * e * t * e) * (t * y * t)⁻¹ =
      y * y * (t * e * t * e) * (y * y)⁻¹ := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, hw, hyy]
    simp only [MulAut.mul_apply]
    rw [ct1, cy1, ct3, map_mul, cy3, cy2]
  have k2 : t * y * t * e * (t * y * t)⁻¹ = y * y * e * (y * y)⁻¹ := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, hw, hyy]
    simp only [MulAut.mul_apply]
    rw [ct2, cy4, ct4, cy2, cy4]
  have hwx : t * y * t * x = x * (t * y * t) :=
    calc t * y * t * x = t * y * (x * t) := by rw [mul_assoc (t * y), ← hxt]
      _ = t * (x * y) * t := by rw [← mul_assoc, mul_assoc t y x, hyx]
      _ = x * (t * y * t) := by rw [← mul_assoc, ← hxt]; group
  have hyyx : y * y * x = x * (y * y) :=
    calc y * y * x = y * (x * y) := by rw [mul_assoc, hyx]
      _ = x * (y * y) := by rw [← mul_assoc, hyx, mul_assoc]
  rcases eq_or_eq_mul_z hF hc ht he hx (mul_mem (mul_mem htM hyM) htM) hwx
      (mul_mem hyM hyM) hyyx k1 k2 with h | h
  · rw [h]
    exact hy3
  · exfalso
    have h1 : t * y * t * (t * y * t) * (t * y * t) = 1 :=
      calc t * y * t * (t * y * t) * (t * y * t) = t * y * (t * t) * y * (t * t) * y * t := by
            simp only [mul_assoc]
        _ = t * (y * y * y) * t := by
            rw [ht2]
            simp only [mul_one, mul_assoc]
        _ = 1 := by rw [hy3, mul_one, ht2]
    rw [h, cube_mul_mul_eq (S.mem_M_iff.mp hyM) hy3 S.z_mul_z] at h1
    exact S.z_ne_one h1

omit [Finite G] in
theorem not_mem_H (hF : IsFrameOf S H F) {t e y : G} (ht : F.Rep t tD) (he : F.Rep e eD)
    (hy₁ : y * (t * e * t * e) * y⁻¹ = S.z * e) : y ∉ H := by
  intro hyH
  obtain ⟨dy, hy⟩ := F.rep_exists (hF.H_eq ▸ hyH)
  have hze : F.Rep (y * (t * e * t * e) * y⁻¹) zeD := by
    rw [hy₁]
    exact F.rep_ze hF.rep_z he
  have h := congrArg Prod.snd
    (F.rep_unique (F.rep_mul (F.rep_mul hy (F.rep_b1 ht he)) (F.rep_inv hy)) hze)
  obtain ⟨-, a, ha, -⟩ := hy
  change compN (compN dy.2 b1D.2) (invN dy.2) = zeD.2 at h
  rw [← ha, show b1D.2 = 1234 by decide +kernel, ← permCode_one, compN_permCode, invN_permCode,
    compN_permCode, mul_one, mul_inv_cancel, permCode_one] at h
  exact absurd h (by decide +kernel)

end YCon

namespace IsFrameOf

variable {S : Setting G} {H : Subgroup G} {F : Frame G}

theorem exists_y (hF : IsFrameOf S H F) (hc : ConfHyp S H)
    (hMbar : Nat.card S.Mbar = 18 ∨ Nat.card S.Mbar = 36)
    {t e x : G} (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) :
    ∃ y : G, y ∈ S.M ∧ y ∉ H ∧ y * y * y = 1 ∧ x * y = y * x ∧ t * y * t * y = 1 ∧
      y * (t * e * t * e) * y⁻¹ = S.z * e ∧ y * e * y⁻¹ = t * e * t := by
  obtain ⟨y, hyM, hyx, hy₁, hy₂, hy3⟩ := YCon.exists_y_cube hF hc hMbar ht he hx
  exact ⟨y, hyM, YCon.not_mem_H hF ht he hy₁, hy3, hyx.symm,
    YCon.t_mul_y_sq hF hc ht he hx hyM hyx hy₁ hy₂ hy3, hy₁, hy₂⟩

end IsFrameOf

end AS62

end CFSG.LargeExtraspecial
