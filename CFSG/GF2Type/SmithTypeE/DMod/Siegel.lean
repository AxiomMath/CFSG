module

public import CFSG.GF2Type.SmithTypeE.DMod.V12

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

@[expose] def TsPair (u w : V12) : Prop := q12 u = 0 ∧ q12 w = 0 ∧ B12 u w = 0

@[expose] noncomputable def siegelLin (u w : V12) : V12 →ₗ[ZMod 2] V12 :=
  LinearMap.id + (B12L.flip w).smulRight u + (B12L.flip u).smulRight w

theorem smul_add_self_V12 (c : ZMod 2) (v : V12) : c • v + c • v = 0 := by
  rw [← add_smul]
  have hc : ∀ d : ZMod 2, d + d = 0 := by decide
  rw [hc c, zero_smul]

theorem siegelLin_apply (u w x : V12) :
    siegelLin u w x = x + B12 x w • u + B12 x u • w := by
  simp [siegelLin, B12L_apply, LinearMap.flip_apply]

theorem siegelLin_siegelLin {u w : V12} (h : TsPair u w) (x : V12) :
    siegelLin u w (siegelLin u w x) = x := by
  obtain ⟨hu, hw, huw⟩ := h
  have hwu : B12 w u = 0 := by rw [B12_comm]; exact huw
  have h1 : B12 (x + B12 x w • u + B12 x u • w) w = B12 x w := by
    simp only [B12_add_left, B12_smul_left, B12_self, huw, mul_zero, add_zero]
  have h2 : B12 (x + B12 x w • u + B12 x u • w) u = B12 x u := by
    simp only [B12_add_left, B12_smul_left, B12_self, hwu, mul_zero, add_zero]
  rw [siegelLin_apply, siegelLin_apply, h1, h2]
  calc x + B12 x w • u + B12 x u • w + B12 x w • u + B12 x u • w
      = x + (B12 x w • u + B12 x w • u) + (B12 x u • w + B12 x u • w) := by abel
    _ = x := by simp only [smul_add_self_V12, add_zero]

open Classical in
@[expose] noncomputable def siegelEquiv (u w : V12) : V12 ≃ₗ[ZMod 2] V12 :=
  if h : TsPair u w then LinearEquiv.ofInvolutive (siegelLin u w) (siegelLin_siegelLin h)
  else LinearEquiv.refl (ZMod 2) V12

theorem siegelLin_involutive {u w : V12} (h : TsPair u w) : Function.Involutive (siegelLin u w) :=
  siegelLin_siegelLin h

theorem siegelEquiv_eq_ofInvolutive {u w : V12} (h : TsPair u w) :
    siegelEquiv u w = LinearEquiv.ofInvolutive (siegelLin u w) (siegelLin_involutive h) := by
  rw [siegelEquiv, dif_pos h] <;> rfl

theorem siegelEquiv_apply {u w : V12} (h : TsPair u w) (x : V12) :
    siegelEquiv u w x = x + B12 x w • u + B12 x u • w := by
  rw [siegelEquiv_eq_ofInvolutive h, LinearEquiv.coe_ofInvolutive, siegelLin_apply]

theorem siegelEquiv_mul_self {u w : V12} (h : TsPair u w) :
    siegelEquiv u w * siegelEquiv u w = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, siegelEquiv_eq_ofInvolutive h]
  simp only [LinearEquiv.coe_ofInvolutive, LinearEquiv.coe_one, id_eq]
  exact siegelLin_siegelLin h x

theorem siegelEquiv_inv {u w : V12} (h : TsPair u w) : (siegelEquiv u w)⁻¹ = siegelEquiv u w :=
  inv_eq_of_mul_eq_one_right (siegelEquiv_mul_self h)

theorem q12_siegelEquiv {u w : V12} (h : TsPair u w) (x : V12) :
    q12 (siegelEquiv u w x) = q12 x := by
  rw [siegelEquiv_apply h x]
  obtain ⟨hu, hw, huw⟩ := h
  simp only [q12_add, q12_smul, B12_add_left, B12_smul_left, B12_smul_right, hu, hw, huw,
    mul_zero, zero_mul, add_zero, zero_add]
  generalize q12 x = s
  generalize B12 x w = p
  generalize B12 x u = r
  revert s p r
  decide

theorem B12_siegelEquiv {u w : V12} (h : TsPair u w) (x y : V12) :
    B12 (siegelEquiv u w x) (siegelEquiv u w y) = B12 x y := by
  have h1 := q12_add (siegelEquiv u w x) (siegelEquiv u w y)
  have h2 := q12_add x y
  rw [← map_add (siegelEquiv u w) x y] at h1
  simp only [q12_siegelEquiv h] at h1
  exact add_left_cancel (h1.symm.trans h2)

theorem siegelEquiv_swap {u w : V12} (h : TsPair u w) : siegelEquiv w u = siegelEquiv u w := by
  have hwu : TsPair w u := by
    obtain ⟨hu, hw, huw⟩ := h
    exact ⟨hw, hu, by rw [B12_comm]; exact huw⟩
  refine LinearEquiv.ext fun x => ?_
  rw [siegelEquiv_apply hwu x, siegelEquiv_apply h x]
  abel

theorem siegelEquiv_add_right {u w : V12} (h : TsPair u w) :
    siegelEquiv u (u + w) = siegelEquiv u w := by
  have h' : TsPair u (u + w) := by
    obtain ⟨hu, hw, huw⟩ := h
    exact ⟨hu, by simp [q12_add, hu, hw, huw], by simp [B12_add_right, B12_self, huw]⟩
  refine LinearEquiv.ext fun x => ?_
  rw [siegelEquiv_apply h' x, siegelEquiv_apply h x, B12_add_right, add_smul, smul_add]
  calc x + (B12 x u • u + B12 x w • u) + (B12 x u • u + B12 x u • w)
      = x + B12 x w • u + B12 x u • w + (B12 x u • u + B12 x u • u) := by abel
    _ = x + B12 x w • u + B12 x u • w := by simp only [smul_add_self_V12, add_zero]

theorem tsPair_swap {u w : V12} (h : TsPair u w) : TsPair w u := by
  obtain ⟨hu, hw, huw⟩ := h
  exact ⟨hw, hu, by rw [B12_comm]; exact huw⟩

theorem B12_of_isometry {g : V12 ≃ₗ[ZMod 2] V12} (hg : ∀ x, q12 (g x) = q12 x) (x y : V12) :
    B12 (g x) (g y) = B12 x y := by
  have h1 := q12_add (g x) (g y)
  have h2 := q12_add x y
  rw [← map_add g x y, hg (x + y), hg x, hg y] at h1
  linear_combination h2 - h1

theorem tsPair_map {g : V12 ≃ₗ[ZMod 2] V12} (hg : ∀ x, q12 (g x) = q12 x) {u w : V12}
    (h : TsPair u w) : TsPair (g u) (g w) := by
  obtain ⟨hu, hw, huw⟩ := h
  exact ⟨(hg u).trans hu, (hg w).trans hw, (B12_of_isometry hg u w).trans huw⟩

theorem conj_siegelEquiv {g : V12 ≃ₗ[ZMod 2] V12} (hg : ∀ x, q12 (g x) = q12 x) {u w : V12}
    (h : TsPair u w) : g * siegelEquiv u w * g⁻¹ = siegelEquiv (g u) (g w) := by
  refine LinearEquiv.ext fun y => ?_
  have hgy : g (g⁻¹ y) = y := by simp
  have hB1 : B12 (g⁻¹ y) w = B12 y (g w) := by
    rw [← B12_of_isometry hg (g⁻¹ y) w, hgy]
  have hB2 : B12 (g⁻¹ y) u = B12 y (g u) := by
    rw [← B12_of_isometry hg (g⁻¹ y) u, hgy]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, siegelEquiv_apply h,
    siegelEquiv_apply (tsPair_map hg h), map_add, map_add, map_smul, map_smul, hgy, hB1, hB2]

theorem siegelEquiv_mem_isometries {u w : V12} (h : TsPair u w) :
    siegelEquiv u w ∈ CFSG.Open.timmesfeldIsometries q12 := by
  show ∀ v, q12 (siegelEquiv u w v) = q12 v
  exact fun v => q12_siegelEquiv h v

theorem tsPair_dec12 {u w : Nat} (hu : qf u = false) (hw : qf w = false) (huw : bf u w = false) :
    TsPair (dec12 u) (dec12 w) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [q12_dec12, hu, bit]
  · simp [q12_dec12, hw, bit]
  · simp [B12_dec12, huw, bit]

theorem siegelEquiv_dec12 {u w : Nat} (hu : qf u = false) (hw : qf w = false)
    (huw : bf u w = false) (x : Nat) :
    siegelEquiv (dec12 u) (dec12 w) (dec12 x) = dec12 (sgl u w x) := by
  rw [siegelEquiv_apply (tsPair_dec12 hu hw huw), B12_dec12, B12_dec12]
  unfold sgl
  cases hb : bf x w <;> cases hb' : bf x u <;> simp [bit, dec12_xor, dec12_zero, hb, hb']

end CFSG.GF2Type.SmithTypeE.DMod
