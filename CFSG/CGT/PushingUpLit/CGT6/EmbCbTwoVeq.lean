module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoFix

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V] {Y : Subgroup (MulAut V)} {m : ℕ}
  {G T : Subgroup (MulAut V)} {t : MulAut V} {X₁ X₂ : Subgroup (MulAut V)}

omit [Finite V] in
private theorem cbv_vvec_sq {C : CbtY Y m} {X : Subgroup (MulAut V)} (L : CbtLift C t X)
    (hV : ∀ v : V, v ^ 2 = 1) : L.vvec * L.vvec = 1 := by
  unfold CbtLift.vvec
  rw [mul_mul_mul_comm, L.D.w_sq hV, L.D.w_sq hV, mul_one]

theorem CbtCtx.V_eq (K : CbtCtx G T Y t m X₁ X₂) (hv₂ : K.L₂.vvec ∈ fixV X₁)
    (hzv₂ : K.L₂.zvec * K.L₁.vvec ∈ fixV X₁) (hv₁ : K.L₁.vvec ∈ fixV X₂)
    (_hzv₁ : K.L₁.zvec * K.L₂.vvec ∈ fixV X₂) :
    (commV X₁ ⊔ commV X₂) ⊔ (fixV X₁ ⊓ fixV X₂) = ⊤ := by
  classical
  have hm := K.hm
  have hodd := K.hodd
  have hV := K.hV
  refine eq_top_iff.mpr fun v _ => ?_
  have hs₁ : v ∈ commV X₁ ⊔ fixV X₁ := by rw [(K.L₁.D.split hm hodd).1]; trivial
  obtain ⟨w₁, hw₁, f, hf, rfl⟩ := Subgroup.mem_sup.mp hs₁
  have hs₂ : f ∈ commV X₂ ⊔ fixV X₂ := by rw [(K.L₂.D.split hm hodd).1]; trivial
  obtain ⟨w₂, hw₂, g, hg, hfg⟩ := Subgroup.mem_sup.mp hs₂
  have hw₂Y : ∀ y ∈ Y, y w₂ = w₂ := by
    intro y hy
    have h1 : y f = f := mem_fixV.mp hf y (K.L₁.hYX hy)
    have h2 : y g = g := mem_fixV.mp hg y (K.L₂.hYX hy)
    have h3 : w₂ = f * g⁻¹ := by
      rw [← hfg]
      group
    rw [h3, map_mul, map_inv, h1, h2]
  have hz₂W : K.L₂.zvec ∈ commV X₂ := (K.L₂.D.hwmem K.L₂.D.b).1
  have hv₁W : K.L₁.vvec ∈ commV X₁ :=
    mul_mem (K.L₁.D.hwmem K.L₁.D.a).1 (K.L₁.D.hwmem K.L₁.D.b).1
  have hv₂W : K.L₂.vvec ∈ commV X₂ :=
    mul_mem (K.L₂.D.hwmem K.L₂.D.a).1 (K.L₂.D.hwmem K.L₂.D.b).1
  have hz₂S : K.L₂.zvec ∈ commV X₁ ⊔ commV X₂ := Subgroup.mem_sup_right hz₂W
  have hv₁S : K.L₁.vvec ∈ commV X₁ ⊔ commV X₂ := Subgroup.mem_sup_left hv₁W
  have hv₂S : K.L₂.vvec ∈ commV X₁ ⊔ commV X₂ := Subgroup.mem_sup_right hv₂W
  have hv₁sq := cbv_vvec_sq K.L₁ hV
  have hw2b : K.L₂.D.w K.L₂.D.b * K.L₂.D.w K.L₂.D.b = 1 := K.L₂.D.w_sq hV _
  have hv2def : K.L₂.vvec = K.L₂.D.w K.L₂.D.a * K.L₂.D.w K.L₂.D.b := rfl
  have hz2def : K.L₂.zvec = K.L₂.D.w K.L₂.D.b := rfl
  have hwa : K.L₂.D.w K.L₂.D.a = K.L₂.zvec * K.L₂.vvec := by
    rw [hz2def, hv2def]
    calc K.L₂.D.w K.L₂.D.a = K.L₂.D.w K.L₂.D.a * (K.L₂.D.w K.L₂.D.b * K.L₂.D.w K.L₂.D.b) := by
          rw [hw2b, mul_one]
      _ = K.L₂.D.w K.L₂.D.b * (K.L₂.D.w K.L₂.D.a * K.L₂.D.w K.L₂.D.b) := by ac_rfl
  have key : ∃ f' g' : V, f' ∈ fixV X₁ ∧ f' ∈ commV X₁ ⊔ commV X₂ ∧ g' ∈ fixV X₂ ∧
      w₂ = f' * g' := by
    rcases cbtFixY_mem K.L₂.D hm hodd K.L₂.hYX hw₂ hw₂Y with h | h | h | h
    · exact ⟨1, 1, one_mem _, one_mem _, one_mem _, by rw [h, mul_one]⟩
    ·
      refine ⟨K.L₂.zvec * K.L₁.vvec * K.L₂.vvec, K.L₁.vvec, mul_mem hzv₂ hv₂,
        mul_mem (mul_mem hz₂S hv₁S) hv₂S, hv₁, ?_⟩
      rw [h, hwa]
      calc K.L₂.zvec * K.L₂.vvec = K.L₂.zvec * K.L₂.vvec * (K.L₁.vvec * K.L₁.vvec) := by
            rw [hv₁sq, mul_one]
        _ = K.L₂.zvec * K.L₁.vvec * K.L₂.vvec * K.L₁.vvec := by ac_rfl
    ·
      refine ⟨K.L₂.zvec * K.L₁.vvec, K.L₁.vvec, hzv₂, mul_mem hz₂S hv₁S, hv₁, ?_⟩
      rw [h]
      calc K.L₂.D.w K.L₂.D.b = K.L₂.zvec * (K.L₁.vvec * K.L₁.vvec) := by
            rw [hv₁sq, mul_one]
            rfl
        _ = K.L₂.zvec * K.L₁.vvec * K.L₁.vvec := by ac_rfl
    · exact ⟨K.L₂.vvec, 1, hv₂, hv₂S, one_mem _, by rw [h, mul_one]; rfl⟩
  obtain ⟨f', g', hf'F, hf'S, hg'F, hw₂eq⟩ := key
  have hR : f * f'⁻¹ ∈ fixV X₁ ⊓ fixV X₂ := by
    have h0 : f * f'⁻¹ ∈ fixV X₁ := Subgroup.mul_mem _ hf (Subgroup.inv_mem _ hf'F)
    refine ⟨h0, ?_⟩
    have h1 : f * f'⁻¹ = g' * g := by
      rw [mul_inv_eq_iff_eq_mul, ← hfg, hw₂eq]
      ac_rfl
    rw [h1]
    exact mul_mem hg'F hg
  have hv : w₁ * f = (w₁ * f') * (f * f'⁻¹) := by
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
  rw [hv]
  exact Subgroup.mul_mem_sup (mul_mem (Subgroup.mem_sup_left hw₁) hf'S) hR

end CFSG.CGT.PushingUpLit.CGT6
