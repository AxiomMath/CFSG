module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL22B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S]

private lemma fzl_mul_mul_central {z : S} (hz : z ∈ center S) (g h x : S) :
    (g * z) * (h * x) = (g * h) * (z * x) := by
  rw [mul_assoc g z (h * x), ← mul_assoc z h x, ← (Subgroup.mem_center_iff.mp hz) h,
    mul_assoc h z x, ← mul_assoc g h (z * x)]

private lemma fzl_gam_mul_central_right (hS : FzSuz S) {z : S} (hz : z ∈ center S) (g h : S) :
    ⁅g, h * z⁆ = ⁅g, h⁆ := by
  rw [fzl_gam_symm hS g (h * z), fzl_gam_mul_central hS hz h g, fzl_gam_symm hS h g]

private lemma fzl_sq_inv (hS : FzSuz S) (g : S) : g⁻¹ * g⁻¹ = g * g := by
  rw [← mul_inv_rev]
  exact fzl_center_inv hS (hS.sq_central g)

theorem fzl_no_sigma3 (hS : FzSuz S) (f u : MulAut S) (hf3 : f ^ 3 = 1)
    (hfix : ∀ g : S, f g = g → g = 1) (hu2 : u * u = 1) (huf : u * f * u⁻¹ = f⁻¹) : False := by
  obtain ⟨z₁, z₂, z₃, hZ1, hZ2, hZ3, hz1ne, _, hz3ne, hz12, _, hz23, hz3eq, hZall,
    huz1, huz2, huz3, hfz1, hfz2, hfz3⟩ := fzl_Z_structure hS f u hf3 hfix hu2 huf
  obtain ⟨a, c, ha_u, hc_u, haZ, hcZ, hacZ⟩ := fzl_exists_fixed_pair hS u hu2
  have hz1sq : z₁ * z₁ = 1 := hS.center_exp z₁ hZ1
  have hz2sq : z₂ * z₂ = 1 := hS.center_exp z₂ hZ2
  have hz3sq : z₃ * z₃ = 1 := hS.center_exp z₃ hZ3
  have fixZ : ∀ z ∈ center S, u z = z → z = 1 ∨ z = z₁ := by
    intro z hz huz
    rcases hZall z hz with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [h] at huz
      rw [huz2] at huz
      exact hz23 huz.symm
    · exfalso
      rw [h] at huz
      rw [huz3] at huz
      exact hz23 huz
  have hua : u a = a * (u a * a⁻¹) := by
    calc u a = (u a * a⁻¹) * a := by group
      _ = a * (u a * a⁻¹) := ((Subgroup.mem_center_iff.mp ha_u) a).symm
  have huc : u c = c * (u c * c⁻¹) := by
    calc u c = (u c * c⁻¹) * c := by group
      _ = c * (u c * c⁻¹) := ((Subgroup.mem_center_iff.mp hc_u) c).symm
  have hu_aa : u (a * a) = a * a := by
    rw [map_mul u a a, hua, fzl_sq_mul_central hS ha_u a]
  have haa : a * a = z₁ := by
    rcases fixZ (a * a) (hS.sq_central a) hu_aa with h | h
    · exact absurd (hS.aniso a h) haZ
    · exact h
  have hu_cc : u (c * c) = c * c := by
    rw [map_mul u c c, huc, fzl_sq_mul_central hS hc_u c]
  have hcc : c * c = z₁ := by
    rcases fixZ (c * c) (hS.sq_central c) hu_cc with h | h
    · exact absurd (hS.aniso c h) hcZ
    · exact h
  have hdd : f c * f c = z₂ := by
    rw [← map_mul f c c, hcc, hfz1]
  have hacZ' : a * c ∉ center S := by
    intro hac
    apply hacZ
    have hc_inv : c⁻¹ = c * z₁ := by
      calc c⁻¹ = c * (c * c)⁻¹ := by group
        _ = c * z₁ := by rw [hcc, fzl_center_inv hS hZ1]
    have hprod : a * c⁻¹ = (a * c) * z₁ := by
      rw [hc_inv]
      group
    rw [hprod]
    exact mul_mem hac hZ1
  have hu_ac_eq : u (a * c) = (a * c) * ((u a * a⁻¹) * (u c * c⁻¹)) := by
    calc u (a * c) = u a * u c := map_mul u a c
      _ = (a * (u a * a⁻¹)) * (c * (u c * c⁻¹)) := by
            conv_lhs => rw [hua, huc]
      _ = (a * c) * ((u a * a⁻¹) * (u c * c⁻¹)) :=
            fzl_mul_mul_central ha_u a c (u c * c⁻¹)
  have hζZ : (u a * a⁻¹) * (u c * c⁻¹) ∈ center S := mul_mem ha_u hc_u
  have hu_acac : u ((a * c) * (a * c)) = (a * c) * (a * c) := by
    rw [map_mul u (a * c) (a * c), hu_ac_eq, fzl_sq_mul_central hS hζZ (a * c)]
  have hacac : (a * c) * (a * c) = z₁ := by
    rcases fixZ ((a * c) * (a * c)) (hS.sq_central (a * c)) hu_acac with h | h
    · exact absurd (hS.aniso (a * c) h) hacZ'
    · exact h
  have hac_comm : ⁅a, c⁆ = z₁ := by
    have h := fzl_sq_mul hS a c
    rw [hacac, haa, hcc, hz1sq, one_mul] at h
    exact h.symm
  have hadZ : a * f c ∉ center S := by
    intro h
    have hz : a * f c ∈ center S := h
    have ha_eq : a = (f c)⁻¹ * (a * f c) := by
      calc a = (a * f c) * (f c)⁻¹ := by group
        _ = (f c)⁻¹ * (a * f c) := ((Subgroup.mem_center_iff.mp hz) (f c)⁻¹).symm
    have hq : a * a = (f c)⁻¹ * (f c)⁻¹ := by
      rw [ha_eq, fzl_sq_mul_central hS hz (f c)⁻¹]
    have h12' : z₁ = z₂ := by
      rw [← haa, hq, fzl_sq_inv hS (f c), hdd]
    exact hz12 h12'
  have hf_inv_mul : f⁻¹ = f * f := by
    rw [inv_eq_iff_mul_eq_one]
    rw [← pow_two, ← pow_succ' f 2]
    exact hf3
  have hf_inv_apply : ∀ x : S, f⁻¹ x = f (f x) := by
    intro x
    rw [hf_inv_mul, MulAut.mul_apply]
  have huf' : u * f = f⁻¹ * u := by
    rw [← huf]
    group
  have huf_apply : ∀ x : S, u (f x) = f⁻¹ (u x) := by
    intro x
    have h := congrArg (fun e : MulAut S => e x) huf'
    simpa only [MulAut.mul_apply] using h
  have hab : ⁅a, f a⁆ = 1 := fzl_comm_f_self hS f hf3 hfix a
  have hcd : ⁅c, f c⁆ = 1 := fzl_comm_f_self hS f hf3 hfix c
  have h_mixed : ⁅a, f c⁆ = ⁅f a, c⁆ := by
    have h := fzl_comm_f_self hS f hf3 hfix (a * c)
    rw [map_mul f a c] at h
    simp only [fzl_gam_mul_left hS, fzl_gam_mul_right hS] at h
    rw [hab, hcd, mul_one, one_mul] at h
    have h' : ⁅a, f c⁆ * ⁅f a, c⁆ = 1 := by
      rw [← fzl_gam_symm hS c (f a)]
      exact h
    have hy2 : ⁅f a, c⁆ * ⁅f a, c⁆ = 1 := hS.center_exp _ (hS.comm_central (f a) c)
    calc ⁅a, f c⁆ = ⁅a, f c⁆ * 1 := (mul_one _).symm
      _ = ⁅a, f c⁆ * (⁅f a, c⁆ * ⁅f a, c⁆) := by rw [hy2]
      _ = (⁅a, f c⁆ * ⁅f a, c⁆) * ⁅f a, c⁆ := by group
      _ = 1 * ⁅f a, c⁆ := by rw [h']
      _ = ⁅f a, c⁆ := one_mul _
  have h_bd : ⁅f a, f c⁆ = z₂ := by
    rw [← map_commutatorElement f a c, hac_comm, hfz1]
  have h_fdc : f (f c) * (c * f c) ∈ center S := by
    have h0 := fzl_norm_central hS f hf3 hfix c
    have hid : f (f c) = (c * f c)⁻¹ * (c * f c * f (f c)) := by group
    rw [hid, mul_assoc, ← (Subgroup.mem_center_iff.mp h0) (c * f c),
      ← mul_assoc, inv_mul_cancel, one_mul]
    exact h0
  have hud_eq : u (f c) = f (f c) * f⁻¹ (u c * c⁻¹) := by
    calc u (f c) = f⁻¹ (u c) := huf_apply c
      _ = f⁻¹ (c * (u c * c⁻¹)) := by conv_lhs => rw [huc]
      _ = f⁻¹ c * f⁻¹ (u c * c⁻¹) := map_mul (f⁻¹) c (u c * c⁻¹)
      _ = f (f c) * f⁻¹ (u c * c⁻¹) := by rw [hf_inv_apply c]
  have hζcZ : f⁻¹ (u c * c⁻¹) ∈ center S := fzl_map_center (f⁻¹) hc_u
  have hud_cd : u (f c) * (c * f c) ∈ center S := by
    have heq : u (f c) * (c * f c) = (f (f c) * (c * f c)) * f⁻¹ (u c * c⁻¹) := by
      rw [hud_eq, mul_assoc, ← (Subgroup.mem_center_iff.mp hζcZ) (c * f c), ← mul_assoc]
    rw [heq]
    exact mul_mem h_fdc hζcZ
  have hud_eq2 : u (f c) = (c * f c)⁻¹ * (u (f c) * (c * f c)) := by
    rw [(Subgroup.mem_center_iff.mp hud_cd) (c * f c)⁻¹]
    group
  have hwZ : ⁅a, f c⁆ ∈ center S := hS.comm_central a (f c)
  have huw : u ⁅a, f c⁆ = z₁ * ⁅a, f c⁆ := by
    have h1 : u ⁅a, f c⁆ = ⁅u a, u (f c)⁆ := map_commutatorElement u a (f c)
    rw [h1, hua, fzl_gam_mul_central hS ha_u a (u (f c))]
    rw [hud_eq2, fzl_gam_mul_central_right hS hud_cd a ((c * f c)⁻¹)]
    rw [fzl_gam_inv_right hS, fzl_gam_mul_right hS, hac_comm]
  have hw_cases : ⁅a, f c⁆ = z₂ ∨ ⁅a, f c⁆ = z₃ := by
    rcases hZall ⁅a, f c⁆ hwZ with h | h | h | h
    · exfalso
      rw [h] at huw
      simp only [map_one, mul_one] at huw
      exact hz1ne huw.symm
    · exfalso
      rw [h, huz1, hz1sq] at huw
      exact hz1ne huw
    · exact Or.inl h
    · exact Or.inr h
  have hqad : (a * f c) * (a * f c) = z₃ * ⁅a, f c⁆ := by
    rw [fzl_sq_mul hS a (f c), haa, hdd, ← hz3eq]
  have hqad_ne : z₃ * ⁅a, f c⁆ ≠ 1 := by
    intro h
    have h1 : (a * f c) * (a * f c) = 1 := by rw [hqad, h]
    exact hadZ (hS.aniso (a * f c) h1)
  have hw2 : ⁅a, f c⁆ = z₂ := by
    rcases hw_cases with h | h
    · exact h
    · exfalso
      apply hqad_ne
      rw [h, hz3sq]
  have hfw : f ⁅a, f c⁆ = ⁅a, f c⁆ * z₂ := by
    have h1 : f ⁅a, f c⁆ = ⁅f a, f (f c)⁆ := map_commutatorElement f a (f c)
    have hid : f (f c) = (c * f c)⁻¹ * (f (f c) * (c * f c)) := by
      rw [(Subgroup.mem_center_iff.mp h_fdc) (c * f c)⁻¹]
      group
    rw [h1, hid, fzl_gam_mul_central_right hS h_fdc (f a) ((c * f c)⁻¹)]
    rw [fzl_gam_inv_right hS, fzl_gam_mul_right hS, ← h_mixed, h_bd]
  have hcontra : z₃ = 1 := by
    calc z₃ = f z₂ := hfz2.symm
      _ = f ⁅a, f c⁆ := by rw [hw2]
      _ = ⁅a, f c⁆ * z₂ := hfw
      _ = z₂ * z₂ := by rw [hw2]
      _ = 1 := hz2sq
  exact hz3ne hcontra

end CFSG.OddStandard.SmallF3.FritzII
