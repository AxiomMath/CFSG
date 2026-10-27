module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAbSigma3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutSpecial

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

variable {T : Type} [Group T] [Finite T] {ρ x : MulAut T}

private theorem sq_eq_one_quot (hS : FpfSpecial T) (v : T ⧸ center T) : v * v = 1 := by
  induction v using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hS.sq_mem g

private theorem aut_apply_self (hx : x * x = 1) (g : T) : x (x g) = g := by
  have h := congrArg (fun f : MulAut T => f g) hx
  simpa [MulAut.mul_apply] using h

private theorem aut_rho_apply (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) (g : T) :
    x (ρ g) = ρ⁻¹ (x g) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h : x * ρ = ρ⁻¹ * x := by
    have h2 := congrArg (fun f : MulAut T => f * x) hxρ
    rw [hxinv] at h2
    simpa [mul_assoc, hx] using h2
  have h3 := congrArg (fun f : MulAut T => f g) h
  simpa [MulAut.mul_apply] using h3

private theorem rho_inv_apply (hρ : ρ ^ 3 = 1) (g : T) : ρ⁻¹ g = ρ (ρ g) := by
  have h : ρ * ρ ^ 2 = 1 := by rw [← pow_succ', hρ]
  have hinv : ρ⁻¹ = ρ ^ 2 := inv_eq_of_mul_eq_one_right h
  have h2 := congrArg (fun f : MulAut T => f g) hinv
  simpa [pow_two, MulAut.mul_apply] using h2

theorem card_center_inf_fix (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) :
    Nat.card ↥(center T ⊓ fixSub x) = 2 := by
  have h := card_eq_sq_fix (N := center T) (fun n hn => hS.sq_center n hn)
    (fun n hn => rho_mem_center ρ hn) (fun n hn => rho_mem_center x hn) hρ hfpf hx hxρ
  rw [hS.card_center] at h
  have h1 : Nat.card ↥(center T ⊓ fixSub x) ^ 2 = (2 : ℕ) ^ 2 := by
    rw [← h]; norm_num
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1

theorem card_fix_quot (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) :
    Nat.card ↥(fixSub (centerAut x)) = 4 := by
  haveI : Finite (T ⧸ center T) :=
    Finite.of_surjective (QuotientGroup.mk' (center T)) (QuotientGroup.mk'_surjective _)
  have hρ' : (centerAut ρ) ^ 3 = 1 := by
    rw [← centerAut_pow, hρ, centerAut_one]
  have hx' : centerAut x * centerAut x = 1 := by
    rw [← centerAut_mul, hx, centerAut_one]
  have hxρ' : centerAut x * centerAut ρ * (centerAut x)⁻¹ = (centerAut ρ)⁻¹ := by
    calc centerAut x * centerAut ρ * (centerAut x)⁻¹
        = centerAut (x * ρ) * (centerAut x)⁻¹ := by rw [← centerAut_mul]
      _ = centerAut (x * ρ) * centerAut x⁻¹ := by rw [← centerAut_inv]
      _ = centerAut ((x * ρ) * x⁻¹) := by rw [← centerAut_mul]
      _ = centerAut (x * ρ * x⁻¹) := by rw [mul_assoc]
      _ = centerAut ρ⁻¹ := by rw [hxρ]
      _ = (centerAut ρ)⁻¹ := centerAut_inv ρ
  have h := card_eq_sq_fix (N := ⊤) (ρ := centerAut ρ) (x := centerAut x)
    (fun v _ => sq_eq_one_quot hS v) (fun v _ => Subgroup.mem_top v)
    (fun v _ => Subgroup.mem_top v) hρ' (centerAut_fpf ρ hρ hfpf) hx' hxρ'
  rw [top_inf_eq, Subgroup.card_top, hS.card_quot] at h
  have h1 : Nat.card ↥(fixSub (centerAut x)) ^ 2 = (4 : ℕ) ^ 2 := by
    rw [← h]; norm_num
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1

theorem exists_lift_fix (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) {g : T}
    (hg : centerAut x (QuotientGroup.mk g) = QuotientGroup.mk g) :
    ∃ g' : T, x g' = g' ∧ (QuotientGroup.mk g' : T ⧸ center T) = QuotientGroup.mk g := by
  let z : T := g⁻¹ * x g
  have hz : z ∈ center T := by
    have hg' : QuotientGroup.mk (x g) = QuotientGroup.mk g := hg
    exact QuotientGroup.eq.mp hg'.symm
  have hzsq : z * z = 1 := hS.sq_center z hz
  have hgxz : g * z = x g := by
    simp only [z]
    group
  have hxz_eq : x z = (x g)⁻¹ * g := by
    simp only [z, map_mul, map_inv, aut_apply_self hx g]
  have hzxz : z * x z = 1 := by
    rw [hxz_eq]
    simp only [z]
    group
  have hxz : x z = z := by
    have h : z * x z = z * z := by rw [hzxz, hzsq]
    exact mul_left_cancel h
  have hzm : z * (ρ z * ρ (ρ z)) = z * z := by
    rw [← mul_assoc, forall_mul_rho_rho_sq ρ hρ hfpf z, hzsq]
  have ha_b : ρ z * ρ (ρ z) = z := mul_left_cancel hzm
  have hb_sq : ρ (ρ z) * ρ (ρ z) = 1 := by
    have h := congrArg (fun t : T => ρ (ρ t)) hzsq
    simpa [map_mul, map_one] using h
  have hzb : z * ρ (ρ z) = ρ z := by
    calc z * ρ (ρ z) = (ρ z * ρ (ρ z)) * ρ (ρ z) := by rw [ha_b]
      _ = ρ z * (ρ (ρ z) * ρ (ρ z)) := by rw [mul_assoc]
      _ = ρ z * 1 := by rw [hb_sq]
      _ = ρ z := by rw [mul_one]
  have hxm : x (ρ z) = ρ (ρ z) := by
    calc x (ρ z) = ρ⁻¹ (x z) := aut_rho_apply hx hxρ z
      _ = ρ⁻¹ z := by rw [hxz]
      _ = ρ (ρ z) := rho_inv_apply hρ z
  refine ⟨g * ρ z, ?_, ?_⟩
  · have h : x (g * ρ z) = (g * z) * ρ (ρ z) := by
      rw [map_mul, ← hgxz, hxm]
    rw [h, mul_assoc, hzb]
  · rw [QuotientGroup.eq]
    have h : (g * ρ z)⁻¹ * g = (ρ z)⁻¹ := by group
    rw [h]
    exact inv_mem (rho_mem_center ρ hz)

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
