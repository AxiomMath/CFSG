module

import CFSG.CGT.PushingUpLit.A78S4.Side
public import CFSG.CGT.PushingUpLit.A78L3.Heis
public import CFSG.CGT.PushingUpLit.A78S4.Nat

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit.A78S4 CFSG.CGT.PushingUpLit.A78L3 Matrix

variable {G : Type} [Group G] {L V K : Subgroup G} {e : ℕ}

theorem scalar_of_odd_cent_sylow (D : NatCoordK G L V K (GaloisField 2 e)) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hn : Odd n) (hxn : x ^ n = 1) {w₀ : Fin 2 → GaloisField 2 e} (hw₀ : w₀ ≠ 0)
    (hcent : ∀ u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e),
      (u : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ w₀ = w₀ →
        ∃ p ∈ L, D.ρ p = u ∧ x * p * x⁻¹ = p) :
    ∃ a : GaloisField 2 e, a ≠ 0 ∧ ∀ w, D.act x w = a • w := by
  obtain ⟨σ, hσ⟩ := D.exists_semilinear hxL hx
  have hσ' : ∀ c w, D.act x (c • w) = σ c • D.act x w := fun c w => hσ c w
  have hT0 : D.act x 0 = 0 := by simpa using hσ' 0 0
  have hcomm : ∀ u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e),
      (u : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ w₀ = w₀ → ∀ w,
        D.act x ((u : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ w) =
          (u : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.act x w := by
    intro u hu w
    obtain ⟨p, hp, hρ, hxp⟩ := hcent u hu
    have h1 := NatCoordK.act_twist (D := D) hxL hx hp w
    rw [hxp, hρ] at h1
    exact h1
  obtain ⟨y₀, hdet⟩ := exists_det2_eq_one hw₀
  have key : ∀ s : GaloisField 2 e,
      σ s • D.act x w₀ = (det2 w₀ (D.act x y₀) * s) • w₀ := by
    intro s
    obtain ⟨M, hM⟩ := S4Side.exists_transvection w₀ s
    have hMw : (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ w₀ = w₀ := by
      rw [hM, det2_self, zero_mul, zero_smul, add_zero]
    have h1 := hcomm M hMw y₀
    rw [hM, hM, hdet, NatCoordK.act_add hx, hσ', one_mul] at h1
    exact add_left_cancel h1
  set d : GaloisField 2 e := det2 w₀ (D.act x y₀) with hd
  have hTw₀ : D.act x w₀ = d • w₀ := by
    have h1 := key 1
    rwa [map_one, one_smul, mul_one] at h1
  have hd0 : d ≠ 0 := by
    intro h0
    apply hw₀
    refine (D.actPerm x hx).injective ?_
    show D.act x w₀ = D.act x 0
    rw [hTw₀, h0, zero_smul, hT0]
  have hσ1 : ∀ s, σ s = s := by
    intro s
    have h1 := key s
    rw [hTw₀, smul_smul] at h1
    have h2 := smul_left_injective (GaloisField 2 e) hw₀ h1
    exact mul_right_cancel₀ hd0 (by rw [h2, mul_comm])
  have hlin : ∀ (c : GaloisField 2 e) (w : Fin 2 → GaloisField 2 e),
      D.act x (c • w) = c • D.act x w := fun c w => by rw [hσ', hσ1]
  obtain ⟨α', hTy⟩ : ∃ α' : GaloisField 2 e, D.act x y₀ = (d * α') • w₀ + d • y₀ := by
    refine ⟨d⁻¹ * det2 (D.act x y₀) y₀, ?_⟩
    have h1 := eq_det2_smul hdet (D.act x y₀)
    rw [← hd] at h1
    rw [mul_inv_cancel_left₀ hd0]
    exact h1
  have hpow : ∀ k : ℕ, D.act (x ^ k) w₀ = d ^ k • w₀ ∧
      D.act (x ^ k) y₀ = d ^ k • y₀ + ((k : GaloisField 2 e) * d ^ k * α') • w₀ := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, NatCoordK.act_one, NatCoordK.act_one]
      simp
    | succ k ih =>
      have hxk : x ^ k ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G) :=
        pow_mem hx k
      rw [pow_succ' x k, NatCoordK.act_mul hx hxk, NatCoordK.act_mul hx hxk, ih.1, ih.2]
      refine ⟨?_, ?_⟩
      · rw [hlin, hTw₀, smul_smul, pow_succ]
      · rw [NatCoordK.act_add hx, hlin, hlin, hTy, hTw₀]
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
  have hn0 : (n : GaloisField 2 e) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff (GaloisField 2 e) 2 n] at h0
    obtain ⟨m, hm⟩ := hn
    omega
  have hα : α' = 0 := by
    have h1 := (hpow n).2
    rw [hxn, NatCoordK.act_one] at h1
    have h2 := congrArg (det2 w₀) h1
    rw [det2_add_right, det2_smul_right, det2_smul_right, det2_self, hdet] at h2
    have h3 := congrArg (fun v => det2 v y₀) h1
    simp only [det2_add_left, det2_smul_left, det2_self, hdet] at h3
    have h4 : (n : GaloisField 2 e) * d ^ n * α' = 0 := by
      linear_combination (-1 : GaloisField 2 e) * h3
    have h5 : d ^ n = 1 := by linear_combination (-1 : GaloisField 2 e) * h2
    rw [h5, mul_one] at h4
    exact (mul_eq_zero.1 h4).resolve_left hn0
  refine ⟨d, hd0, fun w => ?_⟩
  have hw := eq_det2_smul hdet w
  calc D.act x w = D.act x (det2 w y₀ • w₀ + det2 w₀ w • y₀) := congrArg (D.act x) hw
    _ = d • (det2 w y₀ • w₀ + det2 w₀ w • y₀) := by
      rw [NatCoordK.act_add hx, hlin, hlin, hTw₀, hTy, hα]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    _ = d • w := by rw [← hw]

end CFSG.CGT.PushingUpLit.A78G0
