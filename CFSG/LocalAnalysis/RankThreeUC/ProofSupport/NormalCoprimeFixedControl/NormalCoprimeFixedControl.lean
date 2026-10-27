module


public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import CFSG.GroupTheory.AutomorphismAction.CommutingPGroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace ProofSupport

namespace NormalCoprimeFixedControl

open Finset

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
  {W : Type*} [AddCommGroup W] [Module (ZMod p) W] [Finite W]

theorem fixed_of_normalizing_pGroup_fixed
    (tau : H →* (W ≃ₗ[ZMod p] W)) (R D : Subgroup H)
    (hnorm : ∀ d ∈ D, ∀ r ∈ R, d * r * d⁻¹ ∈ R)
    (hcop : Nat.Coprime (Nat.card R) p) (hD : IsPGroup p D)
    (hfix : ∀ w : W, (∀ d : D, tau d w = w) → ∀ r : R, tau r w = w) :
    ∀ r ∈ R, ∀ w : W, tau r w = w := by
  classical
  haveI : Fintype R := Fintype.ofFinite R
  let s : W →ₗ[ZMod p] W := ∑ r : R, ((tau r : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W)
  have hs : ∀ w, s w = ∑ r : R, tau r w := fun w => by
    simp [s, LinearMap.sum_apply]
  have hsr : ∀ (r₀ : R) w, s (tau r₀ w) = s w := fun r₀ w => by
    rw [hs, hs]
    have : ∀ r : R, tau r (tau r₀ w) = tau (r * r₀) w := fun r => by simp [map_mul]
    simp_rw [this]
    exact Fintype.sum_equiv (Equiv.mulRight r₀) _ _ (fun r => by simp)
  have hsd : ∀ (d : D) w, s (tau d w) = tau d (s w) := fun d w => by
    rw [hs, hs, map_sum]
    let c : R ≃ R :=
      { toFun := fun r => ⟨d⁻¹ * r * d, by
          simpa using hnorm (d⁻¹ : D) (D.inv_mem d.2) r r.2⟩
        invFun := fun r => ⟨d * r * d⁻¹, hnorm d d.2 r r.2⟩
        left_inv := fun r => by ext; simp [mul_assoc]
        right_inv := fun r => by ext; simp [mul_assoc] }
    refine (Fintype.sum_equiv c _ _ (fun r => ?_))
    simp only [c, Equiv.coe_fn_mk, ← LinearEquiv.mul_apply, ← map_mul]
    congr 2
    simp [mul_assoc]
  have hbot : LinearMap.ker s = ⊥ := by
    by_contra hne
    obtain ⟨v, hvN, hv0, hvfix⟩ :=
      CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.exists_fixed_of_invariant (p := p) hD
      (tau.comp D.subtype) (LinearMap.ker s)
      (fun d u hu => by
        have hu' : s u = 0 := hu
        change s (tau (d : H) u) = 0
        rw [hsd, hu', map_zero]) hne
    have hR : ∀ r : R, tau r v = v := hfix v (fun d => hvfix d)
    have hsv : s v = (Nat.card R : ZMod p) • v := by
      rw [hs]
      simp [hR, ← Nat.cast_smul_eq_nsmul (ZMod p), Nat.card_eq_fintype_card]
    have hnz : (Nat.card R : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm hd)
    have h0 : s v = 0 := hvN
    rw [hsv] at h0
    exact hv0 ((smul_eq_zero.mp h0).resolve_left hnz)
  intro r hr w
  have hmem : tau r w - w ∈ LinearMap.ker s := by
    change s (tau r w - w) = 0
    rw [map_sub]
    have := hsr ⟨r, hr⟩ w
    simp only at this
    rw [this, sub_self]
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

end NormalCoprimeFixedControl

end ProofSupport

end CFSG.LocalAnalysis.RankThreeUC
