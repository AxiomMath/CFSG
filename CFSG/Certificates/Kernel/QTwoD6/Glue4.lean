module

public import CFSG.Certificates.Kernel.QTwoD6.Glue3

public section

namespace CFSG.StandardType.QTwoD6.K

open Module CFSG.KC.QTwoD6K CFSG.StandardType.QTwoLin

theorem decV_eq_of_cd {t : Nat} {c : V7} (h : cd t = fun j => us j c) : decV t = c := by
  rw [decV, h]
  exact (eq_sum_us_ub c).symm

theorem decA_eq_of_cd {t : Nat} {φ : Dual (ZMod 3) V7} (h : cd t = fun j => φ (ub j)) :
    decA t = φ := by
  apply LinearMap.ext
  intro v
  rw [decA, h, LinearMap.sum_apply]
  conv_rhs => rw [eq_sum_us_ub v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

theorem decL_eq_of_cd {t : Nat} {c : V7} {φ : Dual (ZMod 3) V7}
    (hh : cd (hK t) = fun j => us j c) (ha : cd (aK t) = fun j => φ (ub j)) :
    decL t = LinearMap.id - φ.smulRight c := by
  rw [decL, decV_eq_of_cd hh, decA_eq_of_cd ha]

theorem reflection_coe {c : V7} {φ : Dual (ZMod 3) V7} (h : φ c = 2) :
    ((reflection h : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7) = LinearMap.id - φ.smulRight c := by
  apply LinearMap.ext
  intro v
  rw [LinearEquiv.coe_coe, reflection_apply]
  rfl

theorem apply_eq_sum_coords (φ : Dual (ZMod 3) V7) (c : V7) :
    φ c = ∑ j : Fin 7, φ (ub j) * us j c := by
  conv_lhs => rw [eq_sum_us_ub c]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem dual_ext_ub {f g : Dual (ZMod 3) V7} (h : ∀ j, f (ub j) = g (ub j)) : f = g := by
  apply LinearMap.ext
  intro v
  rw [eq_sum_us_ub v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, h]

theorem conj_reflection (g : V7 ≃ₗ[ZMod 3] V7) {c : V7} {φ : Dual (ZMod 3) V7} (h : φ c = 2) :
    ∃ h' : (φ.comp (g : V7 →ₗ[ZMod 3] V7)) (g.symm c) = 2,
      g⁻¹ * reflection h * g = reflection h' := by
  have h' : (φ.comp (g : V7 →ₗ[ZMod 3] V7)) (g.symm c) = 2 := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h]
  refine ⟨h', ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflection_apply, reflection_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub, map_smul]
  change g.symm (g v) - φ (g v) • g.symm c = v - φ (g v) • g.symm c
  rw [LinearEquiv.symm_apply_apply]

theorem us_symm_apply {g : V7 ≃ₗ[ZMod 3] V7} {σ : Equiv.Perm (Fin 6)} {ε : (ZMod 3)ˣ}
    (hg0 : g e0 = (ε : ZMod 3) • e0) (hg : ∀ j, g (ub j.succ) = ub (σ j).succ) (c : V7) :
    us 0 (g.symm c) = ((ε⁻¹ : (ZMod 3)ˣ) : ZMod 3) * us 0 c ∧
      ∀ k : Fin 6, us k.succ (g.symm c) = us (σ k).succ c := by
  have hs0 : g.symm e0 = ((ε⁻¹ : (ZMod 3)ˣ) : ZMod 3) • e0 := by
    apply g.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, hg0, smul_smul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul]
  have hs : ∀ n : Fin 6, g.symm (ub n.succ) = ub (σ.symm n).succ := by
    intro n
    apply g.injective
    rw [LinearEquiv.apply_symm_apply, hg, Equiv.apply_symm_apply]
  have hus : ∀ (f : Dual (ZMod 3) V7) (c : V7), f (g.symm c) = (f.comp (g.symm : V7 →ₗ[ZMod 3] V7)) c :=
    fun _ _ => rfl
  constructor
  · rw [hus]
    have : (us 0).comp (g.symm : V7 →ₗ[ZMod 3] V7) = ((ε⁻¹ : (ZMod 3)ˣ) : ZMod 3) • us 0 := by
      apply dual_ext_ub
      intro j
      induction j using Fin.cases with
      | zero =>
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ub_zero, hs0, map_smul, LinearMap.smul_apply]
      | succ n =>
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hs, LinearMap.smul_apply, us_ub, us_ub,
          if_neg (Fin.succ_ne_zero _).symm, if_neg (Fin.succ_ne_zero _).symm, smul_zero]
    rw [this, LinearMap.smul_apply, smul_eq_mul]
  · intro k
    rw [hus]
    have : (us k.succ).comp (g.symm : V7 →ₗ[ZMod 3] V7) = us (σ k).succ := by
      apply dual_ext_ub
      intro j
      induction j using Fin.cases with
      | zero =>
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ub_zero, hs0, map_smul, ← ub_zero,
          us_ub, us_ub, if_neg (Fin.succ_ne_zero _), if_neg (Fin.succ_ne_zero _), smul_zero]
      | succ n =>
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hs, us_ub, us_ub]
        simp only [Fin.succ_inj]
        by_cases hn : k = σ.symm n
        · subst hn
          simp
        · have : σ k ≠ n := fun h => hn (by rw [← h, Equiv.symm_apply_apply])
          simp [hn, this]
    rw [this]

theorem comp_ub {g : V7 ≃ₗ[ZMod 3] V7} {σ : Equiv.Perm (Fin 6)} {ε : (ZMod 3)ˣ}
    (hg0 : g e0 = (ε : ZMod 3) • e0) (hg : ∀ j, g (ub j.succ) = ub (σ j).succ)
    (φ : Dual (ZMod 3) V7) :
    (φ.comp (g : V7 →ₗ[ZMod 3] V7)) (ub 0) = (ε : ZMod 3) * φ (ub 0) ∧
      ∀ k : Fin 6, (φ.comp (g : V7 →ₗ[ZMod 3] V7)) (ub k.succ) = φ (ub (σ k).succ) := by
  refine ⟨?_, fun k => ?_⟩
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ub_zero, hg0, map_smul, smul_eq_mul]
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hg]

end CFSG.StandardType.QTwoD6.K

end
