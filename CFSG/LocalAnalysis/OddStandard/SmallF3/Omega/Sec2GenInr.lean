module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenRefl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.ClassicalInvolution

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem coe_reflOf_apply (u : V) (hu : Q u ≠ 0) (x : V) :
    ((reflOf Q u hu : OGroup Q) : V ≃ₗ[ZMod 3] V) x =
      x - (QuadraticMap.polar Q u x / Q u) • u := by
  letI : Invertible (Q u) := invertibleOfNonzero hu
  rw [reflOf_eq u hu, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  exact TauCeti.QuadraticMap.reflection_apply_eq_sub_div Q u x

theorem blockInr_reflOf {s : OGroup Q} (hs : s * s = 1) (u : commSp s)
    (hu : (Q.restrict (commSp s)) u ≠ 0) :
    blockInr hs (reflOf (Q.restrict (commSp s)) u hu) = reflOf Q (u : V) hu := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, x, rfl⟩ := exists_fixSp_add_commSp hs v
  rw [blockInr_apply, blockHom_apply hs (1, reflOf (Q.restrict (commSp s)) u hu) w x,
    coe_reflOf_apply (u : V) hu]
  have h1 : (((1 : OGroup (Q.restrict (fixSp s))) : fixSp s ≃ₗ[ZMod 3] fixSp s) w : V) = w := rfl
  have h2 : ((((reflOf (Q.restrict (commSp s)) u hu : OGroup (Q.restrict (commSp s))) :
      commSp s ≃ₗ[ZMod 3] commSp s) x : commSp s) : V) =
      (x : V) - (QuadraticMap.polar Q (u : V) (x : V) / Q (u : V)) • (u : V) := by
    rw [coe_reflOf_apply u hu x]
    rfl
  have h3 : QuadraticMap.polar Q (u : V) (w : V) = 0 := by
    rw [QuadraticMap.polar_comm]
    exact polar_fixSp_commSp hs w.2 u.2
  simp only [h1, h2, QuadraticMap.polar_add_right, h3, zero_add]
  abel

theorem reflOf_mul_reflOf_mem_omegaGroup {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] {R : QuadraticForm (ZMod 3) W} (hR : R.Nondegenerate)
    (u v : W) (hu : R u ≠ 0) (hv : R v ≠ 0) (huv : R u = R v) :
    reflOf R u hu * reflOf R v hv ∈ omegaGroup hR := by
  letI : Invertible (R u) := invertibleOfNonzero hu
  letI : Invertible (R v) := invertibleOfNonzero hv
  rw [reflOf_eq u hu, reflOf_eq v hv, mem_omegaGroup_iff, map_mul,
    detSpinorNorm_reflectionOrthogonal, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (R u) = unitOfInvertible (R v) :=
    Units.ext (by rw [val_unitOfInvertible, val_unitOfInvertible, huv])
  rw [← hunit]
  refine Prod.ext ?_ ?_
  · show (-1 : (ZMod 3)ˣ) * (-1) = 1
    decide
  · show TauCeti.squareClassHom (unitOfInvertible (R u)) *
      TauCeti.squareClassHom (unitOfInvertible (R u)) = 1
    rw [← map_mul]
    have hsq : ∀ w : (ZMod 3)ˣ, w * w = 1 := by decide
    rw [hsq]
    exact map_one _

theorem reflOf_mul_reflOf_blockInr (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp s)) (u v : V) (hu : u ∈ commSp s)
    (hv : v ∈ commSp s) (hQu : Q u ≠ 0) (hQv : Q v ≠ 0) (huv : Q u = Q v) :
    ∃ b : omegaGroup (nondegenerate_restrict_commSp hQ hs),
      blockInr hs (b : OGroup (Q.restrict (commSp s))) = reflOf Q u hQu * reflOf Q v hQv := by
  have hu' : (Q.restrict (commSp s)) ⟨u, hu⟩ ≠ 0 := hQu
  have hv' : (Q.restrict (commSp s)) ⟨v, hv⟩ ≠ 0 := hQv
  refine ⟨⟨reflOf (Q.restrict (commSp s)) ⟨u, hu⟩ hu' *
    reflOf (Q.restrict (commSp s)) ⟨v, hv⟩ hv',
    reflOf_mul_reflOf_mem_omegaGroup (nondegenerate_restrict_commSp hQ hs) _ _ hu' hv' huv⟩, ?_⟩
  change blockInr hs (reflOf (Q.restrict (commSp s)) ⟨u, hu⟩ hu' *
    reflOf (Q.restrict (commSp s)) ⟨v, hv⟩ hv') = _
  rw [map_mul, blockInr_reflOf hs ⟨u, hu⟩ hu', blockInr_reflOf hs ⟨v, hv⟩ hv']

theorem omegaToProj_reflPair_mem_range (hQ : Q.Nondegenerate) {y : omegaGroup hQ}
    (hyy : (y : OGroup Q) * y = 1) (hU : 2 ≤ Module.finrank (ZMod 3) (commSp (y : OGroup Q)))
    (u v : V) (hu : u ∈ commSp (y : OGroup Q)) (hv : v ∈ commSp (y : OGroup Q))
    (hQu : Q u ≠ 0) (hQv : Q v ≠ 0) (huv : Q u = Q v)
    (g : omegaGroup hQ) (hg : (g : OGroup Q) = reflOf Q u hQu * reflOf Q v hQv) :
    omegaToProj hQ g ∈ (omegaProjInr hQ hyy hU).range := by
  obtain ⟨b, hb⟩ := reflOf_mul_reflOf_blockInr hQ hyy hU u v hu hv hQu hQv huv
  refine ⟨b, ?_⟩
  change omegaToProj hQ (omegaInr hQ hyy hU b) = omegaToProj hQ g
  congr 1
  apply Subtype.ext
  rw [coe_omegaInr, hb, hg]

end CFSG.OddStandard.SmallF3.Omega
