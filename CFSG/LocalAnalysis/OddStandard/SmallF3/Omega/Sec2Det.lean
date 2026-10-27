module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem orthogonalDet_piOrth :
    QuadraticMap.orthogonalDet Q (piOrth Q) = (-1) ^ Module.finrank (ZMod 3) V := by
  rw [QuadraticMap.orthogonalDet_apply]
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have hlin : (piOrth Q : V ≃ₗ[ZMod 3] V).toLinearMap = (-1 : ZMod 3) • LinearMap.id := by
    ext v
    show (piOrth Q : V ≃ₗ[ZMod 3] V) v = ((-1 : ZMod 3) • LinearMap.id) v
    rw [coe_piOrth_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact (neg_one_smul (R := ZMod 3) v).symm
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one]

theorem orthogonalDet_involution {t : OGroup Q} (htt : t * t = 1) :
    QuadraticMap.orthogonalDet Q t = (-1) ^ invDim t := by
  calc QuadraticMap.orthogonalDet Q t
      = QuadraticMap.orthogonalDet Q
          (blockHom htt (1, piOrth (Q.restrict (commSp t)))) := by
        rw [blockHom_one_piOrth htt]
    _ = QuadraticMap.orthogonalDet (Q.restrict (commSp t))
          (piOrth (Q.restrict (commSp t))) := by
        rw [orthogonalDet_blockHom htt (1, piOrth (Q.restrict (commSp t)))]
        simp
    _ = (-1) ^ Module.finrank (ZMod 3) (commSp t) :=
        orthogonalDet_piOrth (V := commSp t) (Q := Q.restrict (commSp t))
    _ = (-1) ^ invDim t := rfl

theorem orthogonalDet_eq_one_of_mul_self_eq_piOrth
    (hev : Even (Module.finrank (ZMod 3) V)) {b : OGroup Q} (hb : b * b = piOrth Q) :
    QuadraticMap.orthogonalDet Q b = 1 := by
  set B : Module.End (ZMod 3) V := (b : V →ₗ[ZMod 3] V) with hB
  have hBBv : ∀ v : V, B (B v) = -v := by
    intro v
    rw [hB]
    exact aux_p_apply_apply hb v
  have hBB : B * B = (-1 : ZMod 3) • (1 : Module.End (ZMod 3) V) := by
    ext v
    rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [show (-1 : ZMod 3) • v = -v from neg_one_smul (R := ZMod 3) v]
    exact hBBv v
  have hB1 : (B + 1) * (B + 1) = -B := by
    have hexp : (B + 1) * (B + 1) = B * B + (B + B) + 1 := by noncomm_ring
    have h1 : ((-1 : ZMod 3) • (1 : Module.End (ZMod 3) V)) = -1 :=
      neg_one_smul (R := ZMod 3) (1 : Module.End (ZMod 3) V)
    have h2 : B + B = (2 : ZMod 3) • B := (two_smul (ZMod 3) B).symm
    have h3 : (2 : ZMod 3) = -1 := by decide
    have h4 : (-1 : ZMod 3) • B = -B := neg_one_smul (R := ZMod 3) B
    rw [hexp, hBB, h1, h2, h3, h4]
    abel
  have hd2 : LinearMap.det B * LinearMap.det B = 1 := by
    have h := LinearMap.det.map_mul B B
    rw [hBB, LinearMap.det_smul, LinearMap.det.map_one, mul_one, hev.neg_one_pow] at h
    exact h.symm
  have he2 : LinearMap.det (B + 1) * LinearMap.det (B + 1) = LinearMap.det B := by
    have h := LinearMap.det.map_mul (B + 1) (B + 1)
    have hneg : (-B : Module.End (ZMod 3) V) = (-1 : ZMod 3) • B :=
      (neg_one_smul (R := ZMod 3) B).symm
    rw [hB1, hneg, LinearMap.det_smul, hev.neg_one_pow, one_mul] at h
    exact h.symm
  have hd1 : LinearMap.det B = 1 := by
    have hsquare : ∀ e : ZMod 3, e * e = 0 ∨ e * e = 1 := by decide
    have hd0 : LinearMap.det B ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hd2
      exact zero_ne_one hd2
    rcases hsquare (LinearMap.det (B + 1)) with h | h
    · rw [he2] at h
      exact absurd h hd0
    · rw [he2] at h
      exact h
  rw [QuadraticMap.orthogonalDet_apply]
  apply Units.ext
  rw [LinearEquiv.coe_det]
  rw [← hB]
  simpa using hd1

theorem two_mul_invDim_of_conj (hQ : Q.Nondegenerate) {t s : OGroup Q} (htt : t * t = 1)
    (hs : s * t * s⁻¹ = piOrth Q * t) : 2 * invDim t = Module.finrank (ZMod 3) V := by
  have h1 := invType_conj hQ htt s
  rw [hs] at h1
  have h2 : Module.finrank (ZMod 3) V - invDim t = invDim t := by
    have h := congrArg Prod.fst h1
    rw [invType_piOrth_mul hQ htt] at h
    simpa only [invType] using h
  have hle : invDim t ≤ Module.finrank (ZMod 3) V := invDim_le t
  omega

theorem orthogonalDet_of_conj (hQ : Q.Nondegenerate) {t s : OGroup Q} (htt : t * t = 1)
    (hs : s * t * s⁻¹ = piOrth Q * t) :
    Even (Module.finrank (ZMod 3) V) ∧
      QuadraticMap.orthogonalDet Q t = (-1) ^ (Module.finrank (ZMod 3) V / 2) := by
  have h2 := two_mul_invDim_of_conj hQ htt hs
  have hev : Even (Module.finrank (ZMod 3) V) := ⟨invDim t, by omega⟩
  refine ⟨hev, ?_⟩
  have hd : invDim t = Module.finrank (ZMod 3) V / 2 := by omega
  rw [orthogonalDet_involution htt, hd]

end CFSG.OddStandard.SmallF3.Omega
