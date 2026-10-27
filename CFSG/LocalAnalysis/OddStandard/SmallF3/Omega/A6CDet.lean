module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem a6c_KM2_conj (hQ : Q.Nondegenerate) {x : ProjSim Q} (hx : KM2 x) (δ : ProjSim Q) :
    KM2 (δ * x * δ⁻¹) := by
  obtain ⟨α, y, hy, hne, t, htt, hty, hto⟩ := hx
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨c, hγ⟩ := γ.2
  obtain ⟨hsq, hty'⟩ := invType_simConj hQ hγ htt
  have hd : invDim t = 1 := congrArg Prod.fst hty
  have hs : invSign t = α := congrArg Prod.snd hty
  have hlift : orthToSim Q (simConj hγ t) = γ * orthToSim Q t * γ⁻¹ :=
    Subtype.ext (LinearEquiv.ext fun v => rfl)
  have hxeq : x = QuotientGroup.mk (orthToSim Q t) := by
    rw [← hy, ← hto]
    rfl
  have himg : projOrthToProjSim Q (toProj Q (simConj hγ t)) =
      QuotientGroup.mk γ * x * (QuotientGroup.mk γ)⁻¹ := by
    rw [projOrthToProjSim_toProj, hlift, hxeq]
    rfl
  have hx1 : x ≠ 1 := fun h =>
    hne (projOrthToProjSim_injective (by rw [hy, h, map_one]))
  have hne' : toProj Q (simConj hγ t) ≠ 1 := by
    intro h
    have h1 := congrArg (projOrthToProjSim Q) h
    rw [map_one, himg, mul_inv_eq_one] at h1
    exact hx1 (mul_eq_left.mp h1)
  refine ⟨toSign c * α, toProj Q (simConj hγ t), himg, hne', simConj hγ t, hsq, ?_, rfl⟩
  rw [hty', hd, hs, pow_one]

theorem a6c_not_KM2_mul (hdim : Module.finrank (ZMod 3) V = 6) {x y : ProjSim Q}
    (hx : KM2 x) (hy : KM2 y) : ¬ KM2 (x * y) := by
  obtain ⟨α, a, ha, -, t, htt, hty, hta⟩ := hx
  obtain ⟨β, b, hb, -, s, hss, hsy, hsb⟩ := hy
  rintro ⟨γ, w, hw, -, u, huu, hut, huw⟩
  have h1 : projOrthToProjSim Q (toProj Q u) = projOrthToProjSim Q (toProj Q (t * s)) := by
    rw [huw, hw, map_mul, map_mul, hta, hsb, ha, hb]
  have h2 : toProj Q u = toProj Q (t * s) := projOrthToProjSim_injective h1
  have hdt : QuadraticMap.orthogonalDet Q t = -1 := by
    rw [orthogonalDet_involution htt, show invDim t = 1 from congrArg Prod.fst hty, pow_one]
  have hds : QuadraticMap.orthogonalDet Q s = -1 := by
    rw [orthogonalDet_involution hss, show invDim s = 1 from congrArg Prod.fst hsy, pow_one]
  have hdu : QuadraticMap.orthogonalDet Q u = -1 := by
    rw [orthogonalDet_involution huu, show invDim u = 1 from congrArg Prod.fst hut, pow_one]
  rcases toProj_eq_or_eq_piOrth h2 with h3 | h3
  · have h4 := congrArg (QuadraticMap.orthogonalDet Q) h3
    rw [map_mul, hdu, hdt, hds] at h4
    exact absurd h4 (by decide)
  · have h4 := congrArg (QuadraticMap.orthogonalDet Q) h3
    rw [map_mul, map_mul, orthogonalDet_piOrth, hdim, hdu, hdt, hds] at h4
    exact absurd h4 (by decide)

end CFSG.OddStandard.SmallF3.Omega
