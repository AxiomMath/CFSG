module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol
import CFSG.RankThree.PartTwo.Sec21.Hering2119SRank4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fx_qe_commute_of_sq {u y : OGroup Q} (h : u * u = y) : u * y = y * u := by
  rw [← h, mul_assoc, h]

private theorem fx_qe_mapsTo_commSp {u y : OGroup Q} (hyy : y * y = 1) (h : u * u = y) :
    ∀ x ∈ commSp y, (u : V ≃ₗ[ZMod 3] V) x ∈ commSp y := by
  intro x hx
  rw [mem_commSp_iff hyy]
  have huy : u * y = y * u := fx_qe_commute_of_sq h
  have hcoe : ((y : OGroup Q) : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V)
      = (u : V ≃ₗ[ZMod 3] V) * (y : V ≃ₗ[ZMod 3] V) := by
    simpa [Subgroup.coe_mul] using
      congrArg (fun z : OGroup Q => (z : V ≃ₗ[ZMod 3] V)) huy.symm
  calc (y : V ≃ₗ[ZMod 3] V) ((u : V ≃ₗ[ZMod 3] V) x)
      = ((y : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V)) x :=
        (LinearEquiv.mul_apply _ _ _).symm
    _ = ((u : V ≃ₗ[ZMod 3] V) * (y : V ≃ₗ[ZMod 3] V)) x := by rw [hcoe]
    _ = (u : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) x) := LinearEquiv.mul_apply _ _ _
    _ = (u : V ≃ₗ[ZMod 3] V) (-x) := by rw [(mem_commSp_iff hyy).mp hx]
    _ = -(u : V ≃ₗ[ZMod 3] V) x := map_neg _ _

theorem fx_qe_no_q8_pair {q r s y : OGroup Q} (hyy : y * y = 1) (hdim : invDim y = 2)
    (hq : q * q = y) (hr : r * r = y) (hs : s * s = y) (hrq : r * q = q⁻¹ * r)
    (hsq : s * q = q * s) (hsr : s * r = r * s) : False := by
  classical
  let W : Submodule (ZMod 3) V := commSp y
  have hWq : ∀ x ∈ W, (q : V ≃ₗ[ZMod 3] V) x ∈ W := fx_qe_mapsTo_commSp hyy hq
  have hWr : ∀ x ∈ W, (r : V ≃ₗ[ZMod 3] V) x ∈ W := fx_qe_mapsTo_commSp hyy hr
  have hWs : ∀ x ∈ W, (s : V ≃ₗ[ZMod 3] V) x ∈ W := fx_qe_mapsTo_commSp hyy hs
  let A : Module.End (ZMod 3) W :=
    LinearMap.restrict ((q : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) hWq
  let B : Module.End (ZMod 3) W :=
    LinearMap.restrict ((r : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) hWr
  let C : Module.End (ZMod 3) W :=
    LinearMap.restrict ((s : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) hWs
  have hqq : (q : V ≃ₗ[ZMod 3] V) * (q : V ≃ₗ[ZMod 3] V) = (y : V ≃ₗ[ZMod 3] V) := by
    rw [← Subgroup.coe_mul, hq]
  have hrr : (r : V ≃ₗ[ZMod 3] V) * (r : V ≃ₗ[ZMod 3] V) = (y : V ≃ₗ[ZMod 3] V) := by
    rw [← Subgroup.coe_mul, hr]
  have hss : (s : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V) = (y : V ≃ₗ[ZMod 3] V) := by
    rw [← Subgroup.coe_mul, hs]
  have hA : A * A = -1 := by
    ext w
    change (q : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) (w : V)) = -(w : V)
    rw [← LinearEquiv.mul_apply, hqq]
    exact (mem_commSp_iff hyy).mp w.2
  have hB : B * B = -1 := by
    ext w
    change (r : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V)) = -(w : V)
    rw [← LinearEquiv.mul_apply, hrr]
    exact (mem_commSp_iff hyy).mp w.2
  have hC : C * C = -1 := by
    ext w
    change (s : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) (w : V)) = -(w : V)
    rw [← LinearEquiv.mul_apply, hss]
    exact (mem_commSp_iff hyy).mp w.2
  have hqinv : q⁻¹ = q * y := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc q * (q * y) = (q * q) * y := by rw [mul_assoc]
      _ = y * y := by rw [hq]
      _ = 1 := hyy
  have hAB : A * B = -(B * A) := by
    ext w
    change (q : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V)) =
      -(r : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) (w : V))
    have hrq_coe : (r : V ≃ₗ[ZMod 3] V) * (q : V ≃ₗ[ZMod 3] V) =
        ((q⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) * (r : V ≃ₗ[ZMod 3] V) := by
      simpa [Subgroup.coe_mul] using
        congrArg (fun z : OGroup Q => (z : V ≃ₗ[ZMod 3] V)) hrq
    have hqinv_coe : ((q⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) =
        (q : V ≃ₗ[ZMod 3] V) * (y : V ≃ₗ[ZMod 3] V) := by
      rw [hqinv, Subgroup.coe_mul]
    have h1 : (r : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) (w : V)) =
        ((q⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V)) := by
      calc (r : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) (w : V))
          = ((r : V ≃ₗ[ZMod 3] V) * (q : V ≃ₗ[ZMod 3] V)) (w : V) :=
            (LinearEquiv.mul_apply _ _ _).symm
        _ = (((q⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) * (r : V ≃ₗ[ZMod 3] V)) (w : V) := by
            rw [hrq_coe]
        _ = ((q⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V)) :=
            LinearEquiv.mul_apply _ _ _
    have h2 : ((q⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V)) =
        -((q : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V))) := by
      rw [hqinv_coe]
      calc ((q : V ≃ₗ[ZMod 3] V) * (y : V ≃ₗ[ZMod 3] V))
            ((r : V ≃ₗ[ZMod 3] V) (w : V))
          = (q : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V)
              ((r : V ≃ₗ[ZMod 3] V) (w : V))) := LinearEquiv.mul_apply _ _ _
        _ = (q : V ≃ₗ[ZMod 3] V) (-((r : V ≃ₗ[ZMod 3] V) (w : V))) := by
            rw [(mem_commSp_iff hyy).mp (fx_qe_mapsTo_commSp hyy hr (w : V) w.2)]
        _ = -((q : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V))) := map_neg _ _
    rw [h1, h2, neg_neg]
  have hsq_coe : (s : V ≃ₗ[ZMod 3] V) * (q : V ≃ₗ[ZMod 3] V) =
      (q : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V) := by
    simpa [Subgroup.coe_mul] using
      congrArg (fun z : OGroup Q => (z : V ≃ₗ[ZMod 3] V)) hsq
  have hAC : A * C = C * A := by
    ext w
    change (q : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) (w : V)) =
      (s : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) (w : V))
    calc (q : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) (w : V))
        = ((q : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V)) (w : V) :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = ((s : V ≃ₗ[ZMod 3] V) * (q : V ≃ₗ[ZMod 3] V)) (w : V) := by rw [← hsq_coe]
      _ = (s : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) (w : V)) :=
          LinearEquiv.mul_apply _ _ _
  have hsr_coe : (s : V ≃ₗ[ZMod 3] V) * (r : V ≃ₗ[ZMod 3] V) =
      (r : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V) := by
    simpa [Subgroup.coe_mul] using
      congrArg (fun z : OGroup Q => (z : V ≃ₗ[ZMod 3] V)) hsr
  have hBC : B * C = C * B := by
    ext w
    change (r : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) (w : V)) =
      (s : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V))
    calc (r : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) (w : V))
        = ((r : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V)) (w : V) :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = ((s : V ≃ₗ[ZMod 3] V) * (r : V ≃ₗ[ZMod 3] V)) (w : V) := by rw [← hsr_coe]
      _ = (s : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (w : V)) :=
          LinearEquiv.mul_apply _ _ _
  have h4 : 4 ∣ Module.finrank (ZMod 3) W :=
    (CFSG.RankThree.PartTwo.Sec21.Hering2119S.rank_four A B C hA hB hC hAB hAC hBC).1
  have hWdim : Module.finrank (ZMod 3) W = 2 := by
    simpa only [W, invDim] using hdim
  omega

end CFSG.OddStandard.SmallF3.Omega
