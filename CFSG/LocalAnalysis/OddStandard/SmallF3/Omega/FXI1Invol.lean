module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXI1End
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentBK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXI1Key

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.RankThree.OrthogonalInvolutions (mem_fixSpace mem_commSpace)

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fx_map_mem_commSp {t u : OGroup Q} (htu : t * u = u * t) {w : V} (hw : w ∈ commSp t) :
    (u : V ≃ₗ[ZMod 3] V) w ∈ commSp t := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hw
  refine mem_commSpace.mpr ⟨(u : V ≃ₗ[ZMod 3] V) y, ?_⟩
  have h := LinearEquiv.congr_fun (congrArg (fun z : OGroup Q => (z : V ≃ₗ[ZMod 3] V)) htu) y
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h
  rw [map_sub, h]

theorem fx_map_mem_fixSp {t u : OGroup Q} (htu : t * u = u * t) {w : V} (hw : w ∈ fixSp t) :
    (u : V ≃ₗ[ZMod 3] V) w ∈ fixSp t := by
  rw [mem_fixSpace] at hw ⊢
  have h := LinearEquiv.congr_fun (congrArg (fun z : OGroup Q => (z : V ≃ₗ[ZMod 3] V)) htu) w
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h
  rw [h, hw]

theorem fx_invDim_not_mid (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {t u : OGroup Q} (htt : t * t = 1) (htu : t * u = u * t) (hu9 : u ^ 9 = 1)
    (hu3 : u ^ 3 ≠ 1) : invDim t ≤ 1 ∨ 5 ≤ invDim t := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  have hsum := finrank_fixSp_add_finrank_commSp t
  rw [hdim] at hsum
  have hinv : invDim t = Module.finrank (ZMod 3) (commSp t) := rfl
  have hdc : Module.finrank (ZMod 3) (commSp t) ≤ 4 := by omega
  have hdf : Module.finrank (ZMod 3) (fixSp t) ≤ 4 := by omega
  set U : Module.End (ZMod 3) V := ((u : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) with hU
  have hU9 : U ^ 9 = 1 := by
    rw [hU, ← fx_toEnd_pow, hu9]
    rfl
  have hiso : ∀ a b, Q.polarBilin (U a) (U b) = Q.polarBilin a b := fun a b => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup u.2 a b
  have hsymm : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := fun a b => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm]
  have h1 := fx_key Q.polarBilin hsymm hiso hU9 (W := commSp t)
    (fun w hw => fx_map_mem_commSp htu hw) hdc
    (fun w hw h => fg_eq_zero_of_polar_zero (nondegenerate_restrict_commSp hQ htt) hw
      fun p hp => by simpa [QuadraticMap.polarBilin_apply_apply] using h p hp)
  have h2 := fx_key Q.polarBilin hsymm hiso hU9 (W := fixSp t)
    (fun w hw => fx_map_mem_fixSp htu hw) hdf
    (fun w hw h => fg_eq_zero_of_polar_zero (nondegenerate_restrict_fixSp hQ htt) hw
      fun p hp => by simpa [QuadraticMap.polarBilin_apply_apply] using h p hp)
  have hall : ∀ v, (U ^ 3) v = v := by
    intro v
    have hv : v ∈ fixSp t ⊔ commSp t := by
      rw [(isCompl_fixSp_commSp htt).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, h2 a ha, h1 b hb]
  apply hu3
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have h := congrArg (fun e : Module.End (ZMod 3) V => e v) (fx_toEnd_pow u 3)
  have h' : ((u ^ 3 : OGroup Q) : V ≃ₗ[ZMod 3] V) v = v := h.trans (hall v)
  simpa using h'

end CFSG.OddStandard.SmallF3.Omega
