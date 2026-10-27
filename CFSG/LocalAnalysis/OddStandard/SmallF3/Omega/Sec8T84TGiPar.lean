module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaInvol
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec8t84t_aux_twist_apply {ρ : ↥(simGroup Q)} {g : OGroup Q}
    (htw : simAct Q ρ g = piOrth Q * g) (w : V) :
    (ρ : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) w) =
      -((g : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) w)) := by
  have hcoe : (ρ : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) * (ρ : V ≃ₗ[ZMod 3] V)⁻¹ =
      (piOrth Q : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) := by
    have h := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) htw
    simpa only [coe_simAct, Subgroup.coe_mul] using h
  have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e ((ρ : V ≃ₗ[ZMod 3] V) w)) hcoe
  simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply,
    coe_piOrth_apply] using h

theorem sec8t84t_gi_twisted_false (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) {ρ : ↥(simGroup Q)}
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) {g : OGroup Q}
    (hgg : g * g = 1) (hgΩ : g ∈ omegaGroup hQ) (htw : simAct Q ρ g = piOrth Q * g) : False := by
  have hrel := sec8t84t_aux_twist_apply (Q := Q) htw
  have hmap₁ : (fixSp g).map ((ρ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) ≤ commSp g := by
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, mem_commSp_iff hgg]
    have hy' : (g : V ≃ₗ[ZMod 3] V) y = y := (mem_fixSp_iff).mp hy
    have h := hrel y
    rw [hy'] at h
    have hneg := congrArg (fun x : V => -x) h
    rw [neg_neg] at hneg
    exact hneg.symm
  have hmap₂ : (commSp g).map ((ρ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) ≤ fixSp g := by
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, mem_fixSp_iff]
    have hy' : (g : V ≃ₗ[ZMod 3] V) y = -y := (mem_commSp_iff hgg).mp hy
    have h := hrel y
    rw [hy', map_neg] at h
    rw [neg_inj] at h
    exact h.symm
  have hle₁ : Module.finrank (ZMod 3) (fixSp g) ≤ Module.finrank (ZMod 3) (commSp g) := by
    calc Module.finrank (ZMod 3) (fixSp g)
        = Module.finrank (ZMod 3)
            ((fixSp g).map ((ρ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V)) :=
          (LinearEquiv.finrank_map_eq (ρ : V ≃ₗ[ZMod 3] V) (fixSp g)).symm
      _ ≤ Module.finrank (ZMod 3) (commSp g) := Submodule.finrank_mono hmap₁
  have hle₂ : Module.finrank (ZMod 3) (commSp g) ≤ Module.finrank (ZMod 3) (fixSp g) := by
    calc Module.finrank (ZMod 3) (commSp g)
        = Module.finrank (ZMod 3)
            ((commSp g).map ((ρ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V)) :=
          (LinearEquiv.finrank_map_eq (ρ : V ≃ₗ[ZMod 3] V) (commSp g)).symm
      _ ≤ Module.finrank (ZMod 3) (fixSp g) := Submodule.finrank_mono hmap₂
  have heq : Module.finrank (ZMod 3) (fixSp g) = Module.finrank (ZMod 3) (commSp g) :=
    le_antisymm hle₁ hle₂
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) g
  rw [heq, hdim] at hsum
  have h3 : invDim g = 3 := by
    simp only [invDim]
    omega
  have heven : Even (invDim g) := ((involution_mem_omegaGroup_iff hQ hgg).mp hgΩ).1
  rw [h3] at heven
  obtain ⟨k, hk⟩ := heven
  omega

end CFSG.OddStandard.SmallF3.Omega
