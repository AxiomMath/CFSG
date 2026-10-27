module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SESim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace sub_mem_commSpace)

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  [AddCommGroup V'] [Module (ZMod 3) V'] [FiniteDimensional (ZMod 3) V']
  {Q : QuadraticForm (ZMod 3) V} {Q' : QuadraticForm (ZMod 3) V'}

private theorem commSp_orthogonalGroupCongr (e : Q.IsometryEquiv Q') (t : OGroup Q) :
    commSp (orthogonalGroupCongr e t) =
      (commSp t).map (e.toLinearEquiv : V →ₗ[ZMod 3] V') := by
  change commSpace ((orthogonalGroupCongr e t : OGroup Q') : V' ≃ₗ[ZMod 3] V') =
    (commSpace (t : V ≃ₗ[ZMod 3] V)).map (e.toLinearEquiv : V →ₗ[ZMod 3] V')
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨(t : V ≃ₗ[ZMod 3] V) (e.toLinearEquiv.symm m) - e.toLinearEquiv.symm m,
      sub_mem_commSpace (t : V ≃ₗ[ZMod 3] V) _, ?_⟩
    simpa only [map_sub, coe_orthogonalGroupCongr_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.coe_coe] using hm
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    refine ⟨e.toLinearEquiv v, ?_⟩
    simp only [coe_orthogonalGroupCongr_apply, LinearEquiv.symm_apply_apply, map_sub,
      LinearEquiv.coe_coe]

private theorem commSp_simAct (γ : simGroup Q) (t : OGroup Q) :
    commSp (simAct Q γ t) = (commSp t).map (γ : V →ₗ[ZMod 3] V) := by
  change commSpace ((simAct Q γ t : OGroup Q) : V ≃ₗ[ZMod 3] V) =
    (commSpace (t : V ≃ₗ[ZMod 3] V)).map (γ : V →ₗ[ZMod 3] V)
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨(t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V).symm m) - (γ : V ≃ₗ[ZMod 3] V).symm m,
      sub_mem_commSpace (t : V ≃ₗ[ZMod 3] V) _, ?_⟩
    simpa only [map_sub, coe_simAct, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply, LinearEquiv.coe_coe] using hm
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    refine ⟨(γ : V ≃ₗ[ZMod 3] V) v, ?_⟩
    simp only [coe_simAct, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, map_sub, LinearEquiv.coe_coe]

private theorem invDim_simAct (γ : simGroup Q) (t : OGroup Q) :
    invDim (simAct Q γ t) = invDim t := by
  simp only [invDim]
  rw [commSp_simAct]
  exact LinearEquiv.finrank_map_eq _ _

private theorem orthToSim_simAct (γ : simGroup Q) (t : OGroup Q) :
    orthToSim Q (simAct Q γ t) = γ * orthToSim Q t * γ⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_orthToSim, coe_simAct]

theorem invDim_orthogonalGroupCongr (e : Q.IsometryEquiv Q') (t : OGroup Q) :
    invDim (orthogonalGroupCongr e t) = invDim t := by
  simp only [invDim]
  rw [commSp_orthogonalGroupCongr]
  exact LinearEquiv.finrank_map_eq _ _

theorem simHasDim_conj {x : ProjSim Q} {r : ℕ} (h : SimHasDim x r) (w : ProjSim Q) :
    SimHasDim (w * x * w⁻¹) r := by
  obtain ⟨t, htt, hdim, hx⟩ := h
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨simAct Q γ t, ?_, ?_, ?_⟩
  · rw [← map_mul, htt, map_one]
  · rw [invDim_simAct, hdim]
  · rw [projOrthToProjSim_toProj, orthToSim_simAct, ← hx, projOrthToProjSim_toProj]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem ffSimOmegaAct_omegaProjCongr (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (h2' : 2 ≤ Module.finrank (ZMod 3) V') (z : ProjOrth Q) (a : omegaProj hQ) :
    omegaProjCongr hQ hQ' e h2 (ffSimOmegaAct hQ h2 (projOrthToProjSim Q z) a) =
      ffSimOmegaAct hQ' h2' (projOrthToProjSim Q' (projOrthCongr e z))
        (omegaProjCongr hQ hQ' e h2 a) := by
  apply Subtype.ext
  simp only [coe_omegaProjCongr, coe_ffSimOmegaAct, projSimAct_projOrthToProjSim, map_mul,
    map_inv]

end CFSG.OddStandard.SmallF3.Omega
