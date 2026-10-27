module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffOutFF6PSTypes_toProj_eq_or_eq_piOrth {a b : OGroup Q}
    (h : toProj Q a = toProj Q b) : a = b ∨ a = piOrth Q * b := by
  have hmem : a / b ∈ piGroup Q := by
    refine (QuotientGroup.eq_iff_div_mem (N := piGroup Q)).mp ?_
    change toProj Q a = toProj Q b
    exact h
  rcases mem_piGroup_iff.mp hmem with h1 | h1
  · left
    rw [div_eq_mul_inv] at h1
    exact mul_inv_eq_one.mp h1
  · right
    rw [div_eq_mul_inv] at h1
    rw [← h1]
    group

theorem ffOutFF6PSTypes_conj_map {G : Type*} [Group G] (f : OGroup Q →* G)
    (a b : OGroup Q) : f a * f b * (f a)⁻¹ = f (a * b * a⁻¹) := by
  rw [map_mul, map_mul, map_inv]

theorem ffOutFF6PSTypes_invType_tnone (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    invType (fr.signChange ({none} : Finset (Option (Fin 5)))) = (1, -1) := by
  rw [PFrame.invType_signChange hQ fr]
  have hcard : ({none} : Finset (Option (Fin 5))).card = 1 := by simp
  rw [hcard]
  decide

theorem ffOutFF6PSTypes_invType_some4 (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    invType (fr.signChange ({some 4} : Finset (Option (Fin 5)))) = (1, 1) := by
  rw [PFrame.invType_signChange hQ fr]
  have hcard : ({some 4} : Finset (Option (Fin 5))).card = 1 := by simp
  rw [hcard]
  decide

theorem ffOutFF6PSTypes_ffOmegaToSim_ffZ0s (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffOmegaToSim hQ (ffZ0s hQ fr) = projOrthToProjSim Q
      (toProj Q (fr.signChange (ffOpt ({0, 1, 2, 3} : Finset (Fin 5))))) := by
  simp only [ffOmegaToSim_apply, ffZ0s, coe_omegaToProj, ffZ0p]

theorem ffOutFF6PSTypes_tsz0_eq (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) =
      projOrthToProjSim Q (toProj Q (fr.signChange ({some 4} : Finset (Option (Fin 5))))) := by
  rw [ffOutFF6PSTypes_ffOmegaToSim_ffZ0s, ffTs, ← map_mul, ← map_mul]
  congr 1
  rw [fr.signChange_mul]
  have hset : symmDiff ({none} : Finset (Option (Fin 5)))
      (ffOpt ({0, 1, 2, 3} : Finset (Fin 5))) = ({some 4} : Finset (Option (Fin 5)))ᶜ := by
    decide
  rw [hset, ff6p_toProj_signChange_compl]

theorem ffOutFF6PSTypes_i1_conj (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (fr : PFrame Q (Option (Fin 5)) ffC)
    {x : ProjSim Q} {α β : ℤˣ} {z : ProjSim Q} {u : OGroup Q} (hu : u * u = 1)
    (hβ : invType u = (1, β)) (hz : z = projOrthToProjSim Q (toProj Q u)) (hαβ : α = β)
    (hx : SimHasType x 1 α) :
    ∃ n : ↥(omegaProj hQ), x = ffOmegaToSim hQ n * z * (ffOmegaToSim hQ n)⁻¹ := by
  obtain ⟨y, hyx, hy1, t, htt, hty, htoy⟩ := hx
  have ht : invType t = invType u := by rw [hty, hαβ, hβ]
  obtain ⟨c, hc, hcj⟩ := exists_mem_omegaGroup_conj hQ (by rw [hdim]; norm_num) htt hu ht
  refine ⟨omegaToProj hQ ⟨c⁻¹, (omegaGroup hQ).inv_mem hc⟩, ?_⟩
  have hι : ffOmegaToSim hQ (omegaToProj hQ ⟨c⁻¹, (omegaGroup hQ).inv_mem hc⟩) =
      projOrthToProjSim Q (toProj Q c⁻¹) := by
    rw [ffOmegaToSim_apply, coe_omegaToProj]
  have hx' : x = projOrthToProjSim Q (toProj Q t) := by rw [htoy, hyx]
  have hkey : toProj Q t = toProj Q (c⁻¹ * u * (c⁻¹)⁻¹) := by
    congr 1
    rw [← hcj]
    group
  rw [hx', hι, hz, hkey]
  exact (ffOutFF6PSTypes_conj_map (f := (projOrthToProjSim Q).comp (toProj Q)) c⁻¹ u).symm

end CFSG.OddStandard.SmallF3.Omega
