module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOrth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrBlockType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec8t84t_exists_block_involution (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) {t : OGroup Q} (htt : t * t = 1)
    (htype : invType t = (2, 1)) :
    ∃ p : OGroup (Q.restrict (fixSp t)) × OGroup (Q.restrict (commSp t)),
      p * p = 1 ∧ blockHom htt p ∈ omegaGroup hQ ∧
        QuadraticMap.orthogonalDet (Q.restrict (fixSp t)) p.1 = -1 := by
  have hQU := nondegenerate_restrict_fixSp hQ htt
  have hQW := nondegenerate_restrict_commSp hQ htt
  have htdim : invDim t = 2 := congrArg Prod.fst htype
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 2 := by
    simpa only [invDim] using htdim
  have hfdim : Module.finrank (ZMod 3) (fixSp t) = 4 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at h
    omega
  obtain ⟨a, haa, hatype⟩ := (exists_involution_of_type hQU 1 1).mpr
    ⟨by omega, fun _ => rfl, fun h => absurd (h.trans hfdim) (by norm_num)⟩
  obtain ⟨b, hbb, hbtype⟩ := (exists_involution_of_type hQW 1 1).mpr
    ⟨by omega, fun _ => rfl, fun h => absurd (h.trans hcdim) (by norm_num)⟩
  have hadim : invDim a = 1 := congrArg Prod.fst hatype
  set g₁ : OGroup Q := blockHom htt (a, 1) with hg1def
  set g₂ : OGroup Q := blockInr htt b with hg2def
  have hg1 : g₁ * g₁ = 1 := by
    rw [hg1def, ← map_mul, Prod.mk_mul_mk, haa, one_mul]
    exact map_one (blockHom htt)
  have hg2 : g₂ * g₂ = 1 := by
    rw [hg2def, ← map_mul, hbb, map_one]
  have hg1type : invType g₁ = (1, 1) := by
    rw [hg1def, ff_invType_blockHom_inl hQ htt haa, hatype]
  have hg2type : invType g₂ = (1, 1) := by
    rw [hg2def, invType_blockInr hQ htt hbb, hbtype]
  have hg1d : invDim g₁ = 1 := congrArg Prod.fst hg1type
  have hg1s : invSign g₁ = 1 := congrArg Prod.snd hg1type
  have hg2d : invDim g₂ = 1 := congrArg Prod.fst hg2type
  have hg2s : invSign g₂ = 1 := congrArg Prod.snd hg2type
  have horth : ∀ v ∈ commSp g₁, ∀ w ∈ commSp g₂, QuadraticMap.polar Q v w = 0 := by
    intro v hv w hw
    rw [hg1def, ff_commSp_blockHom_inl htt a] at hv
    rw [hg2def, commSp_blockInr htt b] at hw
    obtain ⟨v', _, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨w', _, rfl⟩ := Submodule.mem_map.mp hw
    exact polar_fixSp_commSp htt v'.2 w'.2
  have hg12 : (g₁ * g₂) * (g₁ * g₂) = 1 := mul_mul_self_of_orth hQ hg1 hg2 horth
  have hg12type : invType (g₁ * g₂) = (2, -1) := by
    rw [invType_mul_of_orth hQ hg1 hg2 horth, hg1d, hg2d, hg1s, hg2s]
    decide
  have hg12mem : g₁ * g₂ ∈ omegaGroup hQ := by
    refine (involution_mem_omegaGroup_iff hQ hg12).mpr ⟨?_, ?_⟩
    · rw [show invDim (g₁ * g₂) = 2 from congrArg Prod.fst hg12type]
      exact even_two
    · rw [show invDim (g₁ * g₂) = 2 from congrArg Prod.fst hg12type,
        show invSign (g₁ * g₂) = -1 from congrArg Prod.snd hg12type]
      decide
  refine ⟨(a, b), ?_, ?_, ?_⟩
  · rw [Prod.mk_mul_mk, haa, hbb]
    rfl
  · have hpm : blockHom htt (a, b) = g₁ * g₂ := by
      have h1 : (a, b) = (a, 1) * (1, b) := by ext <;> simp
      rw [h1, map_mul]
      rfl
    rw [hpm]
    exact hg12mem
  · show QuadraticMap.orthogonalDet (Q.restrict (fixSp t)) a = -1
    rw [orthogonalDet_involution haa, hadim]
    decide

end CFSG.OddStandard.SmallF3.Omega
