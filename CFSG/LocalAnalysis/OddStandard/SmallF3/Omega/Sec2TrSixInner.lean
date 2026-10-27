module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrBlockType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInner
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrSix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem innerData_omegaProj_of_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hσ : quadSign Q = 1) {y : omegaGroup hQ}
    (hyy : (y : OGroup Q) * y = 1) (hty : invType (y : OGroup Q) = (6, -1)) :
    InnerData (omegaProj hQ) (omegaToProj hQ y) := by
  have hr : Module.finrank (ZMod 3) (commSp (y : OGroup Q)) = 6 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp (y : OGroup Q))) = -1 := by
    simpa only [invType, invSign] using congrArg Prod.snd hty
  have hU : 2 ≤ Module.finrank (ZMod 3) (commSp (y : OGroup Q)) := by omega
  have hW : 0 < Module.finrank (ZMod 3) (fixSp (y : OGroup Q)) := by
    have := finrank_fixSp_add_finrank_commSp (Q := Q) (y : OGroup Q)
    omega
  have hQU := nondegenerate_restrict_commSp hQ hyy
  have hinj := omegaProjInr_injective hQ hyy hU hW
  let φ : omegaGroup hQU ≃* (omegaProjInr hQ hyy hU).range := MonoidHom.ofInjective hinj
  have hquasi : CFSG.IsQuasisimple ↥(omegaProjInr hQ hyy hU).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ (isQuasisimple_omegaGroup_six_minus hQU hr hs)
  have hle : (omegaProjInr hQ hyy hU).range ≤
      Subgroup.centralizer ({omegaToProj hQ y} : Set (omegaProj hQ)) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hc := Subgroup.mem_centralizer_singleton_iff.mp
      (blockInr_mem_centralizer hQ hyy (b : OGroup _))
    change toProj Q (blockInr hyy (b : OGroup _)) * toProj Q (y : OGroup Q) =
      toProj Q (y : OGroup Q) * toProj Q (blockInr hyy (b : OGroup _))
    rw [← map_mul, ← map_mul, hc]
  have hpiU : piOrth (Q.restrict (commSp (y : OGroup Q))) ∈ omegaGroup hQU := by
    refine (piOrth_mem_omegaGroup_iff hQU).mpr ⟨?_, ?_⟩
    · rw [hr]
      decide
    · rw [hs, hr]
      decide
  have hzX : omegaToProj hQ y ∈ (omegaProjInr hQ hyy hU).range := by
    refine ⟨⟨_, hpiU⟩, ?_⟩
    change omegaToProj hQ (omegaInr hQ hyy hU ⟨_, hpiU⟩) = _
    congr 1
    exact Subtype.ext (blockInr_piOrth hyy)
  obtain ⟨t, htt, htype⟩ := (exists_involution_of_type hQU 4 1).mpr
    ⟨by omega, fun h => absurd h (by decide), fun h => absurd (h.trans hr) (by decide)⟩
  have hdt : invDim t = 4 := by simpa only [invType, invDim] using congrArg Prod.fst htype
  have hst : invSign t = 1 := by simpa only [invType, invSign] using congrArg Prod.snd htype
  have htΩ : t ∈ omegaGroup hQU := by
    refine (involution_mem_omegaGroup_iff hQU htt).mpr ⟨?_, ?_⟩
    · rw [hdt]
      decide
    · rw [hdt, hst]
      decide
  have hpocket := asc82PocketCover_holds _ (Q.restrict (commSp (y : OGroup Q))) hQU ⟨t, htΩ⟩
    (Subtype.ext htt) htype
  have hpocket' := isI4PlusIn_top_map_mulEquiv φ hpocket
  have hπt : (piOrth (Q.restrict (commSp (y : OGroup Q))) * t) *
      (piOrth (Q.restrict (commSp (y : OGroup Q))) * t) = 1 := piOrth_mul_mul_self htt
  have hty2 : invType (piOrth (Q.restrict (commSp (y : OGroup Q))) * t) = (2, -1) := by
    rw [invType_piOrth_mul hQU htt, hdt, hst, hr, hs]
    decide
  have hblk : invType (blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t)) =
      (2, -1) := by
    rw [invType_blockInr hQ hyy hπt, hty2]
  have hblk2 : blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t) *
      blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t) = 1 := by
    rw [← map_mul, hπt, map_one]
  have hSS : (piOrth Q * blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t)) *
      (piOrth Q * blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t)) = 1 :=
    piOrth_mul_mul_self hblk2
  have hbd : invDim (blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t)) = 2 := by
    simpa only [invType, invDim] using congrArg Prod.fst hblk
  have hbs : invSign (blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t)) = -1 := by
    simpa only [invType, invSign] using congrArg Prod.snd hblk
  have hSty : invType (piOrth Q *
      blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t)) = (6, -1) := by
    rw [invType_piOrth_mul hQ hblk2, hbd, hbs, hdim, hσ]
    decide
  obtain ⟨c, hc, hcS⟩ := exists_mem_omegaGroup_conj hQ (by omega) hyy hSS
    (hty.trans hSty.symm)
  have hcomm : blockInr hyy t * (y : OGroup Q) = (y : OGroup Q) * blockInr hyy t :=
    Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hyy t)
  have hSeq : piOrth Q * blockInr hyy (piOrth (Q.restrict (commSp (y : OGroup Q))) * t) =
      piOrth Q * (blockInr hyy t * (y : OGroup Q)) := by
    rw [map_mul, blockInr_piOrth, hcomm]
  refine ⟨(omegaProjInr hQ hyy hU).range, ?_, hzX, ?_, φ ⟨t, htΩ⟩, hpocket', ?_⟩
  · exact isComponentIn_of_normal hle hquasi
      (omegaProjInr_range_normal hQ hyy hU (by omega))
  · exact isTwoU43_of_mulEquiv φ (isTwoU43_omegaGroup hQU hr hs)
  · refine ⟨(omegaToProj hQ ⟨c, hc⟩)⁻¹, ?_⟩
    apply Subtype.ext
    rw [inv_inv]
    have h1 : omegaToProj hQ ⟨c, hc⟩ * omegaToProj hQ y * (omegaToProj hQ ⟨c, hc⟩)⁻¹ =
        omegaToProj hQ (⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    change toProj Q (c * (y : OGroup Q) * c⁻¹) =
      toProj Q (blockInr hyy t) * toProj Q (y : OGroup Q)
    rw [hcS, hSeq, map_mul, toProj_piOrth, one_mul, map_mul]

end CFSG.OddStandard.SmallF3.Omega
