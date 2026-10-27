module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN1Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MKinds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOrth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_N1_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KN1 x) : LayerModel ↥(ffFix hQ (by omega) x) .PSL 2 2 := by
  obtain ⟨y, hyx, htype⟩ := hx
  obtain ⟨-, t, htt, hty, hto⟩ := htype
  have htt' : (piOrth Q * t) * (piOrth Q * t) = 1 := piOrth_mul_mul_self htt
  have htype' : invType (piOrth Q * t) = (2, 1) := by
    rw [invType_piOrth_mul hQ htt, hdim, hsgn,
      show invDim t = 4 from congrArg Prod.fst hty,
      show invSign t = -1 from congrArg Prod.snd hty]
    decide
  have hx' : x = projOrthToProjSim Q (toProj Q (piOrth Q * t)) := by
    rw [← hyx, ← hto, map_mul, toProj_piOrth, one_mul]
  rw [hx']
  obtain ⟨E, hEn, hLie, hP, -⟩ :=
    ff6m_N1_exists_E hQ hdim hsgn (by omega) htt' htype'
  exact ⟨E, hEn, hLie, hP⟩

theorem ff6m_N1_cover (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KN1 x) :
    ∃ w : ↥(omegaProj hQ), w ∈ twoRes (ffFix hQ (by omega) x) ∧ w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = w := by
  obtain ⟨y, hyx, htype⟩ := hx
  obtain ⟨-, t, htt, hty, hto⟩ := htype
  have htt' : (piOrth Q * t) * (piOrth Q * t) = 1 := piOrth_mul_mul_self htt
  have htype' : invType (piOrth Q * t) = (2, 1) := by
    rw [invType_piOrth_mul hQ htt, hdim, hsgn,
      show invDim t = 4 from congrArg Prod.fst hty,
      show invSign t = -1 from congrArg Prod.snd hty]
    decide
  have hx' : x = projOrthToProjSim Q (toProj Q (piOrth Q * t)) := by
    rw [← hyx, ← hto, map_mul, toProj_piOrth, one_mul]
  rw [hx']
  have htdim' : invDim (piOrth Q * t) = 2 := congrArg Prod.fst htype'
  have htsgn' : invSign (piOrth Q * t) = 1 := congrArg Prod.snd htype'
  have hcdim : Module.finrank (ZMod 3) (commSp (piOrth Q * t)) = 2 := htdim'
  have hUdim : Module.finrank (ZMod 3) (fixSp (piOrth Q * t)) = 4 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) (piOrth Q * t)
    rw [hcdim, hdim] at h
    omega
  have hQU : (Q.restrict (fixSp (piOrth Q * t))).Nondegenerate :=
    nondegenerate_restrict_fixSp hQ htt'
  obtain ⟨a, haa, hatype⟩ :=
    (exists_involution_of_type (V := ↥(fixSp (piOrth Q * t)))
      (Q := Q.restrict (fixSp (piOrth Q * t))) hQU 2 (-1)).mpr
      ⟨by omega, (fun h => absurd h (by norm_num)),
        (fun h => absurd (h.trans hUdim) (by norm_num))⟩
  have hamem : a ∈ omegaGroup hQU := by
    rw [involution_mem_omegaGroup_iff hQU haa]
    refine ⟨?_, ?_⟩
    · rw [show invDim a = 2 from congrArg Prod.fst hatype]
      exact ⟨1, rfl⟩
    · rw [show invDim a = 2 from congrArg Prod.fst hatype,
        show invSign a = -1 from congrArg Prod.snd hatype]
      decide
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp (piOrth Q * t)) := by omega
  have hwmem : blockHom htt' (a, 1) ∈ omegaGroup hQ :=
    blockHom_left_mem_omegaGroup hQ htt' hW hamem
  have hb2 : blockHom htt' (a, 1) * blockHom htt' (a, 1) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, haa, mul_one]
    exact map_one (blockHom htt')
  let w : ↥(omegaProj hQ) := omegaToProj hQ ⟨blockHom htt' (a, 1), hwmem⟩
  have hw2 : w * w = 1 := by
    have hcoe : (w : ProjOrth Q) = toProj Q (blockHom htt' (a, 1)) := rfl
    apply Subtype.ext
    rw [Subgroup.coe_mul, hcoe, ← map_mul, hb2, map_one]
    rfl
  have hwne : w ≠ 1 := by
    intro h1
    rcases (omegaToProj_eq_one_iff hQ ⟨blockHom htt' (a, 1), hwmem⟩).mp h1 with h | h
    · have ha1 : a = 1 := by
        have h1 : (a, 1) = (1 : OGroup (Q.restrict (fixSp (piOrth Q * t))) ×
            OGroup (Q.restrict (commSp (piOrth Q * t)))) :=
          blockHom_injective htt' (h.trans (map_one (blockHom htt')).symm)
        simpa using congrArg Prod.fst h1
      have h2 : invType (1 : OGroup (Q.restrict (fixSp (piOrth Q * t)))) = (2, -1) := by
        rw [← ha1]; exact hatype
      rw [invType_one] at h2
      exact absurd h2 (by decide)
    · exact ff6m_blockHom_inl_ne_piOrth htt' hcdim a h
  have hbtype : invType (blockHom htt' (a, 1)) = (2, -1) := by
    rw [ff_invType_blockHom_inl hQ htt' haa]
    exact hatype
  have hb1 : invDim (blockHom htt' (a, 1)) = 2 := congrArg Prod.fst hbtype
  have hbs : invSign (blockHom htt' (a, 1)) = -1 := congrArg Prod.snd hbtype
  have hbcomm : commSp (blockHom htt' (a, 1)) ≤ fixSp (piOrth Q * t) := by
    rw [ff_commSp_blockHom_inl htt' a]
    rintro v ⟨u, -, rfl⟩
    exact u.2
  have horth' : ∀ v ∈ commSp (piOrth Q * t), ∀ u ∈ commSp (blockHom htt' (a, 1)),
      QuadraticMap.polar Q v u = 0 := by
    intro v hv u hu
    rw [QuadraticMap.polar_comm]
    exact polar_fixSp_commSp htt' (hbcomm hu) hv
  have hmul2 : ((piOrth Q * t) * blockHom htt' (a, 1)) *
      ((piOrth Q * t) * blockHom htt' (a, 1)) = 1 :=
    mul_mul_self_of_orth hQ htt' hb2 horth'
  have htype_mul : invType ((piOrth Q * t) * blockHom htt' (a, 1)) = (4, -1) := by
    rw [invType_mul_of_orth hQ htt' hb2 horth', htdim', hb1, htsgn', hbs]
    decide
  have hs_inv : invType (piOrth Q * ((piOrth Q * t) * blockHom htt' (a, 1))) = (2, 1) := by
    rw [invType_piOrth_mul hQ hmul2, hdim, hsgn,
      show invDim ((piOrth Q * t) * blockHom htt' (a, 1)) = 4 from
        congrArg Prod.fst htype_mul,
      show invSign ((piOrth Q * t) * blockHom htt' (a, 1)) = -1 from
        congrArg Prod.snd htype_mul]
    decide
  have hpi_type : invType (piOrth Q * ((piOrth Q * t) * blockHom htt' (a, 1))) =
      invType (piOrth Q * t) := hs_inv.trans htype'.symm
  obtain ⟨c, hc, hconj⟩ := exists_mem_omegaGroup_conj hQ (by rw [hdim]; norm_num)
    (piOrth_mul_mul_self hmul2) htt' hpi_type
  have hconj' : c⁻¹ * (piOrth Q * t) * (c⁻¹)⁻¹ =
      piOrth Q * ((piOrth Q * t) * blockHom htt' (a, 1)) := by
    have h2 : c⁻¹ * (piOrth Q * t) * c =
        piOrth Q * ((piOrth Q * t) * blockHom htt' (a, 1)) := by
      conv_lhs => rw [← hconj]
      group
    calc c⁻¹ * (piOrth Q * t) * (c⁻¹)⁻¹ = c⁻¹ * (piOrth Q * t) * c := by group
      _ = piOrth Q * ((piOrth Q * t) * blockHom htt' (a, 1)) := h2
  obtain ⟨a', ha'⟩ :=
    ff6m_cover_of_conj hQ hdim htt' hwmem ((omegaGroup hQ).inv_mem hc) (Or.inr hconj')
  have htwoRes : w ∈ twoRes (ffFix hQ (by omega)
      (projOrthToProjSim Q (toProj Q (piOrth Q * t)))) := by
    obtain ⟨E, -, hLie, -, hcont⟩ :=
      ff6m_N1_exists_E hQ hdim hsgn (by omega) htt' htype'
    obtain ⟨hsimp, hncE⟩ := ff_simple_of_lieModel_psl2 hLie
    exact ff6m_mem_twoRes_of_simple (ffFix hQ (by omega)
      (projOrthToProjSim Q (toProj Q (piOrth Q * t)))) E hsimp hncE
      (hcont a hamem hwmem) hw2
  exact ⟨w, htwoRes, hw2, hwne, a', ha'⟩

end CFSG.OddStandard.SmallF3.Omega
