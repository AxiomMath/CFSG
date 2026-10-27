module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK2Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ff6m_piOrth_mul_t_eq_blockHom {t : OGroup Q} (htt : t * t = 1) :
    (piOrth Q * t : OGroup Q) =
      blockHom htt (piOrth (Q.restrict (fixSp t)), 1) := by
  have h1 := blockHom_piOrth_piOrth htt
  have h2 := blockHom_one_piOrth htt
  calc piOrth Q * t
      = blockHom htt (piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) *
          blockHom htt (1, piOrth (Q.restrict (commSp t))) := by rw [h1, h2]
    _ = blockHom htt ((piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) *
          (1, piOrth (Q.restrict (commSp t)))) := (map_mul _ _ _).symm
    _ = blockHom htt (piOrth (Q.restrict (fixSp t)), 1) := by
          rw [Prod.mk_mul_mk, mul_one, piOrth_mul_self]

theorem ff6m_K2_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KM2 x) : LayerModel ↥(ffFix hQ (by omega) x) .PSp 2 1 := by
  obtain ⟨α, y, hy, -, t, htt, htype, htoProj⟩ := hx
  have hxeq : x = projOrthToProjSim Q (toProj Q t) := by rw [← hy, htoProj]
  rw [hxeq]
  obtain ⟨E, hEn, hLie, hP, -⟩ := ff6m_K2_exists_E hQ hdim hsgn (by omega) htt htype
  exact ⟨E, hEn, hLie, hP⟩

theorem ff6m_K2_cover (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KM2 x) :
    ∃ w : ↥(omegaProj hQ), w ∈ twoRes (ffFix hQ (by omega) x) ∧ w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = w := by
  obtain ⟨α, y, hy, -, t, htt, htype, htoProj⟩ := hx
  have hxeq : x = projOrthToProjSim Q (toProj Q t) := by rw [← hy, htoProj]
  rw [hxeq]
  have htdim : invDim t = 1 := congrArg Prod.fst htype
  have htsgn : invSign t = α := congrArg Prod.snd htype
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 1 := htdim
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 5 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at h
    omega
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp t) := by omega
  have hR : (Q.restrict (fixSp t)).Nondegenerate := nondegenerate_restrict_fixSp hQ htt
  have hnc : ¬ IsConj (piOrth Q * t) t := by
    rw [isConj_piOrth_mul_iff hQ htt]
    rintro ⟨h2r, -⟩
    rw [htdim] at h2r
    omega
  have hUsign : quadSign (Q.restrict (fixSp t)) = α := by
    have h := quadSign_fixSp_eq hQ htt
    rw [hsgn, htsgn, htdim, hdim] at h
    have h1 : (-1 : ℤˣ) ^ (1 * (6 - 1)) = -1 := by decide
    rw [h1] at h
    have h2 : (-1 : ℤˣ) * α * (-1) = α := by
      rw [mul_comm ((-1 : ℤˣ) * α) (-1), ← mul_assoc,
        show (-1 : ℤˣ) * (-1) = 1 by decide, one_mul]
    rwa [h2] at h
  let c : (ZMod 3)ˣ := if α = 1 then 1 else -1
  have htoSign_c : toSign c = α := by
    unfold c
    split_ifs with h
    · rw [h]; decide
    · have h' : α = -1 := by
        rcases Int.units_eq_one_or α with h1 | h1
        · exact absurd h1 h
        · exact h1
      rw [h']; decide
  obtain ⟨a, haQ⟩ := exists_eq_unit_of_two_le_finrank hR (by omega) c
  have ha_ne : (Q.restrict (fixSp t)) a ≠ 0 := by rw [haQ]; exact Units.ne_zero c
  let r : OGroup (Q.restrict (fixSp t)) := reflOf (Q.restrict (fixSp t)) a ha_ne
  have hr2 : r * r = 1 := reflOf_mul_self a ha_ne
  have hrtype : invType r =
      (1, toSign (Units.mk0 ((Q.restrict (fixSp t)) a) ha_ne)) :=
    ff_invType_reflOf hR ha_ne
  have hrdim : invDim r = 1 := congrArg Prod.fst hrtype
  have hrsgn : invSign r = toSign (Units.mk0 ((Q.restrict (fixSp t)) a) ha_ne) :=
    congrArg Prod.snd hrtype
  have huc : Units.mk0 ((Q.restrict (fixSp t)) a) ha_ne = c :=
    Units.ext (by rw [Units.val_mk0, haQ])
  have hsign_a : toSign (Units.mk0 ((Q.restrict (fixSp t)) a) ha_ne) = α := by
    rw [huc, htoSign_c]
  let a' : OGroup (Q.restrict (fixSp t)) := piOrth (Q.restrict (fixSp t)) * r
  have hpi_comm : r * piOrth (Q.restrict (fixSp t)) =
      piOrth (Q.restrict (fixSp t)) * r :=
    Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q.restrict (fixSp t))) r
  have ha'2 : a' * a' = 1 := by
    show (piOrth (Q.restrict (fixSp t)) * r) *
      (piOrth (Q.restrict (fixSp t)) * r) = 1
    calc (piOrth (Q.restrict (fixSp t)) * r) *
          (piOrth (Q.restrict (fixSp t)) * r)
        = piOrth (Q.restrict (fixSp t)) *
            (r * piOrth (Q.restrict (fixSp t))) * r := by group
      _ = piOrth (Q.restrict (fixSp t)) *
            (piOrth (Q.restrict (fixSp t)) * r) * r := by rw [hpi_comm]
      _ = (piOrth (Q.restrict (fixSp t)) *
            piOrth (Q.restrict (fixSp t))) * (r * r) := by group
      _ = 1 := by rw [piOrth_mul_self, hr2, mul_one]
  have hαsq : α * α = 1 := by
    rcases Int.units_eq_one_or α with h | h <;> rw [h] <;> decide
  have ha'type : invType a' = (4, 1) := by
    show invType (piOrth (Q.restrict (fixSp t)) * r) = (4, 1)
    rw [invType_piOrth_mul hR hr2, hrdim, hrsgn, hUdim, hsign_a, hUsign]
    refine Prod.ext ?_ ?_
    · norm_num
    · rw [show (-1 : ℤˣ) ^ (1 * (5 - 1)) = 1 by decide, mul_one, hαsq]
  have ha'mem : a' ∈ omegaGroup hR := by
    rw [involution_mem_omegaGroup_iff hR ha'2]
    refine ⟨?_, ?_⟩
    · rw [show invDim a' = 4 from congrArg Prod.fst ha'type]; decide
    · rw [show invSign a' = 1 from congrArg Prod.snd ha'type,
        show invDim a' = 4 from congrArg Prod.fst ha'type]; decide
  have ha'ne : a' ≠ 1 := by
    intro h
    have hh := congrArg invType h
    rw [ha'type, invType_one] at hh
    exact absurd hh (by decide)
  let wv : OGroup Q := blockHom htt (a', 1)
  have hwvmem : wv ∈ omegaGroup hQ :=
    blockHom_left_mem_omegaGroup hQ htt hW ha'mem
  have hwv2 : wv * wv = 1 := by
    show blockHom htt (a', 1) * blockHom htt (a', 1) = 1
    rw [← map_mul, Prod.mk_mul_mk, ha'2, mul_one]
    exact map_one (blockHom htt)
  have hptw : piOrth Q * t * wv = blockHom htt (r, 1) := by
    show piOrth Q * t * blockHom htt (a', 1) = blockHom htt (r, 1)
    rw [ff6m_piOrth_mul_t_eq_blockHom htt, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · simp only [Prod.mk_mul_mk, mul_one, one_mul]
      rw [show a' = piOrth (Q.restrict (fixSp t)) * r from rfl, ← mul_assoc,
        piOrth_mul_self, one_mul]
    · simp only [Prod.mk_mul_mk, mul_one, one_mul]
  have hptw2 : (piOrth Q * t * wv) * (piOrth Q * t * wv) = 1 := by
    rw [hptw, ← map_mul, Prod.mk_mul_mk, hr2, mul_one]
    exact map_one (blockHom htt)
  have hptw_type : invType (piOrth Q * t * wv) = (1, α) := by
    rw [hptw, ff_invType_blockHom_inl hQ htt hr2, hrtype, hsign_a]
  have h3 : 3 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨g, hg, hgt⟩ :=
    exists_mem_omegaGroup_conj hQ h3 htt hptw2 (htype.trans hptw_type.symm)
  obtain ⟨a₀, ha₀⟩ := ff6m_cover_of_conj hQ hdim htt hwvmem hg
    (Or.inr (by rw [mul_assoc]; exact hgt))
  obtain ⟨E, hEnorm, hLieE, hPE, hcont⟩ :=
    ff6m_K2_exists_E hQ hdim hsgn (by omega) htt htype
  obtain ⟨hsimpleE, hncE⟩ := ff_simple_of_lieModel_psp hLieE
  have hwE : omegaToProj hQ ⟨wv, hwvmem⟩ ∈
      E.map (ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t))).subtype :=
    hcont a' ha'mem hwvmem
  have hw2 : omegaToProj hQ ⟨wv, hwvmem⟩ * omegaToProj hQ ⟨wv, hwvmem⟩ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_omegaToProj, ← map_mul, hwv2, map_one, Subgroup.coe_one]
  have htwoRes : omegaToProj hQ ⟨wv, hwvmem⟩ ∈
      twoRes (ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t))) :=
    ff6m_mem_twoRes_of_simple
      (ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t))) E hsimpleE hncE hwE hw2
  have hwne : omegaToProj hQ ⟨wv, hwvmem⟩ ≠ 1 := by
    intro h1
    rcases (omegaToProj_eq_one_iff hQ ⟨wv, hwvmem⟩).mp h1 with h | h
    · have h' : (a', 1) = (1 : OGroup (Q.restrict (fixSp t)) ×
          OGroup (Q.restrict (commSp t))) :=
        blockHom_injective htt (h.trans (map_one (blockHom htt)).symm)
      exact ha'ne (congrArg Prod.fst h')
    · exact ff6m_blockHom_inl_ne_piOrth_pos htt (by omega) a' h
  exact ⟨omegaToProj hQ ⟨wv, hwvmem⟩, htwoRes, hw2, hwne, a₀, ha₀⟩

end CFSG.OddStandard.SmallF3.Omega
