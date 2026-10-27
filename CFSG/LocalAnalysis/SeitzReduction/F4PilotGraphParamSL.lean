module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphFamily
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviKer
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.Timmesfeld.LieEmbed (a5Root exists_slToE6)
open CFSG.LieType.Steinberg.CentralExt.MinusculeClosed (minTorus minTorus_mulSingle
  minTorus_injective)

local instance f4PilotGraphParamSLNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem exists_chainNode_eq : ∀ j ∈ e6A5Nodes, ∃ k : Fin 5, E6Pilot.chainNode k = j := by
  decide

section Hom

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def slToE6Sc :
    Matrix.SpecialLinearGroup (Fin 6) K →* e6Data_valid.minGroup K :=
  (exists_slToE6 (k := K)).choose

variable {K}

theorem slToE6Sc_transvection {i j : Fin 6} (hij : i ≠ j) (c : K) :
    slToE6Sc K (Matrix.SpecialLinearGroup.transvection hij c) =
      e6Data_valid.xm K (a5Root i j) c :=
  (exists_slToE6 (k := K)).choose_spec i j hij c

theorem slToE6Sc_transvection_castSucc_succ (k : Fin 5) (c : K) :
    slToE6Sc K (Matrix.SpecialLinearGroup.transvection (SL.castSucc_ne_succ k) c) =
      e6Data_valid.xm K (Pi.single (E6Pilot.chainNode k) 1) c := by
  rw [slToE6Sc_transvection, E6Pilot.a5Root_castSucc_succ]

theorem slToE6Sc_transvection_succ_castSucc (k : Fin 5) (c : K) :
    slToE6Sc K (Matrix.SpecialLinearGroup.transvection (SL.castSucc_ne_succ k).symm c) =
      e6Data_valid.xm K (-Pi.single (E6Pilot.chainNode k) 1) c := by
  rw [slToE6Sc_transvection, E6Pilot.a5Root_succ_castSucc]

theorem endo_slToE6Sc_blockHom (k : Fin 5) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    e6Data_valid.endo K (slToE6Sc K (SL.blockHom K k M)) =
      e6Data_valid.blockOp K (E6Pilot.chainNode k) M := by
  have hne := SL.castSucc_ne_succ k
  have hext : (e6Data_valid.minGroup K).subtype.comp ((slToE6Sc K).comp (SL.blockHom K k)) =
      e6Data_valid.slHom K (E6Pilot.chainNode k) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have hb : SL.blockHom K k (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c) =
          Matrix.SpecialLinearGroup.transvection hne c :=
        Subtype.ext (SL.blockMat_transvection_upper k c)
      refine Units.ext ?_
      change e6Data_valid.endo K (slToE6Sc K (SL.blockHom K k
        (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c))) =
          e6Data_valid.blockOp K (E6Pilot.chainNode k) !![1, c; 0, 1]
      rw [hb, slToE6Sc_transvection_castSucc_succ, e6Data_valid.endo_xm,
        e6Data_valid.blockOp_upper]
    · have hb : SL.blockHom K k (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c) =
          Matrix.SpecialLinearGroup.transvection hne.symm c :=
        Subtype.ext (SL.blockMat_transvection_lower k c)
      refine Units.ext ?_
      change e6Data_valid.endo K (slToE6Sc K (SL.blockHom K k
        (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c))) =
          e6Data_valid.blockOp K (E6Pilot.chainNode k) !![1, 0; c, 1]
      rw [hb, slToE6Sc_transvection_succ_castSucc, e6Data_valid.endo_xm,
        e6Data_valid.blockOp_lower]
  exact congrArg (fun f => ((f M : (Module.End K (Fin e6Data.d →₀ K))ˣ) :
    Module.End K (Fin e6Data.d →₀ K))) hext

theorem slToE6Sc_blockHom_HSL (k : Fin 5) (t : Kˣ) :
    slToE6Sc K (SL.blockHom K k (HSL t)) = e6Data_valid.hm K (E6Pilot.chainNode k) t := by
  apply e6Data_valid.endo_injective K
  rw [endo_slToE6Sc_blockHom, e6Data_valid.endo_hm]
  exact e6Data_valid.blockOp_diag K _ t

theorem exists_slToE6Sc_ne_one : ∃ g, slToE6Sc K g ≠ 1 := by
  have hne : (0 : Fin 6) ≠ 1 := by decide
  refine ⟨Matrix.SpecialLinearGroup.transvection hne 1, ?_⟩
  rw [slToE6Sc_transvection, ← e6Data_valid.xm_zero K (a5Root 0 1)]
  intro h
  exact one_ne_zero (e6Data_valid.xm_injective K (CFSG.Timmesfeld.LieEmbed.isRoot_a5Root hne) h)

theorem ker_slToE6Sc_le_center :
    (slToE6Sc K).ker ≤ center (Matrix.SpecialLinearGroup (Fin 6) K) :=
  CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 5 K (by norm_num)) exists_slToE6Sc_ne_one

theorem slToE6Sc_injective : Function.Injective (slToE6Sc K) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (ker_slToE6Sc_le_center hz)
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  set u : Kˣ := Units.mk0 r hr0 with hu
  have hu6 : u ^ 6 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr,
    Units.val_one])
  have hz' : z = SL.blockHom K (0 : Fin 5) (HSL u) * SL.blockHom K 1 (HSL (u ^ 2)) *
      SL.blockHom K 2 (HSL (u ^ 3)) * SL.blockHom K 3 (HSL (u ^ 4)) *
        SL.blockHom K 4 (HSL (u ^ 5)) := by
    refine Subtype.ext ?_
    rw [E6Pilot.blockHom_HSL_prod_eq hu6, ← hrz, Units.val_mk0]
  have himg : slToE6Sc K z = minTorus e6Data_valid K
      (Pi.mulSingle (E6Pilot.chainNode 0) u * Pi.mulSingle (E6Pilot.chainNode 1) (u ^ 2) *
        Pi.mulSingle (E6Pilot.chainNode 2) (u ^ 3) * Pi.mulSingle (E6Pilot.chainNode 3) (u ^ 4) *
          Pi.mulSingle (E6Pilot.chainNode 4) (u ^ 5)) := by
    rw [hz']
    simp only [map_mul, slToE6Sc_blockHom_HSL, minTorus_mulSingle]
  rw [himg, ← map_one (minTorus e6Data_valid K)] at hz
  have h0 := congrFun (minTorus_injective e6Data_valid K hz) (E6Pilot.chainNode 0)
  have e1 : E6Pilot.chainNode 0 ≠ E6Pilot.chainNode 1 := by decide
  have e2 : E6Pilot.chainNode 0 ≠ E6Pilot.chainNode 2 := by decide
  have e3 : E6Pilot.chainNode 0 ≠ E6Pilot.chainNode 3 := by decide
  have e4 : E6Pilot.chainNode 0 ≠ E6Pilot.chainNode 4 := by decide
  simp only [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne e1, Pi.mulSingle_eq_of_ne e2,
    Pi.mulSingle_eq_of_ne e3, Pi.mulSingle_eq_of_ne e4, mul_one, Pi.one_apply] at h0
  have hr1 : r = 1 := by
    have := congrArg Units.val h0
    rwa [hu, Units.val_mk0, Units.val_one] at this
  refine Subtype.ext ?_
  rw [← hrz, hr1, map_one]
  rfl

theorem range_slToE6Sc : (slToE6Sc K).range = e6ScLevi K e6A5Nodes := by
  have hnode : ∀ k : Fin 5, E6Pilot.chainNode k ∈ e6A5Nodes := by decide
  apply le_antisymm
  · rw [MonoidHom.range_eq_map,
      ← CFSG.LieType.Universal.SpecialLinear.iSup_fundamentalRootSubgroup_eq_top (m := 5)
        (F := K), Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    rintro _ ⟨g, hg, rfl⟩
    have hrank : CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup (E6Pilot.chainNode k) ≤
        e6ScLevi K e6A5Nodes := CFSG.LieType.CurtisTits.rankOne_le_levi _ (hnode k)
    cases s
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ g).1 hg
      refine hrank (mem_sup_right ?_)
      rw [show Matrix.SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne' c =
        Matrix.SpecialLinearGroup.transvection (SL.castSucc_ne_succ k).symm c from rfl,
        slToE6Sc_transvection_succ_castSucc]
      exact e6Data_valid.xm_mem_rootGroup K _ c
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ g).1 hg
      refine hrank (mem_sup_left ?_)
      rw [show Matrix.SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne c =
        Matrix.SpecialLinearGroup.transvection (SL.castSucc_ne_succ k) c from rfl,
        slToE6Sc_transvection_castSucc_succ]
      exact e6Data_valid.xm_mem_rootGroup K _ c
  · refine iSup₂_le fun j hj => sup_le ?_ ?_
    · obtain ⟨k, rfl⟩ := exists_chainNode_eq j hj
      intro g hg
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
      exact ⟨_, slToE6Sc_transvection_castSucc_succ k c⟩
    · obtain ⟨k, rfl⟩ := exists_chainNode_eq j hj
      intro g hg
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
      exact ⟨_, slToE6Sc_transvection_succ_castSucc k c⟩

end Hom

end CFSG.SeitzReduction.F4Pilot
