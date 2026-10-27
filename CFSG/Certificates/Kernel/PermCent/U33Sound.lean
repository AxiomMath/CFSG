module

public import CFSG.Certificates.Kernel.PermCent.CVSound
public import Certificates.Data.Kernel.PermCent.U33Twin

public section

namespace CFSG.Certificates.Kernel.PkCV.U33T

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.U33
  CFSG.LargeExtraspecial

theorem invConj_eq : AS35YR.u33InvConjCheck = invConjC := by
  unfold AS35YR.u33InvConjCheck invConjC
  conv_lhs => rw [eq_ev_cOf AS35YR.u33d0, elemsT_eq_elemsC]
  simp only [List.all_map, List.any_map, Function.comp_def, ev_mul', ev_inv', one_eq_ev, beq_ev]

theorem elem_eq : AS35YS.u33ElemCheck = elemC := by
  unfold AS35YS.u33ElemCheck elemC elemAt
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.all_map, List.any_map, Function.comp_def, ev_mul', ev_inv', one_eq_ev, beq_ev,
    List.all_filter, List.any_filter, Bool.or_assoc, Bool.not_not, decide_ev_eq]

open S63 in
theorem two_ev (x : CV 28) : u33Two (ev x) = twoC x := by
  simp only [u33Two, twoC, ev_pow', one_eq_ev, decide_ev_eq]

open S63 in
theorem cent_ev (L : List (CV 28)) (s : CV 28) :
    u33Cent (L.map ev) (ev s) = (centC L s).map ev := by
  simp only [u33Cent, centC, List.filter_map, Function.comp_def, ev_mul', decide_ev_eq]

open S63 in
theorem core_ev (C : List (CV 28)) : u33Core (C.map ev) = (coreC C).map ev := by
  simp only [u33Core, coreC, List.filter_map, List.all_map, Function.comp_def, tab_eq, ev_mul',
    ev_inv', ev_pow', one_eq_ev, decide_ev_eq, two_ev]

open S63 in
theorem invCheck_ev (L : List (CV 28)) (s : CV 28) :
    u33InvCheck (L.map ev) (ev s) = invCheckC L s := by
  simp only [u33InvCheck, invCheckC, cent_ev, core_ev, List.length_map, List.all_map,
    List.any_map, List.any_cons, List.any_nil, Function.comp_def, ev_mul', one_eq_ev,
    decide_ev_eq]

theorem centCheck_eq : S63.u33CentCheck = (elemsC QP).all centAtC := by
  unfold S63.u33CentCheck centAtC
  rw [elemsT_eq_elemsC, List.all_map]
  simp only [Function.comp_def, ev_mul', one_eq_ev, decide_ev_eq, invCheck_ev]

open CFSG.LieType.ChevTwo.OppCl.U33Fin

theorem invsOf_ev (L : List (CV 28)) : invsOf (L.map ev) = (invsOfC L).map ev := by
  simp only [invsOf, invsOfC, List.filter_map, Function.comp_def, ev_mul', one_eq_ev, beq_ev,
    beq_cv, bne_def']

theorem o3Of_ev (L : List (CV 28)) : o3Of (L.map ev) = (o3OfC L).map ev := by
  simp only [o3Of, o3OfC, List.filter_map, Function.comp_def, ev_pow', one_eq_ev, beq_ev,
    beq_cv, bne_def']

theorem center_eq : checkCenter () = centerC := by
  unfold checkCenter elems centerC
  conv_lhs => rw [eq_ev_cOf pa, eq_ev_cOf pb, elemsT_eq_elemsC]
  simp only [List.all_map, Function.comp_def, ev_mul', one_eq_ev, beq_ev, beq_cv]

theorem exp_eq : checkExp () = expC := by
  unfold checkExp elems expC
  rw [elemsT_eq_elemsC]
  simp only [List.all_map, Function.comp_def, ev_pow', one_eq_ev, beq_ev, beq_cv]

theorem f1_eq : checkF1 () = f1C (elemsC QP) (invsOfC (elemsC QP)) := by
  unfold checkF1 elems
  rw [elemsT_eq_elemsC, invsOf_ev]
  simp only [checkF1', f1C, List.all_map, Function.comp_def, ev_pow', ev_mul', one_eq_ev, beq_ev,
    beq_cv, bne_def']

theorem f3_eq : checkF3 () = f3C (invsOfC (elemsC QP)) (o3OfC (elemsC QP)) := by
  unfold checkF3 elems
  rw [elemsT_eq_elemsC, invsOf_ev, o3Of_ev]
  simp only [checkF3', f3C, List.all_map, List.any_cons, List.any_nil, Function.comp_def,
    ev_mul', one_eq_ev, beq_ev, beq_cv, bne_def']

theorem x5_eq : checkX5 () = x5C (elemsC QP) (invsOfC (elemsC QP)) (o3OfC (elemsC QP)) := by
  unfold checkX5 elems
  rw [elemsT_eq_elemsC, invsOf_ev, o3Of_ev]
  simp only [checkX5', x5C, checkX5g, x5gC, List.all_map, List.any_map, List.filter_map,
    Function.comp_def, ev_mul', ev_inv', ev_pow', one_eq_ev, beq_ev, beq_cv, bne_def']

open CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin

theorem closureStep_ev (gs L : List (CV 28)) :
    closureStep (gs.map ev) (L.map ev) = (closureStepC gs L).map ev := by
  unfold closureStep closureStepC
  rw [← dedup_map_ev]
  congr 1
  simp only [List.map_append, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, ev_mul]

theorem t0L_eq : T0L () = t0LC.map ev := by
  unfold T0L t0LC
  have key : ∀ (r : List Nat) (L : List (CV 28)),
      r.foldl (fun L _ => closureStep [ta, tb] L) (L.map ev) =
        (r.foldl (fun L _ => closureStepC [cOf ta, cOf tb] L) L).map ev := by
    intro r
    induction r with
    | nil => intro L; rfl
    | cons x r ih =>
      intro L
      simp only [List.foldl_cons]
      have h : closureStep [ta, tb] (L.map ev) = (closureStepC [cOf ta, cOf tb] L).map ev := by
        rw [← closureStep_ev]
        simp only [List.map_cons, List.map_nil, ev_cOf]
      rw [h, ih]
  have h1 : ([1] : List (Equiv.Perm (Fin 28))) = [(1 : CV 28)].map ev := by
    simp only [List.map_cons, List.map_nil, ev_one]
  rw [h1, key]

theorem t0_eq : checkT0 () = t0C := by
  unfold checkT0 t0C elems
  rw [t0L_eq, elemsT_eq_elemsC]
  simp only [List.length_map, nodup_map_ev, one_eq_ev, contains_map_ev, contains_cv, List.all_map,
    Function.comp_def, ev_inv', ev_mul']

theorem z_eq : checkZ () = zC := by
  unfold checkZ zC zL
  rw [t0L_eq]
  conv_lhs => rw [eq_ev_cOf z0]
  simp only [List.length_map, one_eq_ev, contains_map_ev, contains_cv, List.all_map,
    Function.comp_def, ev_mul', ev_pow', beq_ev, beq_cv, bne_def', List.contains_cons,
    List.contains_nil, List.elem_cons, List.elem_nil]

theorem c_eq : checkC () = cC := by
  rw [checkC.eq_1, cC.eq_1, elems.eq_1, t0.eq_1]
  have h : ((elemsT QP).filter fun x => x * z0 ^ 2 == z0 ^ 2 * x) =
      ((elemsC QP).filter fun x => x * cOf z0 ^ 2 == cOf z0 ^ 2 * x).map ev := by
    rw [elemsT_eq_elemsC, List.filter_map]
    refine congrArg (List.map ev) (congrArg (fun p => List.filter p (elemsC QP)) (funext fun x => ?_))
    simp only [Function.comp_apply]
    conv_lhs => rw [eq_ev_cOf z0]
    rw [ev_pow', ev_mul', ev_mul', beq_ev, beq_cv]
  rw [h, List.length_map]

theorem e1_eq : checkE1 () = e1C := by
  unfold checkE1 e1C elems zL t0
  rw [t0L_eq]
  conv_lhs => rw [eq_ev_cOf z0, elemsT_eq_elemsC]
  simp only [one_eq_ev, contains_map_ev, contains_cv, List.all_map, Function.comp_def, ev_mul',
    ev_pow', beq_ev, beq_cv, bne_def', List.contains_cons, List.contains_nil, List.elem_cons,
    List.elem_nil]

theorem sylow7_eq : ((elemsT QP).filter fun g =>
      (List.range 7).any fun i => decide (g * (pa * pb) * g⁻¹ = (pa * pb) ^ i)).length =
    ((elemsC QP).filter fun g => (List.range 7).any fun i =>
      decide (g * (cOf pa * cOf pb) * g⁻¹ = (cOf pa * cOf pb) ^ i)).length := by
  conv_lhs => rw [eq_ev_cOf pa, eq_ev_cOf pb, elemsT_eq_elemsC]
  simp only [List.filter_map, List.length_map, Function.comp_def, ev_mul', ev_inv', ev_pow',
    decide_ev_eq]

end CFSG.Certificates.Kernel.PkCV.U33T

end
