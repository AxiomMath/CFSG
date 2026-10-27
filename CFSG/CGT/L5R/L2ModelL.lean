module

public import CFSG.CGT.L5R.L2FBL2
public import CFSG.CGT.L5R.L2FCL2
public import CFSG.CGT.L5R.L2GModelL

public section

namespace CFSG.CGT.L5R

open CFSG.CGT.M24R

theorem lift_mk_pos2 {K : Type*} [Group K] (f : Fin 2 → K) (l : List (Fin 2)) :
    FreeGroup.lift f (FreeGroup.mk (l.map fun k => (k, true))) = wv2 f l := by
  simp [wv2, FreeGroup.lift_mk, List.map_map, Function.comp_def]

@[expose] noncomputable def l2ModelL
    (hcard : Nat.card N8 = 322560) : T1ModelL N8 where
  T0 := T8
  B0 := B8L
  b0 := bL 0
  c0 := gL
  d := dL
  theta := thL
  z1 := z1L
  z2 := z2L
  b0_mem := bL_mem_B8L
  b0_ne := bL_ne_one
  d_mem := dL_mem hcard
  theta_mem := thL_mem hcard
  z1_mem := z1L_mem hcard
  z2_mem := z2L_mem hcard
  z1_conj := ⟨nzL, z1_conj hcard⟩
  z2_notMem := z2_notMem hcard
  z2_card := z2_card hcard
  inv_class := inv_classL hcard
  klein_eq := fun B' hb hadm =>
    klein_eqL hcard B' hb hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2
  klein_none := fun B' hg hadm =>
    klein_noneL hcard B' hg hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2
  swap := swapL hcard
  center := centerL hcard
  theta_sq := ⟨fun i => (thDW i).map fun j => (j, true), fun i => by
    rw [lift_mk_pos2, lift_mk_pos2]
    exact theta_wordsL hcard i⟩

end CFSG.CGT.L5R
