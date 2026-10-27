module

public import CFSG.CGT.M24R.L2FA
public import CFSG.CGT.M24R.L2FB
public import CFSG.CGT.M24R.L2FC2
public import CFSG.CGT.M24R.L2GModel8

public section

namespace CFSG.CGT.M24R

theorem lift_mk_pos {K : Type*} [Group K] (f : Fin 3 → K) (l : List (Fin 3)) :
    FreeGroup.lift f (FreeGroup.mk (l.map fun k => (k, true))) = wv f l := by
  simp [wv, FreeGroup.lift_mk, List.map_map, Function.comp_def]

@[expose] noncomputable def l2Model8
    (hcard : Nat.card N8 = 322560) : T1Model8 N8 3 where
  T0 := T8
  B0 := B8
  b0 := bb0
  d := d8
  theta := th8
  b0_mem := Subgroup.subset_closure (by simp)
  d_mem := d8_mem hcard
  theta_mem := th8_mem hcard
  inv_class := inv_class8 hcard
  klein_eq := klein_eq8 hcard
  swap := swap8 hcard
  center := center8 hcard
  theta_sq := ⟨fun i => (thWord i).map fun j => (j, true), fun i => by
    rw [lift_mk_pos, lift_mk_pos]
    exact theta_words8 hcard i⟩

end CFSG.CGT.M24R
