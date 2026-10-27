module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KDBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDLoc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDLocFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDClassZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDClassK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDClassInv

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

@[expose] noncomputable def kdBase : KDBase ctx.A ctx.C where
  x := ctx.S.x₀
  y := ctx.S.y₀
  x_mem := ctx.S.x₀_mem
  y_mem := ctx.S.y₀_mem
  orderOf_x := ctx.S.orderOf_x₀
  y_sq := ctx.S.y₀_sq
  y_inv := ctx.S.y₀_x₀_y₀
  d_y := ctx.d_y
  d_xy := ctx.d_xy
  k_fixed := ctx.k_fixed
  zk_fixed := ctx.zk_fixed
  card_conj_z := ctx.card_conj_z
  card_conj_k := ctx.card_conj_k
  not_conj_k_tk := ctx.not_conj_k_tk
  inv_classes := ctx.inv_classes

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx
