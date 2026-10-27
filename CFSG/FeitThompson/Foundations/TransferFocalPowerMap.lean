module

public import CFSG.FeitThompson.Foundations.FocalGeneratorSet
public import CFSG.FeitThompson.Foundations.TransferRightTransversalIndependent
public import CFSG.FeitThompson.Foundations.CosetRepresentativeMultiplication
import CFSG.FeitThompson.Foundations.TransferAbelianQuotientHom

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup
open scoped IsMulCommutative

variable {G : Type*} [Group G] {P : Subgroup G} {T : Set G} {Q : Type*} [CommGroup Q]

theorem finite_of_isComplement_coe [P.FiniteIndex] (hT : IsComplement (P : Set G) T) : Finite T :=
  Nat.finite_of_card_ne_zero (by rw [hT.card_right]; exact P.index_ne_zero_of_finite)

theorem rightTransversalRepr_mul_eq_transversalAct (T : P.RightTransversal)
    (t : (T : Set G)) (g : G) :
    rightTransversalRepr T ((t : G) * g) = (transversalAct T.2 t g : G) := by
  rw [rightTransversalRepr_congr T (show (transversalAct T.2 t g : G) * ((t : G) * g)⁻¹ ∈ P from by
    simpa using P.inv_mem (mul_mul_transversalAct_inv_mem T.2 t g))]
  exact rightTransversalRepr_eq_self T (transversalAct T.2 t g).2

theorem rightTransfer_eq_transversalTransfer (f : P →* Q) (T : P.RightTransversal) (g : G) :
    rightTransfer f T g = transversalTransfer T.2 f g := by
  rw [rightTransfer_eq_finprod, transversalTransfer_eq_finprod]
  refine finprod_congr fun t => ?_
  congr 1
  exact Subtype.ext <| by
    rw [coe_rightTransversalCocycle, coe_transversalCocycle,
      rightTransversalRepr_mul_eq_transversalAct]

theorem transversalTransfer_comp (hT : IsComplement (P : Set G) T) [Finite T] (f : P →* Q)
    {Q' : Type*} [CommGroup Q'] (φ : Q →* Q') (g : G) :
    transversalTransfer hT (φ.comp f) g = φ (transversalTransfer hT f g) := by
  have : Fintype T := Fintype.ofFinite T
  rw [transversalTransfer_eq_prod, transversalTransfer_eq_prod, map_prod]
  rfl

theorem transversalTransfer_focalSubgroupOf_eq_pow [P.FiniteIndex]
    (hT : IsComplement (P : Set G) T) (u : P) :
    transversalTransfer hT (mk' (focalSubgroupOf P)) (u : G)
      = mk' (focalSubgroupOf P) u ^ P.index := by
  rw [transversalTransfer_eq_transfer,
    show MonoidHom.transfer (mk' (focalSubgroupOf P)) (u : G) = P.transferFocal (u : G) from rfl,
    Subgroup.transferFocal_eq_pow]
  rfl

theorem transversalTransfer_eq_pow_of_focalSubgroupOf_le [P.FiniteIndex]
    (hT : IsComplement (P : Set G) T) (f : P →* Q) (hf : focalSubgroupOf P ≤ f.ker) (u : P) :
    transversalTransfer hT f (u : G) = f u ^ P.index := by
  have : Finite T := finite_of_isComplement_coe hT
  have hcomp : f = (QuotientGroup.lift (focalSubgroupOf P) f hf).comp (mk' (focalSubgroupOf P)) :=
    MonoidHom.ext fun x => by simp
  rw [hcomp, transversalTransfer_comp, transversalTransfer_focalSubgroupOf_eq_pow, map_pow]
  simp

theorem transversalTransfer_focalGeneratorSet_eq_pow [P.FiniteIndex]
    (hT : IsComplement (P : Set G) T) (u : P) :
    transversalTransfer hT (mk' ((closure (focalGeneratorSet P)).subgroupOf P)) (u : G)
      = mk' ((closure (focalGeneratorSet P)).subgroupOf P) u ^ P.index :=
  transversalTransfer_eq_pow_of_focalSubgroupOf_le hT _
    (by rw [QuotientGroup.ker_mk', subgroupOf_closure_focalGeneratorSet]) u

theorem transversalTransferHom_focalSubgroupOf_apply_eq_pow [P.FiniteIndex]
    (hT : IsComplement (P : Set G) T) [Finite T] (u : P) :
    transversalTransferHom hT (mk' (focalSubgroupOf P)) (u : G)
      = mk' (focalSubgroupOf P) u ^ P.index := by
  rw [transversalTransferHom_apply, transversalTransfer_focalSubgroupOf_eq_pow]

theorem rightTransfer_focalSubgroupOf_eq_pow [P.FiniteIndex] (T : P.RightTransversal) (u : P) :
    rightTransfer (mk' (focalSubgroupOf P)) T (u : G) = mk' (focalSubgroupOf P) u ^ P.index := by
  rw [rightTransfer_eq_transversalTransfer, transversalTransfer_focalSubgroupOf_eq_pow]

theorem rightTransfer_focalGeneratorSet_eq_pow [P.FiniteIndex] (T : P.RightTransversal) (u : P) :
    rightTransfer (mk' ((closure (focalGeneratorSet P)).subgroupOf P)) T (u : G)
      = mk' ((closure (focalGeneratorSet P)).subgroupOf P) u ^ P.index := by
  rw [rightTransfer_eq_transversalTransfer, transversalTransfer_focalGeneratorSet_eq_pow]

end CFSG.FeitThompson
