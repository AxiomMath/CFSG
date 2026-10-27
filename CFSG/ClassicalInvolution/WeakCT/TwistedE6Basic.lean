module

public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.ClassicalInvolution.WeakCT.SpAut
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary

public noncomputable section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.LieType.Universal CFSG.LieType.CurtisTits MinData.Valid
open CFSG.ClassicalInvolution.Models.TwistedPairs (fixedField liftSL liftSL_injective map_liftSL)
open scoped MatrixGroups

variable {k : Type} [Field k] (θ : k →+* k)

theorem liftSL_tv01 (c : fixedField θ) :
    liftSL θ 2 (tv 0 1 c : SL(2, fixedField θ)) = (tv 0 1 (c : k) : SL(2, k)) := by
  rw [tv01_eq_sl2Upper, tv01_eq_sl2Upper]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> rfl

theorem liftSL_tv10 (c : fixedField θ) :
    liftSL θ 2 (tv 1 0 c : SL(2, fixedField θ)) = (tv 1 0 (c : k) : SL(2, k)) := by
  rw [tv10_eq_sl2Lower, tv10_eq_sl2Lower]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> rfl

theorem slRankOne_lower (a : Fin (Tag.rank .E6)) (c : k) :
    (slRankOne k a (slLower k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c :=
  Subtype.ext (Units.ext (by
    change e6Data_valid.blockOp k a (slLower k c : Matrix (Fin 2) (Fin 2) k) = _
    rw [slLower_val, e6Data_valid.blockOp_lower]
    rfl))

theorem slRankOne_tv01 (a : Fin (Tag.rank .E6)) (c : k) :
    (slRankOne k a (tv 0 1 c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (Pi.single a 1) c := by
  rw [tv01_eq_sl2Upper]
  exact slRankOne_upper a c

theorem slRankOne_tv10 (a : Fin (Tag.rank .E6)) (c : k) :
    (slRankOne k a (tv 1 0 c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c := by
  rw [tv10_eq_sl2Lower]
  exact slRankOne_lower a c

variable (k) in
@[expose] def e6Rank1 (a : Fin (Tag.rank .E6)) : SL(2, k) →* e6Data_valid.minGroup k :=
  (rankOne (e6Data_valid.rootGroup k) a).subtype.comp (slRankOne k a)

theorem e6Rank1_tv01 (a : Fin (Tag.rank .E6)) (c : k) :
    e6Rank1 k a (tv 0 1 c) = e6Data_valid.xm k (Pi.single a 1) c :=
  slRankOne_tv01 a c

theorem e6Rank1_tv10 (a : Fin (Tag.rank .E6)) (c : k) :
    e6Rank1 k a (tv 1 0 c) = e6Data_valid.xm k (-Pi.single a 1) c :=
  slRankOne_tv10 a c

theorem e6Rank1_injective (a : Fin (Tag.rank .E6)) : Function.Injective (e6Rank1 k a) := by
  intro A B h
  have h1 : e6Data_valid.blockOp k a (A : Matrix (Fin 2) (Fin 2) k) =
      e6Data_valid.blockOp k a (B : Matrix (Fin 2) (Fin 2) k) :=
    congrArg (fun g : e6Data_valid.minGroup k => e6Data_valid.endo k g) h
  exact Subtype.ext (e6Data_valid.blockOp_injective k a h1)

theorem sigma_e6Rank1 (a : Fin (Tag.rank .E6)) (A : SL(2, k)) :
    sigma k θ (e6Rank1 k a A) = e6Rank1 k (rhoPerm a) (Matrix.SpecialLinearGroup.map θ A) := by
  have key : (sigma k θ).comp (e6Rank1 k a) =
      (e6Rank1 k (rhoPerm a)).comp (Matrix.SpecialLinearGroup.map θ) := by
    refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
    · simp only [MonoidHom.comp_apply, e6Rank1_tv01, sigma_xm_single, map_tv01]
    · simp only [MonoidHom.comp_apply, e6Rank1_tv10, sigma_xm_neg_single, map_tv10]
  exact DFunLike.congr_fun key A

end CFSG.ClassicalInvolution.WeakCT
