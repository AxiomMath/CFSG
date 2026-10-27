module

public import CFSG.LocalAnalysis.StandardType.PhanEMinFrob

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.Phan.PhanE

theorem commute_rootOp_of_commute_xm
    {tau : Tag} {D : MinData tau} (hV : D.Valid) {k : Type} [Field k]
    {g : hV.minGroup k} {gamma : Fin tau.rank → ℤ} {c : k} (hc : c ≠ 0)
    (h : Commute g (hV.xm k gamma c)) :
    Commute (hV.endo k g) (D.rootOp k gamma) := by
  have hh := congrArg (hV.endo k) h.eq
  simp only [hV.endo_mul, hV.endo_xm, mul_add, add_mul, mul_one, one_mul] at hh
  have hsc : Commute (hV.endo k g) (c • D.rootOp k gamma) := add_left_cancel hh
  exact (Commute.smul_right_iff₀ hc).mp hsc

theorem commute_xm_of_commute_rootOp
    {tau : Tag} {D : MinData tau} (hV : D.Valid) {k : Type} [Field k]
    {g : hV.minGroup k} {gamma : Fin tau.rank → ℤ}
    (h : Commute (hV.endo k g) (D.rootOp k gamma)) (c : k) :
    Commute g (hV.xm k gamma c) := by
  apply hV.endo_injective k
  have hh := (Commute.one_right (hV.endo k g)).add_right (h.smul_right c)
  simpa only [hV.endo_mul, hV.endo_xm] using hh.eq

theorem commute_xm_baseChange_of_commute_xm_one
    {tau : Tag} {D : MinData tau} (hV : D.Valid) {k E : Type} [Field k] [Field E]
    (iota : k →+* E) {g : hV.minGroup k} {gamma : Fin tau.rank → ℤ}
    (h : Commute g (hV.xm k gamma 1)) (c : E) :
    Commute (minBC hV iota g) (hV.xm E gamma c) := by
  have h1 : Commute (minBC hV iota g) (hV.xm E gamma 1) := by
    simpa only [minBC_xm, map_one] using h.map (minBC hV iota)
  exact commute_xm_of_commute_rootOp hV
    (commute_rootOp_of_commute_xm hV one_ne_zero h1) c

end CFSG.LieType.Steinberg.Minuscule
