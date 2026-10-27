module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum

open CFSG.Blueprint.Chevalley


theorem step_comp_conj_g0_inv {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L) :
    D.step.comp (MulAut.conj D.g0⁻¹).toMonoidHom =
      (MulAut.conj D.g0⁻¹).toMonoidHom.comp D.Φ := by
  refine MonoidHom.ext fun y => ?_
  change D.n * D.Φ (D.g0⁻¹ * y * D.g0) * D.n⁻¹ = D.g0⁻¹ * D.Φ y * D.g0
  rw [map_mul, map_mul, map_inv, D.lang]
  group

end CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum
