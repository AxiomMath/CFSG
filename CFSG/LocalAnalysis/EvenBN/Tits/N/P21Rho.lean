module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LVec

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.LocalAnalysis.EvenBN.Tits.I21L Module

variable {G : Type} [Group G] [Finite G]
  {d : Data G} {z₀ : G}

theorem elemAb2_Ws (h19 : Node19 d z₀) : ElemAb2 ↥(Ws d) := by
  obtain ⟨-, -, -, -, -, -, ⟨hc, hsq⟩, -⟩ := h19
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · exact hc.is_comm.comm a b
  · have := hsq a a.2
    exact Subtype.ext (by simpa [pow_two] using this)

@[expose] noncomputable def rhoI (d : Data G) (hW : ElemAb2 ↥(Ws d)) :
    ↥(Ialpha d) →* (EVec ↥(Ws d) hW ≃ₗ[ZMod 2] EVec ↥(Ws d) hW) :=
  (EVec.mulAutToGL hW).toMonoidHom.comp (Ialpha d).subtype

theorem rhoI_injective (hW : ElemAb2 ↥(Ws d)) : Function.Injective (rhoI d hW) :=
  (EVec.mulAutToGL hW).injective.comp Subtype.val_injective

theorem rhoI_apply (hW : ElemAb2 ↥(Ws d)) (y : ↥(Ialpha d)) (v : EVec ↥(Ws d) hW) :
    rhoI d hW y v = EVec.ofE hW ((y : MulAut ↥(Ws d)) (EVec.toE hW v)) := rfl

theorem finrank_Ws (h19 : Node19 d z₀) :
    finrank (ZMod 2) (EVec ↥(Ws d) (elemAb2_Ws h19)) = 8 :=
  EVec.finrank_eq (elemAb2_Ws h19) h19.2.2.2.2.2.2.2

end CFSG.LocalAnalysis.EvenBN.Tits.N
