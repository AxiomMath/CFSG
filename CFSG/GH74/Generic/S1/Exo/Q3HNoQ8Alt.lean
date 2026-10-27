module

public import CFSG.GH74.Filter.ClassicalOdd.Basic
public import CFSG.ClassicalInvolution.TwoGroupCase.Q8

public section

namespace CFSG.GH74.Generic.S1.Exo

theorem no_q8_perm {n : ℕ} (hn : n < 8) (ψ : CFSG.GH74.Filter.ClassicalOdd.Q8 →* Equiv.Perm (Fin n))
    (hψ : Function.Injective ψ) : False :=
  CFSG.ClassicalInvolution.q8_not_faithful_perm hn ψ hψ

theorem no_q8_of_alt7 {S : Type} [Group S] (e : S ≃* ↥(alternatingGroup (Fin 7)))
    (ψ : CFSG.GH74.Filter.ClassicalOdd.Q8 →* S) (hψ : Function.Injective ψ) : False :=
  no_q8_perm (n := 7) (by norm_num) ((alternatingGroup (Fin 7)).subtype.comp (e.toMonoidHom.comp ψ))
    ((alternatingGroup (Fin 7)).subtype_injective.comp (e.injective.comp hψ))

end CFSG.GH74.Generic.S1.Exo
