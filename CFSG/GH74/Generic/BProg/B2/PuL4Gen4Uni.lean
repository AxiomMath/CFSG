module

public import CFSG.GH74.Generic.BProg.B2.PuL4GraphLin
public import CFSG.GH74.Generic.BProg.B2.PuL4Gen4

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial Subgroup

@[expose] def OutGraphUni : Prop :=
  ∀ {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N} {L : Subgroup N}
    {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), ShapeInCent H t L →
    3 < p ^ f → p ^ f % 8 = 3 →
    ∀ e : ↥H ≃* UnitaryHigher.primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
      (∀ A : UnitaryHigher.primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
        MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) ≠
          UnitaryHigher.primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A) →
      SectionalTwoRankLE N 4 → False

section Certified


theorem outGraphL4W_of_uni (huni : OutGraphUni) : PuL4Gen4.OutGraphL4W :=
  ⟨by
    intro N _ _ H _ t L F _ _ hs hF8 e hnd h4
    exact PuL4GraphLin.outGraph_lin H hs hF8 e hnd h4, huni⟩

theorem puL4m_of_gen4_uni (huni : OutGraphUni) {N : Type} [Group N] [Finite N]
    (H : Subgroup N) (t : N) (L : Subgroup N) (hs : ShapeInCent H t L)
    (h4 : SectionalTwoRankLE N 4) (hJ : PuL4 ↥H) : PuL4m ↥H :=
  puL4m_of_gen4 (outGraphL4W_of_uni huni) H t L hs h4 hJ

end Certified

end CFSG.GH74.Generic.BProg.B2
