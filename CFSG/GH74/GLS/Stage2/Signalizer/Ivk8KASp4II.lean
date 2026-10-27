module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Easy
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4II

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatFactsSp4
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kaSp4II_thm : KASp4II := by
  intro F _ _ hodd A d hAA hdm hsq
  have hℓ : (ringChar F).Prime := CharP.prime_ringChar F
  have : Fintype F := Fintype.ofFinite F
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, -, hqn⟩ := FiniteField.card F (ringChar F)
  have hK : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hqn
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  have hdsq : ∀ l : F, l ^ 2 ≠ (d : F) := by
    rw [hdm]
    exact hsq
  have hμ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      formJ 2 F * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        (d : F) • formJ 2 F := by
    rw [hdm]
    exact multiplierUnit_spec A
  obtain ⟨hqs, -⟩ := fixOf_conjSp_nonsquare hℓ hodd n.pos hK A hd0 hdsq hAA hμ
  refine kaAll_sp4_of_fix hodd (conjSp 2 F A) (conjAut 2 F A) (fun g => conjAut_proj A g)
    (Subgroup.isPerfect_iff.mp hqs.1) ?_
  refine ka_hRp_of_quasisimple hodd (conjSp 2 F A) hqs fun z hz => ?_
  exact typeII_centralizer_scalar hodd A d hAA hdm hsq z fun g hg => (hz g hg).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
