module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Bridges1
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Bridges2
public import CFSG.LocalAnalysis.GLTheoremA.S4.StepTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace Sec13Comp

variable {G : Type} [Group G] [Finite G]

@[expose] def summands (p : ℕ) (M D : Subgroup G) : Set (Subgroup G) :=
  {L | GLAPComponent p M L ∧ ¬ barX p M (gammaStar p D) ≤
    Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M))}

theorem Iof_eq_sSup (p : ℕ) (M D : Subgroup G) : Iof p M D = sSup (summands p M D) := by
  rw [sSup_eq_iSup]
  rfl

theorem isSubnormal_Iof {p : ℕ} (hp : p.Prime) (M D : Subgroup G) :
    IsSubnormal (Iof p M D) M := by
  rw [Iof_eq_sSup]
  exact CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp _ fun _ h => h.1

theorem glaPComponent_of_Iof {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (hL : GLAPComponent p (Iof p M D) L) : GLAPComponent p M L :=
  CFSG.LocalAnalysis.GLTheoremA.glaPComponent_of_isSubnormal' hp (isSubnormal_Iof hp M D) hL

theorem mem_summands_of_Iof {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (hL : GLAPComponent p (Iof p M D) L) : L ∈ summands p M D :=
  CFSG.LocalAnalysis.GLTheoremA.mem_of_le_sSup_glaPComponent hp (summands p M D)
    (fun _ h => h.1) (glaPComponent_of_Iof hp hL) (by rw [← Iof_eq_sSup]; exact hL.1)

end Sec13Comp

theorem sec13_comp_holds : Sec13_compStatement := by
  intro G _ _ m p B M E A D T L h hL
  have hp : p.Prime := h.standing.prime
  exact ⟨Sec13Comp.glaPComponent_of_Iof hp hL, (Sec13Comp.mem_summands_of_Iof hp hL).2⟩

section Cor135ii

set_option linter.unusedSectionVars false

theorem lemma135_ii_of_inputs''
    (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) : Lemma135_iiStatement :=
  lemma135_ii_of_inputs' hP95 h111 h121 sec13_comp_holds

end Cor135ii

theorem lemma136_of_inputs'' (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hP1 : Lemma136.P1BarInput)
    (hO2 : Cex134_O2Statement) (h121c : Prop121_corStatement) (hII : Lemma136.IIHardInput) :
    Lemma136Statement :=
  lemma136_of_inputs' hP95 h111 h121 sec13_comp_holds hP1 hO2 h121c hII

theorem prop134_of_cex_of_inputs' (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (h136 : Lemma136Statement)
    (hI23 : Input23_2AutStatement) (hO2 : Cex134_O2Statement) :
    Prop134_of_cexStatement :=
  prop134_of_cex_of_inputs hP95 h111 h121 h136 hI23 hO2 sec13_comp_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
