module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCE
public import Certificates.Certificate12619
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4Schreier CFSG.Quasithin.J4M2 Matrix
open scoped Classical

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_centralizer_cE_le (_hF : J4Facts) :
    Nat.card ↥(Subgroup.centralizer ({cE} : Set J)) ≤ 2661120 :=
  Certificates.certificate12619

section Final2

theorem centralizer_cE_eq (hF : J4Facts) :
    Subgroup.centralizer ({cE} : Set J) = M2 ⊓ Subgroup.centralizer ({cE} : Set J) ∧
      Nat.card ↥(Subgroup.centralizer ({cE} : Set J)) = 2661120 := by
  have h1 := card_centralizer_cE_M2 hF
  have h2 := card_centralizer_cE_le hF
  have heq : M2 ⊓ Subgroup.centralizer ({cE} : Set J) = Subgroup.centralizer ({cE} : Set J) :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
  exact ⟨heq.symm, by rw [← heq]; exact h1⟩

end Final2

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
