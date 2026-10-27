module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.SpinModels
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelStrip
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelCompletion
import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidueHres
import CFSG.ClassicalInvolution.Phan.PhanDn.FlagTopQTwo
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoGammaThree
import CFSG.ClassicalInvolution.Phan.PhanDn.D4Q2.Cover
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagGeom

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.CurtisTits


section Model

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem nonempty_qTwoModelD (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) :
    Nonempty (QTwoModelD K (m + 1) ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (by rw [hK]; norm_num)
  have hflag : ∀ m', 2 ≤ m' → (flagGraph (unitaryInvolution K 2 1) m').Connected ∧
      (3 ≤ m' → CFSG.Monster.B.Recog.Triangulable (flagGraph (unitaryInvolution K 2 1) m')) := by
    intro m' hm'
    rcases Nat.lt_or_ge m' 4 with h4 | h4
    · interval_cases m'
      · exact ⟨flagGraph_two_connected_of_card_eq_four hσ hK, fun h => by omega⟩
      · obtain ⟨hc, ht⟩ := D4Q2.flagGraph_three_connected_triangulable hσ hK
        exact ⟨hc, fun _ => ht⟩
    · obtain ⟨hc, ht⟩ := flagGraph_connected_triangulable_of_card_eq_four hσ hK h4
      exact ⟨hc, fun _ => ht⟩
  have hres := fun (J : Set (Fin (m + 1))) (hJ : J.Nonempty)
      (hJS : Jᶜ ∉ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1))) =>
    flagResidue_hres_of_card_four E hm hσ hK (fun m' hm' _ => hflag m' hm') hJ hJS
  exact ⟨{ S := qTwoStdFamily E hK m hm
           faithful := qTwoStdFamily_faithful E hK m hm
           P := qTwoParab E m
           T := qTwoTor E m hm
           completion := qTwoParab_isUniversalCompletion E m hm (hflag m (by omega)).1
             ((hflag m (by omega)).2 hm) hres
           strip := qTwoStrip E hK m hm }⟩

end Model

theorem qTwoOmegaModelsD_holds : QTwoOmegaModelsD :=
  fun _ _ _ _ _ E hK m hm => nonempty_qTwoModelD E hK m hm

theorem ghnsMainBQTwo_holds : GHNSMainBQTwo :=
  ghnsMainBQTwo_of_omegaModels qTwoOmegaModelsD_holds

end CFSG.ClassicalInvolution.PhanDn.QTwo
