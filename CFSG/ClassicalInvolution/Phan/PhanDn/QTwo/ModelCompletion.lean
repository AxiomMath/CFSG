module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParab
public import CFSG.LieType.CurtisTits.TitsGeometryRetained
import CFSG.LieType.CurtisTits.AmalgamTransport
import CFSG.ClassicalInvolution.Phan.PhanDn.FlagTransitive
import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidue

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem qTwoParab_isUniversalCompletion (m : ℕ) (hm : 3 ≤ m)
    (hconn : (flagGraph (unitaryInvolution K 2 1) m).Connected)
    (htri : CFSG.Monster.B.Recog.Triangulable (flagGraph (unitaryInvolution K 2 1) m))
    (hres : ∀ J : Set (Fin (m + 1)), J.Nonempty →
      Jᶜ ∉ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1)) →
      (residueGraph (flagGraph (unitaryInvolution K 2 1) m) flagTyp (flagChamber E m)
          J).Connected ∧
        CFSG.Monster.B.Recog.Triangulable
          (residueGraph (flagGraph (unitaryInvolution K 2 1) m) flagTyp (flagChamber E m) J)) :
    IsUniversalCompletion.{0, 0, 0}
      (fun C : ↥(qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1))) =>
        qTwoParab E m C.1) := by
  refine IsUniversalCompletion.cotype
    (Q := fun J => parabolic ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))
      (flagChamber E m) J) (fun C hC => hC.1) ?_
  exact tits_geometry_isUniversalCompletion_of_retained (flagTyp_flagChamber E)
    (flagTyp_smul E) (flagTyp_ne_of_adj E.isUnitary.invol (by omega)) (flagGraph_adj_smul E)
    (fun _ _ hij => flagChamber_adj E hij) (flagTransitive_flagGraph E hm) hconn htri
    {J | Jᶜ ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1))}
    (fun J hJ => Set.nonempty_iff_ne_empty.mpr fun h => hJ.1 (by rw [h, Set.compl_empty]))
    (fun _ _ hJ h => qTwoShape_mono hJ (Set.compl_subset_compl.mpr h)) hres

end CFSG.ClassicalInvolution.PhanDn.QTwo
