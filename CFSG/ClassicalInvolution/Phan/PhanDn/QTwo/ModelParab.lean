module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.StdFamily
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagGeom
public import CFSG.LieType.CurtisTits.TitsGeometry

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

@[expose] noncomputable def qTwoParab (m : ℕ) (C : Set (Fin (m + 1))) :
    Subgroup ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
  CFSG.LieType.CurtisTits.parabolic _ (flagChamber E m) Cᶜ

@[expose] noncomputable def qTwoTor (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    Subgroup ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
  ((qTwoStdIota E m hm i).comp (torusTwo (unitaryInvolution K 2 1))).range

theorem mem_qTwoParab {m : ℕ} {C : Set (Fin (m + 1))}
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))} :
    x ∈ qTwoParab E m C ↔ ∀ j ∉ C, x • flagChamber E m j = flagChamber E m j := by
  simp only [qTwoParab, CFSG.LieType.CurtisTits.parabolic, Subgroup.mem_iInf,
    MulAction.mem_stabilizer_iff, Set.mem_compl_iff]

end CFSG.ClassicalInvolution.PhanDn.QTwo
