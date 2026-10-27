module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParab
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyTorus

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem map_qTwoTor_iSup_eq_diagTorus (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) :
    Subgroup.map
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
        (⨆ i, qTwoTor E m hm i) =
      diagTorusV F (unitaryInvolution K 2 1) (m + 1) := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  rw [← torus_stdFamilyV E m hm hK',
    CFSG.ClassicalInvolution.Phan.PhanE.PhanFamilyE.torus, Subgroup.map_iSup]
  exact iSup_congr fun i => by
    rw [qTwoTor, MonoidHom.map_range]
    rfl

end CFSG.ClassicalInvolution.PhanDn.QTwo
