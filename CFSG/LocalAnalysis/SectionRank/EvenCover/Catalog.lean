module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.LocalAnalysis.SectionRank.QuasisimpleCatalog
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.SectionRank.EvenCover

open CFSG.Assembly.LowTwoRank

theorem catalog_classical_even
    : CatalogClassicalEvenHyp := by
  intro L _ _ hL hSQT hodd t n f h
  cases t with
  | PSL => exact even_linear_odd_cover_catalog_step hL hSQT hodd h
  | PSU =>
    obtain rfl := even_unitary_SQT_degree_three_bound hL hSQT hodd h
    exact even_unitary_three_odd_cover_catalog_step hL hSQT hodd h
  | PSp => exact (even_symplectic_odd_cover_catalog_step hL hodd h).2 hSQT
  | POmegaOdd => exact (h.1.2.2.2 rfl).elim
  | POmegaPlus => exact (even_split_orthogonal_odd_cover_catalog_step hL hodd h).2 hSQT
  | POmegaMinus => exact (even_nonsplit_orthogonal_odd_cover_catalog_step hL hodd h).2 hSQT
  | _ => exact h.2.elim

end CFSG.SectionRank.EvenCover
