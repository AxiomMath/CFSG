module

public import CFSG.GH74.QTGen4.Ch7.Rows711
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsCh7

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsCh7S331
public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.GH74 CFSG.GH74.QTGen4.Ch7
open scoped IsMulCommutative

theorem stmt7_0_1_F4_holds (hmod : StmtFSUModule) (hshape : Stmt7_0_1_shapeC)
    (h711 : CFSG.Quasithin.H13.Stmt7_1_1_F4) : Stmt7_0_1_F4 := by
  intro G _ _ T L I hfsu
  obtain ⟨hab, hnorm⟩ := hmod G T L I hfsu
  have hc : IsMulCommutative ↥(fsuV T I) := hab.1
  refine ⟨hc, hab, hnorm, ?_⟩
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hyp : Hyp7_0_2 G T L I :=
    { fsu := hfsu
      notFF := fun _ => h1
      notThree := fun h => h4 ⟨h.1, hshape G T L I hfsu h.1 h.2, h.2⟩
      notOrth := fun _ => h3 }
  obtain ⟨_, hrow⟩ := h711 G T L I hyp
  exact not_rows7_1_1_of_gen4 T L I CFSG.GH74.QTGen4.Finite4.gen4 hab hrow

end CFSG.GH74.QTGen4.Leaves

