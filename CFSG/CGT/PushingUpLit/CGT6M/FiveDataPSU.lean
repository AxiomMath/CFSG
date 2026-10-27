module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveHeisTransfer
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartOne.S11c.UnitaryFiveData
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

theorem heisData_PSU3_5 {Q : Type} [Group Q] (hQ : CFSG.Open.StatedClassicalModel Q .PSU 3 5 1) :
    HeisData Q := by
  have hQ' : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSU 3 5 1 := hQ
  obtain ⟨x, y, -, -, -, hx, hy, hcx, hcy, -, hz1, -⟩ :=
    CFSG.RankThree.PartOne.HNRed.unitary_three_five_heisenberg_data hQ'
  have hcard := (CFSG.RankThree.Classical.unitary_three_five_model Q hQ').1
  exact ⟨x, y, hx, hy, hcx, hcy, hz1, by rw [hcard]; norm_num⟩

end CFSG.CGT.PushingUpLit.CGT6M
