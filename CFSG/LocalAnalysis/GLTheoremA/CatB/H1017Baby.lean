module

public import Certificates.Certificate431004
public import CFSG.Certificates.Kernel.BabyMonster.E35Group
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint


set_option maxRecDepth 100000 in
theorem i1017BabyAttained_holds : I1017BabyAttained := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .B
  obtain ⟨_, _, hx, hg, h⟩ := Certificates.certificate431004
  exact CFSG.KC.BM.E35Group.attained_of_submonoid _ hx hg h (e.trans b.symm)

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
