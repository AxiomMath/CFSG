module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueCore
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueGW
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchDValueData
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchStatement

public section

namespace CFSG.Semidihedral.UnitaryDValue.DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem d_value_of_m_eq_two
    (hm : D.m = 2) (hext : D.CharacterExtend)
    (htriv : D.CharacterTrivial) (hpair : D.PrincipalPair) :
    D.m * Nat.card D.A * Nat.gcd (D.q + 1) 3 = D.q + 1 :=
  D.d_value hext htriv hpair (D.gwStep_of_m_eq_two hm)

end CFSG.Semidihedral.UnitaryDValue.DValueData

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem dValue_of_centralizerCharacterTrivial
    (h : CentralizerCharacterTrivialStatement) :
    DValueStatement := by
  intro G _ _ _ hGnonab hrec n hn S fS t ht _ hLnonab hcentral hnc p f hp hpodd hf hq4 hq5 hmodel
    hcov hY hA₀
  obtain ⟨_, D, hm, hpD, hfD, hA, hext, htriv, hpair⟩ := exists_dValueData h G hGnonab hrec n hn
    S fS t ht hLnonab hcentral hnc p f hp hpodd hf hq4 hq5 hmodel hcov hY hA₀
  have key := D.d_value_of_m_eq_two hm hext htriv hpair
  have hq : D.q = p ^ f := by
    show D.p ^ D.f = p ^ f
    rw [hpD, hfD]
  rw [hm, hA, hq] at key
  exact key

end CFSG.Semidihedral.UnitaryBranch
