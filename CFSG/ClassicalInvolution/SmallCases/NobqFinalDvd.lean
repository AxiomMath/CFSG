module

public import CFSG.ClassicalInvolution.SmallCases.NobqA7
public import CFSG.ClassicalInvolution.SmallCases.NobqAlt
public import CFSG.ClassicalInvolution.SmallCases.NobqL2
public import CFSG.ClassicalInvolution.SmallCases.NobqL34
public import CFSG.ClassicalInvolution.SmallCases.NobqLy
public import CFSG.ClassicalInvolution.SmallCases.NobqSmall
public import CFSG.ClassicalInvolution.SmallCases.NobqSporadic
public import CFSG.ClassicalInvolution.SmallCases.NobqSz
public import CFSG.ClassicalInvolution.SmallCases.NobqU3

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

theorem noDatum_Ly_of_dvd (hOut : Nat.card (Outer NativeSporadic.Ly) ∣ 2) (F : Type) [Group F]
    (h : NativeSporadic.IsSporadic F .Ly) : NoDatum F := by
  obtain ⟨e⟩ := h
  have : Finite NativeSporadic.Ly := Finite.of_equiv _ CFSG.Sporadic.Ly.lyEquivJ.symm.toEquiv
  exact NoDatum.of_mulEquiv e (noDatum_of_noUniqueInvNormal noUniqueInvNormal_Ly
    (OutTwoCyclic.of_card_le_two (F := NativeSporadic.Ly) (Nat.le_of_dvd two_pos hOut)))

theorem smallNoDatum_of_dvd (hOut : Nat.card (Outer NativeSporadic.Ly) ∣ 2) : SmallNoDatum where
  a7 := noDatum_alternating_seven
  psu34 := noDatum_of_statedPSU
  psl28 := fun F _ hF => noDatum_of_lieModel_psl_two_even F hF
  psl216 := fun F _ hF => noDatum_of_lieModel_psl_two_even F hF
  psl34 := fun F _ hF => noDatum_of_lieModel_psl_three_two F hF
  sz8 := fun F _ hF => noDatum_of_lieModel_twistedB2 F hF
  alt := noDatum_alternating
  m22 := noDatum_M22
  m23 := noDatum_M23
  j1 := noDatum_J1
  j2 := noDatum_J2
  j3 := noDatum_J3
  mcl := noDatum_McL
  ly := noDatum_Ly_of_dvd hOut

theorem normalOddByQuaternionSmall_of_outLy_dvd (hGH : GH74SectionalModels)
    (hOut : Nat.card (Outer NativeSporadic.Ly) ∣ 2) :
    NormalOddByQuaternionUnder fun {G} _ _ _ => TwoSubgroupsFourGenerated (genFittingFStar G) :=
  normalOddByQuaternionSmall_of_gh74 hGH (smallNoDatum_of_dvd hOut)

end CFSG.ClassicalInvolution.Nobq
