module

public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.ClassicalInvolution.SmallCases.NobqM22
public import CFSG.ClassicalInvolution.SmallCases.NobqM23
public import CFSG.ClassicalInvolution.SmallCases.NobqJ1
public import CFSG.ClassicalInvolution.SmallCases.NobqJ2
public import CFSG.ClassicalInvolution.SmallCases.NobqMcL
public import CFSG.ClassicalInvolution.SmallCases.NobqJ3
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairMcLOut
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem outTwoCyclic_M22 : OutTwoCyclic NativeSporadic.M22 :=
  OutTwoCyclic.of_card_le_two (card_outer_le_two_of_card_mulAut_le
    CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card)

theorem outTwoCyclic_M23 : OutTwoCyclic NativeSporadic.M23 :=
  OutTwoCyclic.of_card_le_two CFSG.Sporadic.Schreier.at_m23_schreier.1

theorem outTwoCyclic_J1 : OutTwoCyclic NativeSporadic.J1 :=
  OutTwoCyclic.of_card_le_two (by rw [CFSG.Sporadic.Schreier.at_j1_schreier.1]; norm_num)

theorem outTwoCyclic_J2 : OutTwoCyclic NativeSporadic.J2 :=
  OutTwoCyclic.of_card_le_two CFSG.ComponentClassification.J2Cover.at_j2_schreier.1

theorem outTwoCyclic_J3 : OutTwoCyclic NativeSporadic.J3 :=
  OutTwoCyclic.of_mulEquiv CFSG.Sporadic.Schreier.j3PermEquiv
    (OutTwoCyclic.of_card_le_two CFSG.Sporadic.SmallOddCore.j3_outer_card_le)

theorem outTwoCyclic_McL : OutTwoCyclic NativeSporadic.McL :=
  OutTwoCyclic.of_card_le_two CFSG.Sporadic.Schreier.McL_outer_card_le_two.1

theorem noDatum_M22 (F : Type) [Group F] (h : NativeSporadic.IsSporadic F .M22) : NoDatum F := by
  obtain ⟨e⟩ := h
  exact NoDatum.of_mulEquiv e (noDatum_of_noUniqueInvNormal noUniqueInvNormal_M22 outTwoCyclic_M22)

theorem noDatum_M23 (F : Type) [Group F] (h : NativeSporadic.IsSporadic F .M23) : NoDatum F := by
  obtain ⟨e⟩ := h
  exact NoDatum.of_mulEquiv e (noDatum_of_noUniqueInvNormal noUniqueInvNormal_M23 outTwoCyclic_M23)

theorem noDatum_J1 (F : Type) [Group F] (h : NativeSporadic.IsSporadic F .J1) : NoDatum F := by
  obtain ⟨e⟩ := h
  exact NoDatum.of_mulEquiv e (noDatum_of_noUniqueInvNormal noUniqueInvNormal_J1 outTwoCyclic_J1)

theorem noDatum_J2 (F : Type) [Group F] (h : NativeSporadic.IsSporadic F .J2) : NoDatum F := by
  obtain ⟨e⟩ := h
  exact NoDatum.of_mulEquiv e (noDatum_of_noUniqueInvNormal noUniqueInvNormal_J2 outTwoCyclic_J2)

theorem noDatum_J3 (F : Type) [Group F] (h : NativeSporadic.IsSporadic F .J3) : NoDatum F := by
  obtain ⟨e⟩ := h
  exact NoDatum.of_mulEquiv e (noDatum_of_noUniqueInvNormal noUniqueInvNormal_J3 outTwoCyclic_J3)

theorem noDatum_McL (F : Type) [Group F] (h : NativeSporadic.IsSporadic F .McL) : NoDatum F := by
  obtain ⟨e⟩ := h
  exact NoDatum.of_mulEquiv e (noDatum_of_noUniqueInvNormal noUniqueInvNormal_McL outTwoCyclic_McL)

end CFSG.ClassicalInvolution.Nobq
