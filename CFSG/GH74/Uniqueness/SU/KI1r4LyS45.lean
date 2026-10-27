module

public import CFSG.GH74.Uniqueness.SU.KI1r4LyFix
public import CFSG.GH74.Generic.S45.LEven
public import CFSG.GH74.Generic.S45.LG4Spor
public import CFSG.GH74.Generic.S45.LOddG
public import CFSG.GH74.Generic.S45.LSporJ1
public import CFSG.GH74.Generic.S45.LSporJ2
public import CFSG.GH74.Generic.S45.LSporM12
public import CFSG.GH74.Generic.S45.LSporOrd
public import CFSG.GH74.Generic.S45.LSporWit

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.GH74.Uniqueness.Bender

theorem sporRow_ly' :
    SporRow .Ly :=
  sporRow_of_perfect_order_four .Ly fun S _ e α hα hα1 => by
    have e' : S ≃* NativeSporadic.Ly := e
    obtain ⟨P, hPperf, hPfix, c, hcP, h4⟩ :=
      CFSG.GH74.Uniqueness.SU.K.R4.LyPerm.exists_perfect_fixed_of_equiv e' α hα hα1
    exact ⟨P, fun p hp => mem_autFixed_iff.2 (hPfix p hp), hPperf, c, hcP, h4⟩

theorem b_1310_spor_g4'
    : B_1310_spor_g4 := by
  intro K _ _ y L hypg hS
  obtain ⟨s, ⟨e⟩⟩ := hS
  have hyp : Hyp1310 K y L := hypg.2
  by_cases h1 : s = .J1
  · subst h1
    exact (spor_j1_false hyp (e.trans CFSG.Walter.walterJ1EquivNative.symm)).elim
  by_cases h2 : s = .M12
  · subst h2
    exact spor_m12 hyp e
  by_cases h3 : s = .J2
  · subst h3
    exact spor_j2 hyp e (j2_cover_row hyp e)
  by_cases h4 : s = .M11
  · subst h4
    exact (sporRow_m11 K y L hyp ⟨e⟩).elim
  by_cases h5 : s = .M22
  · subst h5
    exact (sporRow_m22 K y L hyp ⟨e⟩).elim
  by_cases h6 : s = .M23
  · subst h6
    exact (sporRow_m23 K y L hyp ⟨e⟩).elim
  by_cases h7 : s = .J3
  · subst h7
    exact (sporRow_j3 sporRowCls_j3_1920 K y L hyp ⟨e⟩).elim
  by_cases h8 : s = .McL
  · subst h8
    exact (sporRow_mcl K y L hyp ⟨e⟩).elim
  by_cases h9 : s = .Ly
  · subst h9
    exact (sporRow_ly' K y L hyp ⟨e⟩).elim
  have hout : s ∈ CFSG.GH74.Filter.sporadicOut := by
    cases s <;> simp_all [CFSG.GH74.Filter.sporadicOut]
  exact (sporRowG_of_out s hout K y L hypg ⟨e⟩).elim

theorem b_III11_13_10_g4_of_odd_rest_g4
    (hOdd4 : B_1310_odd_rest_g4) : B_III11_13_10_g4 :=
  b_III11_13_10_g4_of_leaves_odd b_1310_alt b_1310_spor_g4' b_1310_even (b_1310_odd_rest_g4 hOdd4)

end CFSG.GH74.Generic.S45
